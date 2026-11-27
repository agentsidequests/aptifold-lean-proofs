"""Verify the recorded Schwarzschild proof sources with pinned Lean and Mathlib."""

from argparse import ArgumentParser
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "lean"
MANIFEST = ROOT / "proof-manifest.json"
LAKE_MANIFEST = ROOT / "lake-manifest.json"
MODULE_NAME = re.compile(r"[A-Za-z][A-Za-z0-9]*")
IMPORT = re.compile(r"^(?:(?:public|private|meta) )*import ([A-Za-z0-9_.]+)", re.M)
AXIOM_REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)[ \t]*$",
    re.M,
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXTERNAL_ROOTS = {"Init", "Lean", "Mathlib", "Std"}


def file_hash(path):
    return sha256(path.read_bytes()).hexdigest()


def axiom_report(output):
    result = {}
    for theorem, names in AXIOM_REPORT.findall(output):
        axioms = sorted(re.findall(r"[\w.]+", names))
        if set(axioms) - STANDARD_AXIOMS:
            raise ValueError(f"{theorem} uses an unexpected axiom: {axioms}")
        if theorem in result:
            raise ValueError(f"Duplicate axiom report for {theorem}")
        result[theorem] = axioms
    if re.search(r"declaration uses 'sorry'|sorryAx", output):
        raise ValueError("Lean reported a proof placeholder")
    return result


def qualified_sources(manifest):
    modules = manifest["modules"]
    if set(modules) != {path.stem for path in SOURCE.glob("*.lean")}:
        raise ValueError("The proof sources differ from the manifest's module list")
    dependencies = {}
    external = set()
    for name, data in modules.items():
        if MODULE_NAME.fullmatch(name) is None:
            raise ValueError(f"Unexpected Lean module name: {name}")
        path = SOURCE / (name + ".lean")
        if file_hash(path) != data["sha256"]:
            raise ValueError(f"Proof source differs from the manifest: {name}")
        requires = IMPORT.findall(path.read_text(encoding="utf-8"))
        dependencies[name] = [dep for dep in requires if dep in modules]
        for dep in set(requires) - modules.keys():
            if dep.split(".", 1)[0] not in EXTERNAL_ROOTS:
                raise ValueError(f"A required proof module is missing: {name} imports {dep}")
            external.add(dep)
    if sorted(external) != manifest["external_imports"]:
        raise ValueError("The external import set differs from the manifest")
    return dependencies


def build_order(dependencies, targets):
    order = []
    visiting = set()
    checked = set()

    def visit(name):
        if name in checked:
            return
        if name in visiting:
            raise ValueError(f"Cyclic Lean import: {name}")
        if name not in dependencies:
            raise ValueError(f"Unknown proof target: {name}")
        visiting.add(name)
        for dep in dependencies[name]:
            visit(dep)
        visiting.remove(name)
        checked.add(name)
        order.append(name)

    for target in targets:
        visit(target)
    return order


def command_output(command, cwd):
    result = subprocess.run(
        command, cwd=cwd, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise ValueError(f"{command[0]} failed in {cwd}:\n{result.stdout.strip()}")
    return result.stdout.strip()


def dependency_lock(manifest):
    lock = json.loads(LAKE_MANIFEST.read_text(encoding="utf-8"))
    mathlib = [p for p in lock["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != manifest["mathlib_revision"]:
        raise ValueError("Lake and the proof manifest disagree on the Mathlib revision")
    if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != manifest["lean_toolchain"]:
        raise ValueError("lean-toolchain disagrees with the proof manifest")
    return lock


def library_paths(packages, manifest, lock):
    def qualify_repository(root, revision):
        if command_output(["git", "rev-parse", "HEAD"], root) != revision:
            raise ValueError(f"Unexpected revision of {root.name}")
        if command_output(["git", "status", "--porcelain", "--untracked-files=no"], root):
            raise ValueError(f"Tracked files have changed in {root.name}")

    paths = []
    for package in lock["packages"]:
        root = packages / package["name"]
        if not (root / ".git").exists():
            raise ValueError(f"Dependency checkout missing: {root}. Run replay_lean.py --prepare.")
        qualify_repository(root, package["rev"])
        paths.append(root / ".lake/build/lib/lean")
    mathlib = packages / "mathlib"
    if (mathlib / "lean-toolchain").read_text(encoding="utf-8").strip() != manifest["lean_toolchain"]:
        raise ValueError("Mathlib requires a different Lean toolchain")
    dependency_revs = {p["name"]: p["rev"] for p in lock["packages"] if p["name"] != "mathlib"}
    mathlib_lock = json.loads((mathlib / "lake-manifest.json").read_text(encoding="utf-8"))
    if dependency_revs != {p["name"]: p["rev"] for p in mathlib_lock["packages"]}:
        raise ValueError("The transitive Lake lock differs from pinned Mathlib's own lock")
    for dep in mathlib_imports(manifest):
        module = Path(*dep.split(".")).with_suffix(".olean")
        if not (mathlib / ".lake/build/lib/lean" / module).is_file():
            raise ValueError(f"The Mathlib cache is missing {dep}. Run replay_lean.py --prepare.")
    return paths


def mathlib_imports(manifest):
    return [dep for dep in manifest["external_imports"] if dep.startswith("Mathlib.")]


def require_compiler(command, manifest):
    version = command_output(command + ["--version"], ROOT)
    if manifest["lean_commit"] not in version or f"version {manifest['lean_toolchain'].split(':v')[1]}," not in version:
        raise ValueError(f"Lean is not the pinned compiler: {version}")
    return version


def prepare_packages(manifest, lock):
    print(require_compiler(["lake", "env", "lean"], manifest), flush=True)
    subprocess.run(["lake", "exe", "cache", "get", *mathlib_imports(manifest)], cwd=ROOT, check=True)
    library_paths(ROOT / lock["packagesDir"], manifest, lock)


def check_module(name, build, heap_mib, env):
    args = ["-j", "1", "-M", str(heap_mib), "--tstack=65536", "-D", "Elab.async=false",
            "-o", str(build / (name + ".olean")), name + ".lean"]
    result = subprocess.run(["lean", *args], cwd=SOURCE, env=env, text=True,
                            encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (build / (name + ".log")).write_text(result.stdout, encoding="utf-8")
    if result.returncode != 0:
        print(result.stdout, flush=True)
        raise RuntimeError(f"Lean failed while checking {name}")
    return axiom_report(result.stdout)


def run_graph(graph, order, jobs, check):
    if jobs == 1:
        for name in order:
            check(name)
        return

    sorter = TopologicalSorter({name: graph[name] for name in order})
    sorter.prepare()
    ready = deque(sorter.get_ready())
    running = {}
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while ready or running:
            while ready and len(running) < jobs:
                name = ready.popleft()
                running[executor.submit(check, name)] = name
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for result in done:
                result.result()
                sorter.done(running.pop(result))
            ready.extend(sorter.get_ready())


def replay(manifest, graph, order, packages, lock, build, heap_mib, jobs):
    libraries = library_paths(packages, manifest, lock)
    print(require_compiler(["lean"], manifest), flush=True)
    if build.exists() and (not build.is_dir() or any(build.iterdir())):
        raise ValueError(f"Use an empty output directory: {build}")
    build.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, [build, *libraries]))}
    indices = {name: i for i, name in enumerate(order, 1)}

    def check(name):
        print(f"[{indices[name]}/{len(order)}] {name}", flush=True)
        actual = check_module(name, build, heap_mib, env)
        if actual != manifest["modules"][name]["axioms"]:
            raise ValueError(f"The axiom report differs from the recorded result for {name}")

    run_graph(graph, order, jobs, check)


def main():
    sys.stdout.reconfigure(errors="backslashreplace")
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--packages", type=Path,
                        help="Reuse an existing .lake/packages directory with the same revisions")
    parser.add_argument("--output", type=Path, default=ROOT / ".lean-replay",
                        help="Empty directory for the build output")
    parser.add_argument("--target", action="append", metavar="MODULE",
                        help="Replay just this target and its dependencies. May be repeated.")
    parser.add_argument("--heap-mib", type=int, default=2500, help="Lean heap limit per module")
    parser.add_argument("--jobs", type=int, default=1, help="Maximum concurrent Lean checks (default: 1)")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check-source", action="store_true",
                        help="Check recorded hashes and import closure without compiling")
    action.add_argument("--prepare", action="store_true",
                        help="Fetch the pinned Lake packages and the required Mathlib cache")
    args = parser.parse_args()
    if args.heap_mib < 1 or args.jobs < 1:
        parser.error("--heap-mib and --jobs must be positive")
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    lock = dependency_lock(manifest)
    graph = qualified_sources(manifest)
    order = build_order(graph, args.target or manifest["roots"])
    if args.check_source:
        print(f"PASS: verified {len(graph)} source hashes and resolved {len(order)} replay modules")
        return
    if args.prepare:
        if args.packages is not None:
            parser.error("--prepare initializes this bundle's .lake/packages directory")
        prepare_packages(manifest, lock)
        print("PASS: pinned Lake packages and required Mathlib cache are ready")
        return
    packages = args.packages.resolve() if args.packages else ROOT / lock["packagesDir"]
    replay(manifest, graph, order, packages, lock, args.output.resolve(), args.heap_mib, args.jobs)
    print(f"PASS: Lean checked {len(order)} modules against the recorded axiom reports")


if __name__ == "__main__":
    main()
