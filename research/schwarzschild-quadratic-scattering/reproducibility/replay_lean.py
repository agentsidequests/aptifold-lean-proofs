"""Verify the recorded Schwarzschild proof sources with pinned Lean and Mathlib."""

from argparse import ArgumentParser
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "lean"
MANIFEST = ROOT / "proof-manifest.json"
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
    return subprocess.check_output(
        command, cwd=cwd, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", errors="replace",
    ).strip()


def library_paths(mathlib, manifest):
    def qualify_repository(root, revision):
        if command_output(["git", "rev-parse", "HEAD"], root) != revision:
            raise ValueError(f"Unexpected revision of {root.name}")
        if command_output(["git", "status", "--porcelain", "--untracked-files=no"], root):
            raise ValueError(f"Tracked files have changed in {root.name}")

    qualify_repository(mathlib, manifest["mathlib_revision"])
    if (mathlib / "lean-toolchain").read_text().strip() != manifest["lean_toolchain"]:
        raise ValueError("Mathlib requires a different Lean toolchain")
    dependencies = json.loads((mathlib / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = mathlib / dependencies["packagesDir"]
    paths = [mathlib / ".lake/build/lib/lean"]
    for package in dependencies["packages"]:
        root = packages / package["name"]
        qualify_repository(root, package["rev"])
        paths.append(root / ".lake/build/lib/lean")
    for dep in manifest["external_imports"]:
        if dep.startswith("Mathlib."):
            module = Path(*dep.split(".")).with_suffix(".olean")
            if not any((path / module).is_file() for path in paths):
                raise ValueError(f"The Mathlib cache is missing {dep}. Run lake exe cache get.")
    return paths


def replay(manifest, order, mathlib, build, heap_mib):
    libraries = library_paths(mathlib, manifest)
    command = ["lean", f"+{manifest['lean_toolchain']}"]
    version = command_output(command + ["--version"], SOURCE)
    if manifest["lean_commit"] not in version:
        raise ValueError(f"Lean is not the pinned compiler: {version}")
    if build.exists() and (not build.is_dir() or any(build.iterdir())):
        raise ValueError(f"Use an empty output directory: {build}")
    build.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, [build, *libraries]))}
    for index, name in enumerate(order, 1):
        args = ["-j", "1", "-M", str(heap_mib), "--tstack=65536", "-D", "Elab.async=false",
                "-o", str(build / (name + ".olean")), name + ".lean"]
        print(f"[{index}/{len(order)}] {name}", flush=True)
        result = subprocess.run(command + args, cwd=SOURCE, env=env, text=True,
                                encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (build / (name + ".log")).write_text(result.stdout, encoding="utf-8")
        if result.returncode != 0:
            print(result.stdout)
            raise RuntimeError(f"Lean failed while checking {name}")
        if axiom_report(result.stdout) != manifest["modules"][name]["axioms"]:
            raise ValueError(f"The axiom report differs from the recorded result for {name}")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, help="Path to the pinned Mathlib checkout and cache")
    parser.add_argument("--output", type=Path, default=ROOT / ".lean-replay",
                        help="Empty directory for the build output")
    parser.add_argument("--target", action="append", metavar="MODULE",
                        help="Replay just this target and its dependencies. May be repeated.")
    parser.add_argument("--heap-mib", type=int, default=2500, help="Lean heap limit per module")
    parser.add_argument("--check-source", action="store_true",
                        help="Check recorded hashes and import closure without compiling")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    graph = qualified_sources(manifest)
    order = build_order(graph, args.target or manifest["roots"])
    if args.check_source:
        print(f"PASS: verified {len(graph)} source hashes and resolved {len(order)} replay modules")
        return
    if args.mathlib is None:
        parser.error("--mathlib is required for a Lean replay. Use --check-source for hashes only.")
    replay(manifest, order, args.mathlib.resolve(), args.output.resolve(), args.heap_mib)
    print(f"PASS: Lean checked {len(order)} modules against the recorded axiom reports")


if __name__ == "__main__":
    main()
