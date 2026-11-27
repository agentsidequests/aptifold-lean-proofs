"""Recover the checked Lean 4.36 review sources from the pinned public Git object."""

from argparse import ArgumentParser
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZipFile

import replay_lean


ROOT = Path(__file__).resolve().parent
PUBLIC = "research/schwarzschild-quadratic-scattering/reproducibility"


def materialize(repo):
    manifest = json.loads(replay_lean.MANIFEST.read_text(encoding="utf-8"))
    destination = replay_lean.SOURCE
    if destination.exists() or destination.is_symlink():
        replay_lean.qualified_sources(manifest)
        print("PASS: exact review sources are already present")
        return

    commit = manifest["source_commit"]
    root = subprocess.check_output(
        ["git", "-C", str(repo.resolve()), "rev-parse", "--show-toplevel"],
        text=True, encoding="utf-8",
    ).strip()
    git = ["git", "-C", root]
    original = json.loads(subprocess.check_output(
        git + ["show", f"{commit}:{PUBLIC}/proof-manifest.json"]
    ))["modules"]
    if set(manifest["modules"]) - set(original) != {"ClassificationReview"}:
        raise ValueError("The review manifest names an unexpected added module")
    ported = ROOT / "ported"
    changed = {
        name + ".lean" for name, record in manifest["modules"].items()
        if original.get(name, {}).get("sha256") != record["sha256"]
    }
    if {path.name for path in ported.iterdir()} != changed:
        raise ValueError("The ported source set differs from the recorded changes")
    archived = subprocess.check_output(git + ["archive", "--format=zip", commit, PUBLIC + "/lean"])

    with TemporaryDirectory(prefix=".review-source-", dir=ROOT) as temporary:
        work = Path(temporary)
        sources = work / "lean"
        sources.mkdir()
        with ZipFile(BytesIO(archived)) as archive:
            for name, record in manifest["modules"].items():
                if not replay_lean.MODULE_NAME.fullmatch(name):
                    raise ValueError(f"Invalid Lean module name: {name!r}")
                filename = name + ".lean"
                if filename in changed:
                    data = (ported / filename).read_bytes()
                else:
                    data = archive.read(f"{PUBLIC}/lean/{filename}")
                if sha256(data).hexdigest() != record["sha256"]:
                    raise ValueError(f"The replay source hash differs for {name}")
                (sources / filename).write_bytes(data)
        sources.rename(destination)
    replay_lean.qualified_sources(manifest)
    print(f"PASS: {len(manifest['modules'])} review source files match their recorded hashes")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=ROOT,
                        help="Public Git checkout with the pinned source commit")
    args = parser.parse_args()
    materialize(args.repository)


if __name__ == "__main__":
    main()
