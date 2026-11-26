"""Rebuild the fourth-multipole polarization zeros using the sealed radial solver."""

from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
import runpy
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile


HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent / "referee-supplement.zip"
ARCHIVE_HASH = "9adb1398862ee0516bc464c44e2c703f2b2475a6b1afd18c8a32bf6272f93388"
SCATTERING = Path("verification/investigations/gw-likelihood-opportunities-20261101/scattering")
POLARIZATION = "verify_polarization_zeros.py"


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--level", choices=("coarse", "fine"), default="coarse")
    parser.add_argument("--scratch", type=Path, help="Directory for temporary extracted inputs")
    args = parser.parse_args()
    raw = ARCHIVE.read_bytes()
    if sha256(raw).hexdigest() != ARCHIVE_HASH:
        raise ValueError("The referee supplement does not match the recorded revision")
    with TemporaryDirectory(prefix="schwarzschild-", dir=args.scratch) as temp:
        root = Path(temp).resolve()
        with ZipFile(ARCHIVE) as archive:
            for member in archive.namelist():
                if not (root / member).resolve().is_relative_to(root):
                    raise ValueError(f"Archive member leaves the replay directory: {member}")
            archive.extractall(root)
        work = root / SCATTERING / "second-polarization-angular-20261117" / "polarization"
        work.mkdir(parents=True)
        (work / "REFEREE-SUPPLEMENT.zip").write_bytes(raw)
        driver = work / POLARIZATION
        driver.write_bytes((HERE / POLARIZATION).read_bytes())
        sys.path.insert(0, str(root))
        sys.argv = [str(driver), str(root / "upstream"), "--level", args.level]
        runpy.run_path(str(driver), run_name="__main__")


if __name__ == "__main__":
    main()
