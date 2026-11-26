"""Rebuild and kernel-check the exact Schwarzschild matrix certificate."""
import argparse
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from math import lcm
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZipFile


OBSTRUCTION = "706383d67b06c2bbe255e0ea3ada5f54cb2d4194c67a3b57c1edaff470050e00"
ODD_POLES = "5cec48c32f86f248bdb0e8d5facd80de8cc16fe2f4c95c85274587be2cfdd2f3"
# Q = (2 ell + 1)(2 ell - 1)(ell + 1).
Q = dict(enumerate(map(Fraction, (-1, -1, 4, 4))))
# k - Gamma, where Gamma = gamma(2 ell) / 2.
BASE_DENOMINATOR = {
    (1, 0): Fraction(1),
    (0, 1): Fraction(1, 6), (0, 2): Fraction(1, 6),
    (0, 3): Fraction(-2, 3), (0, 4): Fraction(-2, 3),
}


def read_member(archive, name, expected):
    member = f"certificate/data/{name}.json"
    payload = archive.read(member)
    if sha256(payload).hexdigest() != expected:
        raise ValueError(f"{member} differs from the pinned referee input")
    return json.loads(payload)


def terms(records):
    """Return powers of radius, frequency and angular label with exact coefficients."""
    result = {}
    for powers, value in records:
        if len(powers) != 10 or any(powers[i] for i in (1, 3, 4, 5, 6, 7, 8)):
            raise ValueError("Unexpected variable in a Laurent coefficient")
        key = (powers[0], powers[2], powers[9])
        if key in result or not Fraction(value):
            raise ValueError("Duplicate or zero monomial")
        result[key] = Fraction(value)
    return result


def bivariate(records):
    result = {}
    for (r, k, ell), value in terms(records).items():
        if r != 0:
            raise ValueError("Unexpected radius in matrix witness")
        result[k, ell] = value
    return result


def times_angular(poly, angular):
    result = defaultdict(Fraction)
    for (k, ell), coefficient in poly.items():
        for power, factor in angular.items():
            result[k, ell + power] += coefficient * factor
    return {monomial: coefficient for monomial, coefficient in result.items() if coefficient}


def divide_exact(dividend, divisor):
    rest = dividend.copy()
    quotient = {}
    degree = max(divisor)
    while rest and (shift := max(rest) - degree) >= 0:
        factor = rest[degree + shift] / divisor[degree]
        quotient[shift] = factor
        for power, coefficient in divisor.items():
            key = power + shift
            rest[key] = rest.get(key, Fraction()) - factor * coefficient
            if not rest[key]:
                del rest[key]
    if rest:
        raise ValueError("The source denominator does not divide the common denominator")
    return quotient


def cleared_rows(entries):
    """Clear the common denominator D = 6 Q (k - Gamma) in all source rows."""
    rows = {}
    for component, entry in enumerate(entries):
        denominator = terms(entry["denominator"])
        radius_powers = {r for r, _, _ in denominator}
        if len(radius_powers) != 1:
            raise ValueError("Expected one radius power in the source denominator")
        (radius_power,) = radius_powers
        base = {(k, l): c for (_, k, l), c in denominator.items()}
        angular = {l: c for (k, l), c in base.items() if k == 1}
        if base != times_angular(BASE_DENOMINATOR, angular):
            raise ValueError("Source denominator is not (k - Gamma) times an angular factor")
        multiplier = {l: 6 * c for l, c in divide_exact(Q, angular).items()}
        numerators = defaultdict(dict)
        for (r, k, ell), value in terms(entry["numerator"]).items():
            numerators[r - radius_power][k, ell] = value
        for power, numerator in numerators.items():
            rows[component, power] = times_angular(numerator, multiplier)
    return rows


def integer_scale(polys):
    return lcm(*(value.denominator for poly in polys for value in poly.values()))


def dense(poly, scale):
    if not poly:
        return []
    result = [[] for _ in range(1 + max(k for k, _ in poly))]
    by_frequency = defaultdict(dict)
    for (k, ell), value in poly.items():
        by_frequency[k][ell] = int(scale * value)
    for k, coefficients in by_frequency.items():
        result[k] = [coefficients.get(ell, 0) for ell in range(1 + max(coefficients))]
    return result


def render(archive):
    obstruction = read_member(archive, "obstruction", OBSTRUCTION)
    odd = read_member(archive, "odd-poles", ODD_POLES)
    labels = list(map(tuple, obstruction["equation_labels"]))
    if obstruction["columns"] != 30 or obstruction["rows"] != 41 or len(set(labels)) != 41:
        raise ValueError("Unexpected certificate dimensions or duplicate row")
    weights = [{} for _ in labels]
    for index, entry in obstruction["witness"].items():
        if bivariate(entry["denominator"]) != {(0, 0): Fraction(1)}:
            raise ValueError("Expected polynomial witness")
        weights[int(index)] = bivariate(entry["numerator"])
    source = cleared_rows(odd["remaining_source"])
    if not set(source) <= set(labels):
        raise ValueError("Source contains an unrepresented equation")
    target = obstruction["pure_odd_obstruction"]
    if bivariate(target["denominator"]) != BASE_DENOMINATOR:
        raise ValueError("Unexpected angular obstruction denominator")
    angular = bivariate(target["numerator"])
    if {k for k, _ in angular} != {6} or max(ell for _, ell in angular) != 65:
        raise ValueError("Expected k^6 A(ell) with angular degree 65")

    witness_scale = integer_scale(weights)
    source_scale = integer_scale(source.values())
    angular_scale = integer_scale([angular])
    lines = [
        "/- Generated by verify_matrix_lean.py from the referee supplement.",
        f"obstruction.json SHA-256 {OBSTRUCTION}",
        f"odd-poles.json SHA-256 {ODD_POLES} -/",
        "import Init",
        "",
        "namespace SchwarzschildMatrix",
        "",
        "abbrev Polynomial := List (List Int)",
        "abbrev Monomial := Nat × Nat × Int",
        "",
        f"def witnessScale : Int := {witness_scale}",
        f"def sourceScale : Int := {source_scale}",
        f"def angularScale : Int := {angular_scale}",
        "",
        "def rowLabels : List (Nat × Int) := [",
    ]
    lines += ["  " + ",\n  ".join(", ".join(map(str, labels[i:i+6])) for i in range(0, len(labels), 6)) + "]"]
    coefficients = dense(angular, angular_scale)[6]
    lines += ["", "def angularCoefficients : List Int := [",
              "  " + ",\n  ".join(", ".join(map(str, coefficients[i:i+4]))
                                    for i in range(0, 66, 4)) + "]"]
    for i, poly in enumerate(weights):
        value = dense(poly, witness_scale)
        if value:
            lines += ["", f"private def weight{i} : Polynomial := [",
                      "  " + ",\n  ".join(map(str, value)) + "]"]
    lines += ["", "def witness : List Polynomial := [",
              "  " + ",\n  ".join(
                  ", ".join(f"weight{i}" if weights[i] else "[]" for i in range(offset, min(offset + 6, 41)))
                  for offset in range(0, 41, 6)
              ) + "]",
              "", "def clearedSource : List (List Monomial) := ["]
    lines += ["  " + ",\n  ".join(str([
        (k, ell, int(c * source_scale))
        for (k, ell), c in sorted(source.get(label, {}).items())
    ]) for label in labels) + "]", "", "end SchwarzschildMatrix", ""]
    return "\n".join(lines).encode("utf-8")


def verify(data):
    source = Path(__file__).resolve().parent
    command = [
        "lean", "+leanprover/lean4:v4.34.1", "-j", "1", "-M", "1200", "--tstack=65536",
    ]
    with TemporaryDirectory(prefix="aptifold-schwarzschild-lean-") as directory:
        work = Path(directory)
        (work / "MatrixCertificateData.lean").write_bytes(data)
        for name in ("AngularObstructionPilot.lean", "MatrixCertificate.lean"):
            shutil.copyfile(source / name, work / name)
        env = {**os.environ, "LEAN_PATH": str(work)}
        for module in ("MatrixCertificateData", "AngularObstructionPilot"):
            print(f"Compiling {module}", flush=True)
            subprocess.run(command + ["-o", f"{module}.olean", f"{module}.lean"],
                           cwd=work, env=env, check=True)
        print("Checking the exact matrix certificate", flush=True)
        check = subprocess.run(command + ["MatrixCertificate.lean"], cwd=work, env=env,
                               encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, check=False)
        print(check.stdout, end="")
        check.check_returncode()
        axioms = dict(re.findall(
            r"^'SchwarzschildMatrix\.([a-z_]+)' depends on axioms: \[([^\]]*)\]$",
            check.stdout, re.MULTILINE,
        ))
        required = {
            "annihilates_column", "source_projection_identity",
            "projected_source_nonzero", "no_solution",
        }
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        if set(axioms) != required or any(
            set(names.split(", ")) - allowed for names in axioms.values()
        ):
            raise ValueError("The theorem audit is incomplete or uses an unexpected axiom")
    print("PASS: the kernel accepted the matrix certificate and the no-solution theorem.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("supplement", nargs="?", type=Path,
                        default=Path(__file__).with_name("REFEREE-SUPPLEMENT.zip"))
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--write-data", type=Path)
    modes.add_argument("--check-data", type=Path)
    args = parser.parse_args()
    with ZipFile(args.supplement) as archive:
        data = render(archive)
    if args.write_data:
        args.write_data.write_bytes(data)
    elif args.check_data:
        if args.check_data.read_bytes().replace(b"\r\n", b"\n") != data:
            raise ValueError("Generated Lean inputs differ from the requested file")
    else:
        verify(data)


if __name__ == "__main__":
    main()
