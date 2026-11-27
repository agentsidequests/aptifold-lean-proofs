"""Compare polarization-zero enclosures with the pinned v1 records."""

from argparse import ArgumentParser
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import sys

from flint import acb, arb, ctx


HERE = Path(__file__).resolve().parent
REFERENCE_SHA256 = {
    "coarse": "c9c5312a3c74aa1f9ad02a31c7223b187a76efc9aab6ffa9c68eabf16639b761",
    "fine": "c7966c49b284002a532fce1527def2dea181fe062a47f5be8cab3092e14052f9",
}
# Smallest powers of ten above the largest serialized root radius at each level.
MAX_RADIUS = {"coarse": "1e-10", "fine": "1e-16"}
CASE_FIELDS = (
    "parent", "daughter", "parent_frequency", "projection",
    "source_archive_sha256", "source_member_sha256",
)
ROOT_FIELDS = ("ratios_in_reference_parent_basis", "incident_odd_over_even")


def load_record(raw):
    record = json.loads(raw)
    if not isinstance(record, dict):
        raise ValueError("Expected one JSON record.")
    return record


def archived_record(level):
    path = HERE / f"polarization-zeros-{level}.json"
    raw = path.read_bytes()
    if sha256(raw).hexdigest() != REFERENCE_SHA256[level]:
        raise ValueError(f"The saved {level} reference differs from its v1 hash.")
    return load_record(raw)


def decoded_roots(record, level):
    if record.get("state") != "PASS" or record.get("level") != level:
        raise ValueError(f"Expected a successful {level} replay record.")
    radius_limit = arb(MAX_RADIUS[level])
    coordinate_lists = []
    for field in ROOT_FIELDS:
        entries = record.get(field)
        if not isinstance(entries, list) or len(entries) != 2:
            raise ValueError(f"Expected two enclosures in {field}.")
        roots = []
        for entry in entries:
            if not isinstance(entry, dict) or not all(
                isinstance(entry.get(axis), str) for axis in ("real", "imag")
            ):
                raise ValueError(f"Expected Arb interval strings in {field}.")
            root = acb(arb(entry["real"]), arb(entry["imag"]))
            if not root.is_finite() or not root.rad() < radius_limit:
                raise ValueError(f"{field} has a nonfinite enclosure or exceeds the {level} radius limit.")
            roots.append(root)
        coordinate_lists.append(roots)
    return tuple(zip(*coordinate_lists, strict=True))


def compare_records(candidate, candidate_level, reference, reference_level):
    for field in CASE_FIELDS:
        if field not in candidate or field not in reference or candidate[field] != reference[field]:
            raise ValueError(f"Replay case differs in {field}.")

    with ctx.workprec(256):
        fresh = decoded_roots(candidate, candidate_level)
        saved = decoded_roots(reference, reference_level)
        matches = [
            order for order in permutations(range(2))
            if all(
                all(a.overlaps(b) for a, b in zip(fresh[index], saved[other], strict=True))
                for index, other in enumerate(order)
            )
        ]
    if len(matches) != 1:
        raise ValueError("Expected a unique one-to-one overlap in both root coordinates.")
    return matches[0]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("record", nargs="?", type=Path,
                        help="Fresh replay JSON. Omit to compare the two saved records.")
    parser.add_argument("--level", choices=REFERENCE_SHA256, help="Level of the fresh replay")
    args = parser.parse_args()
    if (args.record is None) != (args.level is None):
        parser.error("Supply a replay JSON file and --level together.")

    try:
        if args.record is None:
            compare_records(archived_record("fine"), "fine", archived_record("coarse"), "coarse")
            print("PASS: the pinned coarse and fine roots overlap in both coordinates.")
        else:
            candidate = load_record(args.record.read_bytes())
            compare_records(candidate, args.level, archived_record(args.level), args.level)
            print(f"PASS: both {args.level} replay roots match the pinned enclosures.")
    except (OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
