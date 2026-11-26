"""Enclose the outgoing-polarization zeros for the ell=4 half-frequency case."""

import argparse
from dataclasses import asdict
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys
from zipfile import ZipFile

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
DIRECT = HERE.parents[1] / "ell4-second-mixture-direct-20261123"
sys.path.insert(0, str(DIRECT))

import source
import green
from common import a, serialize
from direct import current, manufactured, strain_units
from verify_linear_reflections import closed_strain, gamma

ARCHIVE_SHA = "9adb1398862ee0516bc464c44e2c703f2b2475a6b1afd18c8a32bf6272f93388"
NAMES = ("even_even", "even_odd", "odd_odd")


def compiled_sources(upstream):
    archive_path = HERE / "REFEREE-SUPPLEMENT.zip"
    source.require(sha256(archive_path.read_bytes()).hexdigest() == ARCHIVE_SHA,
                   "The source archive does not match its recorded digest.")
    pins = {}
    with ZipFile(archive_path) as archive:
        for name in archive.namelist():
            if name.startswith("upstream/jl/") and name.endswith(".jl"):
                original = archive.read(name)
                source.require(
                    (upstream / name.removeprefix("upstream/")).read_bytes() == original,
                    f"Unpinned source input: {name}"
                )
                pins[name] = sha256(original).hexdigest()
    even_frame, odd_frame = source.Frame(source.ell), source.Frame(source.ell)
    odd_frame.ve = source.potential(source.ell)[4]
    components = (
        source.compare_even_even(upstream, even_frame, odd_frame),
        source.compare_even_odd(upstream),
        source.compare_odd_odd(upstream),
    )
    cases = [source.prepare_kernels(source.quadratic(case.regularized)) for case in components]
    control = manufactured()
    cases.append((control["horizon_density_pole_order_before_parent_substitution"], control["kernels"]))
    return [
        (pole, {name: tuple(map(source.Ratio.restore, rows)) for name, rows in kernels.items()})
        for pole, kernels in cases
    ], pins


def integrate(cases, settings):
    operator = green.waves.instrument("O")
    initial = (green.initial_wave(operator, label, rate, settings) for label, rate in green.MODES)
    waves, seed_proofs = zip(*initial, strict=True)
    left, right = 2 + settings.h, Fraction(settings.R)
    left_current = current([wave.enclose(left) for wave in waves], left)
    near = [green.horizon_tail(operator, kernels["horizon_density"], pole, settings, seed_proofs)
            for pole, kernels in cases]
    radial = [kernels["r"] for _, kernels in cases]
    finite, panel_report = green.finite_integrals(operator, settings, radial, waves)
    right_current = current([wave.enclose(right) for wave in waves], right)
    far_waves = [green.asymptotic_wave(operator, wave, settings) for wave in waves]
    far = [green.infinity_tail(kernels["inverse_square"], far_waves, settings)
           for _, kernels in cases]
    control_errors = (
        near[-1][0] - left_current,
        finite[-1] - (right_current - left_current),
        far[-1][0] + right_current,
    )
    parts = [(n[0], m, t[0]) for n, m, t in zip(near[:-1], finite[:-1], far[:-1], strict=True)]
    return far_waves, parts, control_errors, panel_report


def verify(upstream, level):
    settings = green.LEVELS[level]
    ctx.prec = settings.bits
    cases, pins = compiled_sources(upstream)
    far_waves, parts, control_errors, panel_report = integrate(cases, settings)
    (parent, *_), (daughter, *_) = far_waves
    ell, omega = source.PARENT, a(source.OMEGA)
    k, g, G = acb(0, omega), gamma(ell), gamma(2 * ell) / 2
    alpha = (g + k) / (g - k)
    rho = (G + g) / ((G - g) * alpha)
    normalizer = (alpha / parent[-1])**2 / (4 * k * daughter[-1])
    source.require(all(error.contains(0) and (error * normalizer).abs_upper() < arb("1e-9")
                       for error in control_errors),
                   "The manufactured Green integral does not recover its endpoint currents.")
    responses = [normalizer * sum(rows, acb(0)) for rows in parts]
    E, X, O = responses
    source.require(all(q.is_finite() and q.abs_lower() > 0 for q in responses),
                   "At least one response coefficient has unresolved sign or magnitude.")

    # Transform to the incident strain convention used by the closed formulas.
    parent_reflection = alpha * parent[1] / parent[-1]
    daughter_reflection = daughter[1] / daughter[-1]
    checks = {}
    for branch, ratio in enumerate((acb(1), rho), 1):
        direct = strain_units() * (E + X * ratio + O * ratio**2) / (1 + alpha * ratio)**2
        closed = closed_strain(ell, omega, branch, parent_reflection, daughter_reflection)
        error = direct - closed
        source.require(error.contains(0) and error.abs_upper() < arb("1e-9"),
                       f"The independently integrated source does not match closed branch {branch}.")
        checks[str(branch)] = {"direct": serialize(direct), "closed": serialize(closed)}

    discriminant = X**2 - 4 * E * O
    source.require(discriminant.abs_lower() > 0, "The roots are not yet resolved as simple.")
    square = discriminant.sqrt()
    roots = [(-X + sign * square) / (2 * O) for sign in (1, -1)]
    source.require(all(root.is_finite() and (E + X * root + O * root**2).contains(0)
                       for root in roots), "The quadratic-root check failed.")
    source.require(not roots[0].overlaps(roots[1]) and not roots[0].overlaps(-roots[1]),
                   "The zeros or their parity reversals are unresolved.")
    source.require(all((root - ratio).abs_lower() > 0 for root in roots for ratio in (1, rho)),
                   "A root is not separated from the rational local mixtures.")
    source.require(all(root.rad() < arb("1e-7") for root in roots),
                   "The root enclosures are too wide for the reported precision.")
    return {
        "state": "PASS",
        "level": level,
        "parent": ell,
        "daughter": 2 * ell,
        "parent_frequency": str(source.OMEGA),
        "projection": "regularized X^-",
        "source_archive_sha256": ARCHIVE_SHA,
        "source_member_sha256": pins,
        "settings": {name: str(value) for name, value in asdict(settings).items()},
        "coefficients": dict(zip(NAMES, map(serialize, responses), strict=True)),
        "discriminant": serialize(discriminant),
        "reference_odd_scale": serialize(alpha),
        "rational_ratios": list(map(serialize, (acb(1), rho))),
        "incident_odd_over_even": [serialize(-acb(0, 1) * alpha * root) for root in roots],
        "ratios_in_reference_parent_basis": list(map(serialize, roots)),
        "root_radii": [str(root.rad()) for root in roots],
        "integration_parts": {
            name: list(map(serialize, rows)) for name, rows in zip(NAMES, parts, strict=True)
        },
        "manufactured_current_errors": [str((error * normalizer).abs_upper()) for error in control_errors],
        "admitted_branch_cross_checks": checks,
        "finite_panel_report": panel_report,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pinned_upstream", type=Path)
    parser.add_argument("--level", choices=green.LEVELS, default="coarse")
    args = parser.parse_args()
    print(json.dumps(verify(args.pinned_upstream, args.level), indent=2))


if __name__ == "__main__":
    main()
