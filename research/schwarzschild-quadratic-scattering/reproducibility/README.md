# Reproducibility

The Lean files prove the two-mixture classification for rational local particular fields in the projected quadratic Schwarzschild equation. They also verify source and reconstruction steps in the chosen gauge, the retarded boundary-value problem, and several consequences of the two closed strain formulas.

## Referee quickstart

Download and extract the [referee supplement](referee-supplement.zip). Use Python 3.13 with Python-FLINT 0.9.0 (`python -m pip install python-flint==0.9.0`). Run the commands below from the extracted folder. Once Python-FLINT is installed, the supplement runs offline.

**Check the exact exclusion certificate.**

```sh
python -B review.py --check certificate
```

`PASS: certificate` confirms the witness annihilates all 30 columns of the 41-equation system and that the obstruction is nonzero on the stated parameter domain. The [full Lean replay](#replay-the-lean-proof) also checks the reduction from rational local fields to this system.

**Check the printed strain bounds against the archived intervals.** Save the [paper's TeX source](../paper/schwarzschild.tex) and supply its path.

```sh
python -B review.py --check table --manuscript "/path/to/schwarzschild.tex"
```

`PASS: table` confirms that the saved complex strain intervals support the bounds in Table 1.

**Rerun the radial strain benchmark.**

```sh
python -B review.py --check radial
```

This longer check regenerates the source and integrates the ℓ = 4, Mω = 1/2 case on two fresh grids. A pass requires the fresh strain to overlap the archived and closed-form enclosures, with absolute normalized complex error below `1.32e-14` on the coarse grid and `1.09e-20` on the fine grid.

The supplement's `REFEREE-START.md` describes the exact source reconstruction, contour integral and independent linear reflection checks. See [the full supplement replay](#rebuild-the-source-and-check-the-numerical-results) to run those together.

## Find the result you want to check

| Result | Lean source |
| --- | --- |
| Vacuum background and linear parent equations | [VacuumSeries.lean](lean/VacuumSeries.lean) |
| Sourced parity equations and reconstruction in the exterior angular chart | [ParityMasterProjection.lean](lean/ParityMasterProjection.lean), [ParityReconstructionTheorem.lean](lean/ParityReconstructionTheorem.lean), [QuadraticScatteringReconstruction.lean](lean/QuadraticScatteringReconstruction.lean) |
| Two and only two lines of incident parity mixtures on a fixed nonzero parent | [MetricMeromorphicClassification.lean](lean/MetricMeromorphicClassification.lean), [MixtureClassification.lean](lean/MixtureClassification.lean) |
| Finite exclusion witness and the bounds that make the test exhaustive | [MatrixCertificate.lean](lean/MatrixCertificate.lean), [LaurentReduction.lean](lean/LaurentReduction.lean), [RationalRowExclusion.lean](lean/RationalRowExclusion.lean) |
| Metric-derived to regularized forcing | [RegularizationBridge.lean](lean/RegularizationBridge.lean) |
| Uniqueness of the rational particular rows and analytic horizon extension for the two mixtures | [RationalLocalUniqueness.lean](lean/RationalLocalUniqueness.lean), [AdmittedFutureHorizon.lean](lean/AdmittedFutureHorizon.lean) |
| Retarded field existence, uniqueness, and outgoing strain | [RetardedScattering.lean](lean/RetardedScattering.lean), [LinearRetardedUniqueness.lean](lean/LinearRetardedUniqueness.lean), [CompleteOutgoingStrain.lean](lean/CompleteOutgoingStrain.lean) |
| Green representation and bounds for comparisons with numerical solutions | [RetardedGreenReplay.lean](lean/RetardedGreenReplay.lean), [RetardedStrainError.lean](lean/RetardedStrainError.lean), [ScatteringTailEstimate.lean](lean/ScatteringTailEstimate.lean) |
| Rationality and retarded response across the top daughter multiplet | [AngularMixtureClassification.lean](lean/AngularMixtureClassification.lean), [AngularRetardedScattering.lean](lean/AngularRetardedScattering.lean) |
| Small-frequency absorption upper bound, strain floor, and transfer of the linear phase expansion to the nonlinear strain | [SharpSoftIncidence.lean](lean/SharpSoftIncidence.lean), [PhysicalSoftResponse.lean](lean/PhysicalSoftResponse.lean), [SoftCubicTransfer.lean](lean/SoftCubicTransfer.lean), [SoftThresholdFactor.lean](lean/SoftThresholdFactor.lean) |
| Light-ring phase and envelope consequences | [LightRingPhaseLimits.lean](lean/LightRingPhaseLimits.lean) |
| Angular factorization of polarization zeros and conditional exclusion of simultaneous zeros of both spin components | [AngularPolarizationZeros.lean](lean/AngularPolarizationZeros.lean) |

The matrix certificate operates on the derived, pole-subtracted source. The Laurent bounds and the fixed-parent argument justify applying it to the full rational local class. The classification allows any positive real shared frequency and any integer parent multipole at least two. The outgoing phase and strain use the conventions in the paper. The top daughter has twice the parent multipole and twice the shared frequency.

The light-ring Lean proof starts from the assumed logarithmic relative-phase law and transfers it to the limiting interference envelopes. The derivation of the law by matching the linear waves is analytic. The angular proof uses the top-multipole coupling normalization given in the paper. Interval calculations provide the numerical examples, including nonzero coefficients needed in the polarization result at the specified frequency.

## Replay the Lean proof

This is the **full v1 replay on Lean 4.33.1**. The [focused Theorem 1 replay](../review-4.36.0/) uses Lean 4.36.0.

Use Python 3.10 or newer, Git, the Lean toolchain `leanprover/lean4:v4.33.1`, and Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474`. The script checks the compiler commit, the Mathlib and transitive dependency revisions, and the proof source hashes. Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` occur in the recorded audits.

Run an integrity check from this directory.

```sh
python -B replay_lean.py --check-source
```

With the pinned Mathlib checkout and cache in place, run the serial verifier.

```sh
python -B replay_lean.py --mathlib /path/to/pinned/mathlib4 --output .lean-replay/full
```

If you need the checkout, use the official [Mathlib repository](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). Check out the commit above and run `lake exe cache get` there with its checked-in dependency manifest. The verification command itself reads the existing Mathlib cache and writes build outputs only to its chosen output directory.

The full command checks **570 proof modules** and compares **592 named axiom reports**. It compiles one module at a time and leaves local logs with the build. The generated artifacts require roughly 0.6 GB before compiler metadata and logs, in addition to a prepared Mathlib cache. Use an empty `--output` path for each independent run. You can start with a single proof and its imports.

```sh
python -B replay_lean.py --mathlib /path/to/pinned/mathlib4 --target LightRingPhaseLimits --output .lean-replay/light-ring
```

The retained proof inputs are in [lean/](lean/) and their SHA-256 hashes and expected axiom reports in [proof-manifest.json](proof-manifest.json). Numerical comparisons and the archived source-to-certificate checks have separate entry points below.

## Rebuild the matrix witness

The matrix generator uses only Python's standard library. This command rebuilds its Lean input from the referee supplement and checks it against the stored module.

```sh
python -B lean/verify_matrix_lean.py referee-supplement.zip --check-data lean/MatrixCertificateData.lean
```

The command `python -B lean/verify_matrix_lean.py referee-supplement.zip` checks the regenerated matrix certificate and associated no-solution theorem under standalone Lean 4.34.1. The main replay uses the source inputs in this folder with Lean 4.33.1 and includes the rational-class reduction.

## Rebuild the source and check the numerical results

After the [quickstart](#referee-quickstart), run `python -B review.py` from the extracted supplement directory to check the exact matrix certificate, compare the three generated source sectors and strain weights, and rerun the radial, independent contour and reflection checks. The script lists individual checks under `--help`.

The archive keeps the released upstream source bytes and the upstream MIT license. Its SHA-256 is `9adb1398862ee0516bc464c44e2c703f2b2475a6b1afd18c8a32bf6272f93388`. Source conventions follow [Bucciotti et al., *Second-order scattering response of a Schwarzschild black hole*](https://arxiv.org/abs/2609.20934v2). The source in the archive is pinned to [the authors' implementation at revision 5831ae7](https://github.com/jredondoyuste/BlackHoleNonlinearities.jl/tree/5831ae75e20b31489ef2034c8bbb13a53c5d4a3d).

The [benchmarks](benchmarks/) folder supplies the recorded complex strain, cancellation-band and polarization-zero enclosures, low-frequency doubling ratios, and the light-ring propagation comparison. The light-ring comparisons check the analytic phase asymptotics numerically. The enclosure files give finite-frequency results at their stated labels and intervals.

To reproduce the fourth-multipole polarization zeros at \(M\omega = 1/2\), run the following commands with the same Python-FLINT runtime. Each command prints a JSON record with the two enclosed roots, source coefficients, error controls, and complex strain cross-checks. Compare these with the saved [coarse](benchmarks/polarization-zeros-coarse.json) and [fine](benchmarks/polarization-zeros-fine.json) records.

```sh
python -B benchmarks/replay_polarization.py --level coarse
python -B benchmarks/replay_polarization.py --level fine
```
