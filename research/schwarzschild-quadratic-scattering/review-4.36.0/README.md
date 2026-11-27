# Lean 4.36.0 review of the Schwarzschild classification

**Aptifold Research · Version 1.0.0-review.1 · Preprint awaiting peer review**

Theorem 1 classifies local quadratic particular fields with rational radial coefficients in the maximal azimuthal Schwarzschild daughter channel. For every integer parent multipole ℓ ≥ 2 and common frequency ω > 0, the projected equation on a fixed nonzero parent admits such a field on exactly two incident parity lines. The supporting replay checks the metric source, both directions of the classification, rational uniqueness, and future-horizon regularity for the admitted fields. [Preprint and conventions](https://www.alphaxiv.org/abs/2611.rational-parity-mixtures-schwarzschild-scattering), [positive-frequency Lean statement](ported/ClassificationReview.lean).

## Replay from a full Git clone

Use Git, [Elan](https://lean-lang.org/install/), and Python 3.10 or newer. On systems that expose Python as `python3` or `py -3`, use that in place of `python`.

```sh
git clone https://github.com/agentsidequests/aptifold-lean-proofs.git
cd aptifold-lean-proofs/research/schwarzschild-quadratic-scattering/review-4.36.0
python -B materialize_review.py
python -B replay_lean.py --check-source
python -B replay_lean.py --prepare
python -B replay_lean.py
```

The first Python command assembles 508 Lean modules from five files in [ported](ported/) and 503 files in the [pinned original Git commit](https://github.com/agentsidequests/aptifold-lean-proofs/commit/f31879f7d05e1333eebacbc69e668d83b48c1244). It checks every source hash and validates existing generated sources on a rerun. [PORTING.patch](PORTING.patch) shows the compatibility edits and the new reviewer entry point. The two manifests pin the compiler, Mathlib, transitive dependencies, and expected axiom reports.

The clean Windows replay of these source bytes finished in 29 minutes 21 seconds with the pinned dependencies ready and two Lean checks running at a time (`--jobs 2`). It ended with `PASS: Lean checked 508 modules against the recorded axiom reports`. The expected axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`. For another replay, select an empty directory with `--output .lean-replay-second`.

## What to review

- Start with the [positive-frequency statement](ported/ClassificationReview.lean) and confirm its parent equation, projection, and parity coordinates against [Theorem 1 in the preprint](https://www.alphaxiv.org/abs/2611.rational-parity-mixtures-schwarzschild-scattering).
- Inspect the finite exclusion and its completeness in the [matrix certificate](../reproducibility/lean/MatrixCertificate.lean), [Laurent reduction](../reproducibility/lean/LaurentReduction.lean), and [fixed-parent classification](../reproducibility/lean/MetricMeromorphicClassification.lean).
- Follow the physical source and the horizon condition through the [regularization bridge](../reproducibility/lean/RegularizationBridge.lean) and [future-horizon proof](../reproducibility/lean/AdmittedFutureHorizon.lean).

Aptifold Research supplies the formalization and the replay. Paul Wishall is the human project lead. Cite this version for the Lean replay and the preprint for the physics result. [Citation metadata](CITATION.cff), [original research release](../).
