# Exactly two rational parity mixtures in quadratic Schwarzschild scattering

**Aptifold Research · 26 November 2026 · preprint for technical review**

[Read the paper (PDF)](paper.pdf) · [View the TeX source](paper/schwarzschild.tex) · [Replay the Lean proofs](reproducibility/) · [Browse the benchmark records](reproducibility/benchmarks/)

Two incoming gravitational waves at the same frequency generate a daughter wave at twice that frequency. In the highest-angular-momentum channel on Schwarzschild, exactly two incident parity mixtures allow a rational local quadratic particular field. This holds for every integer parent multipole ℓ ≥ 2 and every positive common frequency. Each admitted field gives a unique retarded completion and an exact outgoing complex strain in terms of linear reflection amplitudes.

Aptifold formulated the classification question, derived the result, developed the follow-on analysis, and wrote the Lean formalization. Paul Wishall led the research project and coordinates publication.

## Start with the claim you want to inspect

| Question | Where to start |
| --- | --- |
| Why can there be no third rational mixture? | [Matrix certificate](reproducibility/lean/MatrixCertificate.lean) and [Laurent reduction](reproducibility/lean/LaurentReduction.lean) |
| Does the certificate apply to the metric-derived source and one physical parent? | [Metric and fixed-parent classification](reproducibility/lean/MetricMeromorphicClassification.lean) |
| Why is there only one retarded solution? | [Conserved-flux proof](reproducibility/lean/LinearRetardedUniqueness.lean) and [construction and strain](reproducibility/lean/RetardedScattering.lean) |
| What if the incoming azimuthal modes have different parities? | [Complete top-daughter retarded response](reproducibility/lean/AngularRetardedScattering.lean) |
| Which checks start from the recorded data and which rebuild it? | [Reproduction guide](reproducibility/README.md) |

The paper gives the low-frequency sign change for the second mixture, the finite fourth-multipole cancellation benchmark, two certified spin-minus zeros outside the rational class, and the light-ring limit with a winding relative phase. The quadratic strain formulas are Lean-checked. The high-angular-momentum matching is analytic. Lean checks its transfer to the interference envelopes. The radial and finite-frequency calculations use outward-rounded arithmetic.

## Figures and citations

The paper's [vector figures](paper/figures/) and the [data-driven figure source](paper/draw_figures.py) are included. Start with the [original visual explainer](https://aptifold.ai/gw-physics) for the physical setup. The full bibliography is in the paper.

The source, radiation convention, and prior quadrupolar polarization zeros are from [Bucciotti et al.](https://arxiv.org/abs/2609.20934v2). The pinned upstream numerical source inside the replay supplement retains its MIT notice. The material in this folder is the paper and its scientific evidence.

Suggested citation · Aptifold Research, *Exactly two rational parity mixtures in quadratic Schwarzschild scattering*, preprint, 26 November 2026.

This work is available for technical scrutiny. A concrete starting point is the first equation, coefficient, or normalization where an independent calculation differs.
