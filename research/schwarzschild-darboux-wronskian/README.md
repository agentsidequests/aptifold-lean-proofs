# Wronskian and radial current of the normalized Schwarzschild Darboux map

**Aptifold Research · November 2026**

The odd-to-even Darboux map acts on a wave value and its tortoise derivative at each exterior radius. Its normalization changes the bilinear Wronskian of a pair at the same frequency. For a wave paired with its complex conjugate, the two normalizations cancel and the radial current is preserved.

- `same_frequency_wronskian` gives the factor `(g - k) / (g + k)` for two jets at `k = iω`, where `g` is the special rate.
- `opposite_frequency_wronskian` pairs a jet at `k` with a jet at `-k` and gives an unchanged Wronskian whenever both denominators are nonzero.
- `real_frequency_radial_current` applies the second identity to the conjugate jet for real frequency, real superpotential, and nonzero real rate. `radialCurrent_eq_im` checks that the current is `Im(conj(u) Du)`.

At `g = ω = 1`, the first factor is `-i`. The Lean file checks this case and the positive current of a unit outgoing plane wave. These checks help catch sign or normalization errors when comparing odd and even numerical solutions. The statements concern the transformation at a radius. They use the factorized radial equations to identify the transformed jet and leave the choice of scattering boundary data to the application.

## Reproduce

Open this directory with Git and [Elan](https://lean-lang.org/install/) available. The lockfile pins Lean 4.36.0’s Mathlib revision and dependencies.

```sh
lake exe cache get Mathlib.Basic.Complex.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum Mathlib.Tactic.Ring
lake build
lake env lean -DwarningAsError=true DarbouxWronskian.lean
```

The last command prints the axioms of the named results. Their dependencies are subsets of `propext`, `Classical.choice` and `Quot.sound`.

## Sources and credit

The classical Darboux transform and its scattering consequences are described by Glampedakis, Johnson and Kennefick. The sign and normalization follow Section 3, equation (4), of the Aptifold preprint, which gives the inverse parity map. Aptifold Research supplies this Lean formalization and its test cases. Paul Wishall is the human project lead. The Lean work was prepared with OpenAI Codex. [Classical source, Section III and Appendix A](https://arxiv.org/pdf/1702.06459v3), [Aptifold preprint](https://www.alphaxiv.org/abs/2611.rational-parity-mixtures-schwarzschild-scattering), [citation metadata](CITATION.cff).
