# Analytic work on the prime interval

The proposed proof for an unbounded range uses exact prime witnesses below \(X=4\times10^{14}\) and a uniform estimate for Chebyshev’s \(\psi\) above \(X\). The weighted sum \(\psi(x)\) counts powers of primes up to \(x\). A sufficiently sharp estimate ensures the interval is wide enough to contain an ordinary prime.

- [`SexticTailBudget.lean`](SexticTailBudget.lean) checks the scalar 29 ppm error budget for \(x\ge X\) under the specified component bounds. It also converts the resulting estimate into the strict prime interval.
- [`SexticTailJoinPilot.lean`](SexticTailJoinPilot.lean) checks the primality of 400,021,602,885,757 and proves that it witnesses the strict interval for 24,070,136,736 consecutive integer inputs spanning \(X\).
- [`SexticLowZeros.lean`](SexticLowZeros.lean) checks the low-zero contribution for the two smoothing windows as a finite sum of weighted terms. It builds with the same pinned Mathlib as the standalone replay.
- [`conditional-low-zeros/`](conditional-low-zeros/) contains the argument for the actual zeta zeros, with analytic multiplicity, through height 1,890,000. On the finite-height Riemann hypothesis it bounds their contribution by \(30\sqrt{x}\). It combines a low-ordinate reciprocal-weight bound of 1.85 and a higher-ordinate bound of 13.1, then accounts for conjugate zeros and the smoothing factor. These files were kernel-replayed with the analytic dependencies described below.

The scalar budget leaves three main pieces for the unbounded formal result: the higher-zero contribution of at most \(3.9\times10^{-6}(x+1)\), a left-contour remainder of at most 1, and full coverage from the 7,713,133,853 cutoff to the certified join block. The conditional theorem also needs a formally accepted finite-height RH import for the network.

## Conditional proof dependencies

The conditional modules use the same Lean and Mathlib pins as the standalone replay. They also import `BacklundCountEndpoint`, `BacklundHighCount`, `BacklundLowMainTerm` and `RosserTailIntegrals` from [RSBounds at `82d7a55`](https://github.com/Garald1/RSBounds/tree/82d7a55f02e52cd071cd8ed800cc889a23ad3e61), and `Zeta23.ZetaReflect` from [Mercuri and Mehta’s zeta project at `8c33343`](https://github.com/smmercuri/zeta/tree/8c33343004adc68a97f7b46a152c035323163eaa). The original replay used compatibility builds of the upstream modules for Lean 4.33.1. Rebuilding those upstream modules requires equivalent compatibility work before the conditional files can be replayed in an independent checkout. Build them in the order `SexticLowZerosActual`, `SexticLowZerosHighTail`, `SexticLowZerosMoment`, and `SexticLowZerosFiniteRH` after `SexticTailBudget` and `SexticLowZeros`.

The finite-height premise is met by the [published theorem through height 1,895,609](https://github.com/smmercuri/zeta/blob/8c33343004adc68a97f7b46a152c035323163eaa/Zeta/Main.lean#L23-L30). The supplied conditional theorem isolates this premise. The per-ordinate smoothing bounds use the [sixfold coefficient in RSBounds](https://github.com/Garald1/RSBounds/blob/82d7a55f02e52cd071cd8ed800cc889a23ad3e61/RSBounds/SchoenfeldSexticAveraged.lean#L190).
