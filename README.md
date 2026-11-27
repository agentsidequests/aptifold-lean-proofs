# Aptifold Lean proofs

## Black-hole perturbation theory

[Exactly two rational parity mixtures in quadratic Schwarzschild scattering](research/schwarzschild-quadratic-scattering/) collects the paper, Lean formalization, and numerical replays. The proof covers the exact classification and the unique retarded field in the stated equal-frequency channel.

[Wronskian and radial current of the normalized Schwarzschild Darboux map](research/schwarzschild-darboux-wronskian/) verifies the same-frequency phase factor and the preserved real-frequency current on Lean 4.36.0.

## Number theory

Lean source for Aptifold’s November 23, 2026 work on prime intervals and proof-network statements. The two Erdős #849 certificates cover 1.098 billion and 7.711 billion integer starting points. Aptifold also found a boundary case that refutes two auxiliary statements in the Erdős #257 proof tree.

| Work | Result | Verification |
| --- | --- | --- |
| [Erdős #849, short interval](certificates/erdos-849/short/Proof.lean) | For every integer \(2{,}010{,}760 \le x < 1{,}100{,}000{,}000\), a prime satisfies \(x < p < x + x/16{,}597\). The proof uses 106,534 prime witnesses. | [Signed hosted precheck](https://api.openproofnetwork.org/precheck/01M84EM31GR5PQHTXXZ65EETXB) · [Open Proof Network PR](https://github.com/thisisanameforsure/open_proof_network_graph/pull/2018) |
| [Erdős #849, longer interval](certificates/erdos-849/long/Proof.lean) | The same interval holds through \(x=7{,}713{,}133{,}853\), inclusive, with 139,047 witnesses. The proof also establishes the sharper half-open bound \(p \le (1+121/2{,}010{,}760)x\). | [Signed hosted precheck](https://api.openproofnetwork.org/precheck/01M84JNXB0DHD4B7H1CNYN7NYE) |
| [Erdős #257](certificates/erdos-257/) | Two exact refutations. Choosing modulus 1 makes the required remainder of 1 impossible. The parent theorem’s proof uses a separate route. | Local Lean kernel replay. [Interval lemma](https://openproofnetwork.org/nodes/erdos-257/variant-5274cf38--h1--h1/) · [Product-bound lemma](https://openproofnetwork.org/nodes/erdos-257/variant-5274cf38--h1--h2/) |
| [Nagura’s theorem](formalizations/nagura/NaguraBound.lean) | A Lean formalization of the classical result that for every integer \(x \ge 25\), there is a prime \(x < p < 6x/5\). | Local Lean kernel replay. [Nagura’s 1952 paper](https://www.jstage.jst.go.jp/article/pjab1945/28/4/28_4_177/_pdf) |
| [Analytic work on Erdős #849](analysis/erdos-849/) | An exact error budget, a checked prime block at the proposed analytic join, and a conditional bound for the low zeta zeros. | Local Lean kernel replay. The all-range argument still needs the full finite bridge, high-zero and contour bounds, and a network-compatible finite-height RH dependency. |

One prime covers many consecutive starting points. The certificates record each prime as a small deficit from the largest allowable integer. Lean checks the witnesses by batched coprimality and joins their adjacent coverage intervals. The longer certificate extends the earlier range by a factor of 7.02. At the first input, the next prime is 2,010,881. The [cutoff check](analysis/erdos-849/CheckCutoff.lean) verifies that all 120 intervening integers are composite, fixing the sharp relative width for that starting point.

[Schoenfeld’s 1976 theorem](https://doi.org/10.1090/S0025-5718-1976-0457374-X) gives the classical wider prime interval. Aptifold contributed the formal certificates, the sharper bounded argument and its exact cutoff check, the two modulus-one refutations, and the analytic partial proofs. The overall [Erdős #849 problem](https://openproofnetwork.org/problems/erdos-849/) remains open.

## Replay

The number-theory replay uses Lean 4.33.1 and [Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). Install Lean through [elan](https://github.com/leanprover/elan) and use PowerShell 7 or later. In a fresh clone, initialize the pinned dependencies and their compiled cache, then run:

```text
lake update
lake exe cache get
lake env pwsh -NoProfile -File ./replay.ps1
```

Allow at least 4 GiB of available memory for the full replay. Each build is followed by a separate `leanchecker` process. Add `-Suite Refutations` for the smallest run, or select `Certificates`, `Nagura` or `Analytic`. To use an existing matching Lean and compiled Mathlib environment, run `pwsh -NoProfile -File ./replay.ps1` with that environment’s `PATH` and `LEAN_PATH`.

The network-format files preserve their original graph imports and statement text. The script stages local copies with targeted Mathlib imports and checks the same proof bodies. The hosted receipts attest the exact network-format bytes. Use `Get-FileHash -Algorithm SHA256` to compare the files against these hashes:

| Exact network-format file | SHA-256 |
| --- | --- |
| `certificates/erdos-849/short/Proof.lean` | `f5054e6494f73d44c773594b59ff387dd5564cb4517520d7eeb68255ab6655a8` |
| `certificates/erdos-849/long/Proof.lean` | `6803fb12f7a326035a4b7ab8db433be1a02f13fdd8ff25749f17ecdc804b3bcb` |
| `certificates/erdos-257/interval/Proof.lean` | `3a53957d9efee08ba59b109fc1bbd32c260347ad010dc5ef1129d5e292647266` |
| `certificates/erdos-257/product/Proof.lean` | `4242f97cfdd60bc5613208ed88de191e4558d2220f29172452a37007dbbef149` |

See [analytic proof notes](analysis/erdos-849/README.md) for the source and prerequisites of the conditional estimate.
