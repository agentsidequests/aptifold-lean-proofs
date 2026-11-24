import Lean.Elab.Tactic.Omega
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

/-!
# The final witness block at the proposed analytic join

One recursively certified prime covers the block crossing 4 × 10^14.
Lean checks the witness from its Lucas certificate. The preceding blocks
still need their own certificates.
-/

namespace ShortPrimeInterval.SexticTailJoin

private theorem prime_dvd_prod_mem {q : ℕ} (hq : q.Prime) (factors : List ℕ)
    (primes : ∀ p ∈ factors, Nat.Prime p) (hd : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    have hone : q ∣ 1 := by simpa using hd
    exact (hq.ne_one (Nat.dvd_one.mp hone)).elim
  | cons p ps ih =>
    rw [List.prod_cons] at hd
    rcases hq.dvd_mul.mp hd with h | h
    · exact List.mem_cons.mpr
        (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (primes p (by simp))).1 h))
    · exact List.mem_cons.mpr (Or.inr (ih (fun r hr => primes r (List.mem_cons_of_mem _ hr)) h))

private theorem prime_certificate (p a : ℕ) (factors : List ℕ)
    (factorization : factors.prod = p - 1)
    (primes : ∀ q ∈ factors, Nat.Prime q)
    (full : (a : ZMod p) ^ (p - 1) = 1)
    (proper : ∀ q ∈ factors, (a : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    p.Prime := by
  apply lucas_primality p (a : ZMod p) full
  intro q hq hd
  rw [← factorization] at hd
  exact proper q (prime_dvd_prod_mem hq factors primes hd)

private theorem prime1543 : Nat.Prime 1543 := by
  apply prime_certificate 1543 5 [2, 3, 257] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide +kernel
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> (reduce_mod_char; decide +kernel)

private theorem prime562519 : Nat.Prime 562519 := by
  apply prime_certificate 562519 6 [2, 3, 3, 3, 11, 947] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide +kernel)

private theorem prime300316518683 : Nat.Prime 300316518683 := by
  apply prime_certificate 300316518683 2 [2, 173, 1543, 562519] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · decide +kernel
    · exact prime1543
    · exact prime562519
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide +kernel)

theorem primeAtJoin : Nat.Prime 400021602885757 := by
  apply prime_certificate 400021602885757 2 [2, 2, 3, 3, 37, 300316518683] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact prime300316518683 | decide +kernel
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide +kernel)

theorem blockAtJoin (x : ℕ) (lo : 399997532749021 ≤ x) (hi : x < 400021602885757) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ 16618 * p < 16619 * x :=
  ⟨400021602885757, primeAtJoin, hi, by omega⟩

end ShortPrimeInterval.SexticTailJoin
