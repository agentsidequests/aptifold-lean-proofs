import Mathlib.Data.Nat.Prime.Defs
import Lean

namespace Erdos849

private def smallFactors : Array Nat :=
  #[251, 2, 41, 2, 3, 2, 11, 2, 1103, 2, 3, 2,
    29, 2, 5, 2, 3, 2, 59, 2, 419, 2, 3, 2,
    5, 2, 79, 2, 3, 2, 71, 2, 367, 2, 3, 2,
    1151, 2, 7, 2, 3, 2, 617, 2, 5, 2, 3, 2,
    43, 2, 11, 2, 3, 2, 5, 2, 641, 2, 3, 2,
    23, 2, 487, 2, 3, 2, 7, 2, 887, 2, 3, 2,
    11, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2,
    5, 2, 167, 2, 3, 2, 107, 2, 13, 2, 3, 2,
    1367, 2, 293, 2, 3, 2, 593, 2, 5, 2, 3, 2,
    7, 2, 67, 2, 3, 2, 5, 2, 11, 2, 3, 2]

private theorem factorsValid : ∀ k : Fin 120,
    let d := smallFactors[k.val]!
    2 ≤ d ∧ d < 2010761 + k.val ∧ d ∣ 2010761 + k.val := by decide +kernel

private theorem allBeforeNextAreComposite (k : Fin 120) :
    ¬ Nat.Prime (2010761 + k.val) := by
  intro prime
  obtain ⟨lo, hi, divides⟩ := factorsValid k
  exact (Nat.prime_def_lt'.1 prime).2 _ lo hi divides

theorem noEarlierPrime :
    ∀ p : Nat, 2010760 < p → Nat.Prime p → 2010881 ≤ p := by
  intro p lo isPrime
  by_cases hi : 2010881 ≤ p
  · exact hi
  · let k : Fin 120 := ⟨p - 2010761, by omega⟩
    have recovered : 2010761 + k.val = p := by
      dsimp [k]
      omega
    exact False.elim (allBeforeNextAreComposite k (recovered.symm ▸ isPrime))

theorem narrowerAtCutoffImpossible :
    ¬ (∃ p : Nat, Nat.Prime p ∧ 2010760 < p ∧ 2010760 * p < 2010881 * 2010760) := by
  rintro ⟨p, isPrime, lo, tooSmall⟩
  have hi := noEarlierPrime p lo isPrime
  omega

#print axioms noEarlierPrime
#print axioms narrowerAtCutoffImpossible

end Erdos849
