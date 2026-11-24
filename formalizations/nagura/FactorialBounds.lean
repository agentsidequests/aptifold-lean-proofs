import Arithmetic
import Mathlib.Data.Nat.Choose.Basic

namespace Nagura

open Nat

-- A term of the binomial expansion is bounded by the whole expansion.
-- Induction on the two indices avoids importing the real analysis stack.
theorem chooseWeight (a b s t : Nat) :
    (s + t).choose s * a ^ s * b ^ t ≤ (a + b) ^ (s + t) := by
  induction s generalizing t with
  | zero =>
    simpa using Nat.pow_le_pow_left (Nat.le_add_left b a) t
  | succ s hs =>
    induction t with
    | zero =>
      simpa using Nat.pow_le_pow_left (Nat.le_add_right a b) (s + 1)
    | succ t ht =>
      have sumEq : s + 1 + (t + 1) = (s + (t + 1)) + 1 := by omega
      have prev : s + (t + 1) = s + 1 + t := by omega
      calc
        (s + 1 + (t + 1)).choose (s + 1) * a ^ (s + 1) * b ^ (t + 1)
            = a * ((s + (t + 1)).choose s * a ^ s * b ^ (t + 1)) +
                b * ((s + 1 + t).choose (s + 1) * a ^ (s + 1) * b ^ t) := by
              rw [sumEq, Nat.choose_succ_succ, prev]
              simp only [Nat.succ_eq_add_one, Nat.pow_succ, Nat.add_mul]
              grind
        _ ≤ a * (a + b) ^ (s + (t + 1)) + b * (a + b) ^ (s + 1 + t) :=
              Nat.add_le_add (Nat.mul_le_mul_left a (hs (t + 1)))
                (Nat.mul_le_mul_left b ht)
        _ = (a + b) ^ (s + 1 + (t + 1)) := by
              rw [← prev, ← Nat.add_mul, sumEq, Nat.pow_succ, Nat.mul_comm]

def lowerNumerator (m : Nat) : Nat := (30 * m)! * (m !)

def lowerDenominator (m : Nat) : Nat := (15 * m)! * (10 * m)! * (6 * m)!

def upperDenominator (m : Nat) : Nat :=
  (903 * m)! * (602 * m)! * (258 * m)! * (42 * m)! * (m !)

private def rising (start : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => rising start k * (start + k + 1)

private theorem risingLower (start k : Nat) : start ^ k ≤ rising start k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, rising]
    exact Nat.mul_le_mul ih (by omega)

private theorem risingUpper (start k : Nat) : rising start k ≤ (start + k) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rising, Nat.pow_succ]
    exact Nat.mul_le_mul_right _
      (ih.trans (Nat.pow_le_pow_left (by omega) _))

private theorem factorialRising (start k : Nat) : (start + k)! = (start !) * rising start k := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [Nat.add_succ, Nat.factorial_succ, ih, rising]
    rw [Nat.mul_comm (start + k + 1), Nat.mul_assoc]

private theorem factorialStep (d m : Nat) : (d * (m + 1))! = (d * m)! * rising (d * m) d := by
  rw [Nat.mul_add, Nat.mul_one, factorialRising]

private def nextNumerator (m : Nat) : Nat := rising (30 * m) 30 * (m + 1)

private def nextDenominator (m : Nat) : Nat :=
  rising (15 * m) 15 * rising (10 * m) 10 * rising (6 * m) 6

private theorem groupTwo (a b c d : Nat) : (a * b) * (c * d) = (a * d) * (b * c) := by
  grind

private theorem lowerNumeratorStep (m : Nat) :
    lowerNumerator (m + 1) = lowerNumerator m * nextNumerator m := by
  unfold lowerNumerator nextNumerator
  rw [factorialStep 30 m, Nat.factorial_succ m]
  exact groupTwo _ _ _ _

private theorem groupThree (a b c x y z : Nat) :
    (a * x) * (b * y) * (c * z) = (a * b * c) * (x * y * z) := by
  grind

private theorem lowerDenominatorStep (m : Nat) :
    lowerDenominator (m + 1) = lowerDenominator m * nextDenominator m := by
  calc
    lowerDenominator (m + 1) =
        ((15 * m)! * rising (15 * m) 15) * ((10 * m)! * rising (10 * m) 10) *
          ((6 * m)! * rising (6 * m) 6) :=
      congrArg₂ Nat.mul
        (congrArg₂ Nat.mul (factorialStep 15 m) (factorialStep 10 m)) (factorialStep 6 m)
    _ = lowerDenominator m * nextDenominator m := groupThree _ _ _ _ _ _

private def numScale : Nat := 30 ^ 30
private def denScale : Nat := 15 ^ 15 * 10 ^ 10 * 6 ^ 6

private theorem nextNumeratorBound (m : Nat) : numScale * m ^ 31 ≤ nextNumerator m := by
  calc
    numScale * m ^ 31 = (30 * m) ^ 30 * m := by
      rw [numScale, Nat.mul_pow, Nat.pow_succ m 30]
      exact (Nat.mul_assoc _ _ _).symm
    _ ≤ nextNumerator m := Nat.mul_le_mul (risingLower _ _) (Nat.le_succ m)

private theorem nextDenominatorBound (m : Nat) :
    nextDenominator m ≤ denScale * (m + 1) ^ 31 := by
  calc
    nextDenominator m ≤ (15 * m + 15) ^ 15 * (10 * m + 10) ^ 10 * (6 * m + 6) ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul (risingUpper _ _) (risingUpper _ _)) (risingUpper _ _)
    _ = denScale * (((m + 1) ^ 15 * (m + 1) ^ 10) * (m + 1) ^ 6) := by
      rw [show 15 * m + 15 = 15 * (m + 1) by omega,
          show 10 * m + 10 = 10 * (m + 1) by omega,
          show 6 * m + 6 = 6 * (m + 1) by omega]
      simp only [denScale, Nat.mul_pow]
      exact groupThree _ _ _ _ _ _
    _ = denScale * (m + 1) ^ 31 := by rw [← Nat.pow_add, ← Nat.pow_add]

private theorem rescalePowers (A B K a b r s u v : Nat) (ha : 0 < a)
    (scale : a * u ≤ b * v) (constant : K * (B * b ^ r) ^ s ≤ (A * a ^ r) ^ s) :
    K * (B * u ^ r) ^ s ≤ (A * v ^ r) ^ s := by
  have hn : 0 < (a ^ r) ^ s := Nat.pow_pos (Nat.pow_pos ha)
  apply Nat.le_of_mul_le_mul_right _ hn
  calc
    (K * (B * u ^ r) ^ s) * (a ^ r) ^ s =
        K * (B * (a * u) ^ r) ^ s := by
        rw [Nat.mul_assoc K, ← Nat.mul_pow (B * u ^ r) (a ^ r) s, Nat.mul_assoc B,
          Nat.mul_comm (u ^ r) (a ^ r), ← Nat.mul_pow a u r]
    _ ≤ K * (B * (b * v) ^ r) ^ s :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scale _)) _)
    _ = (K * (B * b ^ r) ^ s) * (v ^ r) ^ s := by
        rw [Nat.mul_pow b v r, ← Nat.mul_assoc B, Nat.mul_pow (B * b ^ r) (v ^ r) s,
          ← Nat.mul_assoc K]
    _ ≤ (A * a ^ r) ^ s * (v ^ r) ^ s :=
        Nat.mul_le_mul_right _ constant
    _ = (A * v ^ r) ^ s * (a ^ r) ^ s := by
        rw [← Nat.mul_pow (A * a ^ r) (v ^ r) s, ← Nat.mul_pow (A * v ^ r) (a ^ r) s,
          Nat.mul_assoc A, Nat.mul_assoc A, Nat.mul_comm (a ^ r) (v ^ r)]

private theorem nextRatio (m : Nat) (hm : 300 ≤ m) :
    2 ^ 397 * nextDenominator m ^ 10 ≤ nextNumerator m ^ 10 := by
  have scale : 300 * (m + 1) ≤ 301 * m := by omega
  calc
    2 ^ 397 * nextDenominator m ^ 10 ≤ 2 ^ 397 * (denScale * (m + 1) ^ 31) ^ 10 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (nextDenominatorBound m) _)
    _ ≤ (numScale * m ^ 31) ^ 10 :=
      rescalePowers numScale denScale (2 ^ 397) 300 301 31 10 _ _
        (by decide) scale (by decide +kernel)
    _ ≤ nextNumerator m ^ 10 := Nat.pow_le_pow_left (nextNumeratorBound m) _

private theorem crossProducts (a b c d : Nat) : a * b * (c * d) = (a * c) * (b * d) := by
  grind

theorem lowerGrowth (base : lowerDenominator 300 ≤ lowerNumerator 300)
    (k : Nat) : 2 ^ (397 * k) * lowerDenominator (300 + k) ^ 10 ≤
      lowerNumerator (300 + k) ^ 10 := by
  induction k with
  | zero => simpa using Nat.pow_le_pow_left base 10
  | succ k ih =>
    change 2 ^ (397 * (k + 1)) * lowerDenominator (300 + k + 1) ^ 10 ≤
      lowerNumerator (300 + k + 1) ^ 10
    rw [lowerDenominatorStep, lowerNumeratorStep, Nat.mul_add, Nat.mul_one,
      Nat.pow_add, Nat.mul_pow, Nat.mul_pow]
    calc
      2 ^ (397 * k) * 2 ^ 397 *
          (lowerDenominator (300 + k) ^ 10 * nextDenominator (300 + k) ^ 10) =
        (2 ^ (397 * k) * lowerDenominator (300 + k) ^ 10) *
           (2 ^ 397 * nextDenominator (300 + k) ^ 10) := crossProducts _ _ _ _
      _ ≤ lowerNumerator (300 + k) ^ 10 * nextNumerator (300 + k) ^ 10 :=
        Nat.mul_le_mul ih (nextRatio _ (Nat.le_add_right 300 k))

def upperBase : Nat := 2 ^ 903 * 3 ^ 602 * 7 ^ 258 * 43 ^ 42 * 1806

private def upperWeights : Nat := 2 ^ 602 * 6 ^ 258 * 42 ^ 42

private theorem interleave (a b c d x y z : Nat) :
    (a * b * c * d) * (x * y * z) = a * (b * x) * (c * y) * (d * z) := by
  grind

private theorem powerThree (a b c m : Nat) :
    (a * b * c) ^ m = a ^ m * b ^ m * c ^ m :=
  (Nat.mul_pow (a * b) c m).trans (congrArg (fun r => r * c ^ m) (Nat.mul_pow a b m))

private theorem collectFactors (a b c d f g h i j : Nat) :
    a * f * (b * g * (c * h * (d * i * j))) = (f * g * h * i * j) * (a * b * c * d) := by
  grind

theorem factorialSplit (s t : Nat) : (s + t)! = (s + t).choose s * (s !) * (t !) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := s + t) (k := s) (by omega)
  simpa using h.symm

theorem upperFactorial (m : Nat) : (1806 * m)! ≤ upperDenominator m * upperBase ^ m := by
  let c₁ := (1806 * m).choose (903 * m)
  let c₂ := (903 * m).choose (602 * m)
  let c₃ := (301 * m).choose (258 * m)
  let c₄ := (43 * m).choose (42 * m)
  have h₁ : c₁ ≤ 2 ^ (1806 * m) := by
    simpa [c₁, show 903 * m + 903 * m = 1806 * m by omega] using
      chooseWeight 1 1 (903 * m) (903 * m)
  have h₂ : c₂ * 2 ^ (602 * m) ≤ 3 ^ (903 * m) := by
    simpa [c₂, show 602 * m + 301 * m = 903 * m by omega] using
      chooseWeight 2 1 (602 * m) (301 * m)
  have h₃ : c₃ * 6 ^ (258 * m) ≤ 7 ^ (301 * m) := by
    simpa [c₃, show 258 * m + 43 * m = 301 * m by omega] using
      chooseWeight 6 1 (258 * m) (43 * m)
  have h₄ : c₄ * 42 ^ (42 * m) ≤ 43 ^ (43 * m) := by
    simpa [c₄, show 42 * m + m = 43 * m by omega] using chooseWeight 42 1 (42 * m) m
  have constant : upperBase * upperWeights = 2 ^ 1806 * 3 ^ 903 * 7 ^ 301 * 43 ^ 43 := by
    decide +kernel
  have weightsPos : 0 < upperWeights := by decide +kernel
  have expanded : (c₁ * c₂ * c₃ * c₄) * upperWeights ^ m =
      c₁ * (c₂ * 2 ^ (602 * m)) * (c₃ * 6 ^ (258 * m)) * (c₄ * 42 ^ (42 * m)) := by
    have weights : upperWeights ^ m = 2 ^ (602 * m) * 6 ^ (258 * m) * 42 ^ (42 * m) :=
      (powerThree (2 ^ 602) (6 ^ 258) (42 ^ 42) m).trans
        (congrArg₂ Nat.mul
          (congrArg₂ Nat.mul (Nat.pow_mul 2 602 m).symm (Nat.pow_mul 6 258 m).symm)
          (Nat.pow_mul 42 42 m).symm)
    exact (congrArg (fun t => (c₁ * c₂ * c₃ * c₄) * t) weights).trans
      (interleave c₁ c₂ c₃ c₄ (2 ^ (602 * m)) (6 ^ (258 * m)) (42 ^ (42 * m)))
  have folded : (2 : Nat) ^ (1806 * m) * 3 ^ (903 * m) * 7 ^ (301 * m) * 43 ^ (43 * m) =
      upperBase ^ m * upperWeights ^ m := by
    rw [← Nat.mul_pow upperBase upperWeights m, constant,
      Nat.mul_pow (2 ^ 1806 * 3 ^ 903 * 7 ^ 301) (43 ^ 43) m,
      Nat.mul_pow (2 ^ 1806 * 3 ^ 903) (7 ^ 301) m, Nat.mul_pow (2 ^ 1806) (3 ^ 903) m,
      ← Nat.pow_mul 2 1806 m, ← Nat.pow_mul 3 903 m, ← Nat.pow_mul 7 301 m,
      ← Nat.pow_mul 43 43 m]
  have hprod : c₁ * c₂ * c₃ * c₄ ≤ upperBase ^ m := by
    have productBound := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃) h₄
    exact Nat.le_of_mul_le_mul_right
      (expanded.le.trans (productBound.trans folded.le)) (Nat.pow_pos (n := m) weightsPos)
  have f₁ : (1806 * m)! = c₁ * (903 * m)! * (903 * m)! := by
    simpa [c₁, show 903 * m + 903 * m = 1806 * m by omega] using
      factorialSplit (903 * m) (903 * m)
  have f₂ : (903 * m)! = c₂ * (602 * m)! * (301 * m)! := by
    simpa [c₂, show 602 * m + 301 * m = 903 * m by omega] using
      factorialSplit (602 * m) (301 * m)
  have f₃ : (301 * m)! = c₃ * (258 * m)! * (43 * m)! := by
    simpa [c₃, show 258 * m + 43 * m = 301 * m by omega] using
      factorialSplit (258 * m) (43 * m)
  have f₄ : (43 * m)! = c₄ * (42 * m)! * (m !) := by
    simpa [c₄, show 42 * m + m = 43 * m by omega] using factorialSplit (42 * m) m
  calc
    (1806 * m)! = c₁ * (903 * m)! * (c₂ * (602 * m)! * (301 * m)!) :=
      f₁.trans (congrArg (fun n => c₁ * (903 * m)! * n) f₂)
    _ = upperDenominator m * (c₁ * c₂ * c₃ * c₄) := by
      rw [f₃, f₄]
      unfold upperDenominator
      exact collectFactors _ _ _ _ _ _ _ _ _
    _ ≤ upperDenominator m * upperBase ^ m := Nat.mul_le_mul_left _ hprod

end Nagura
