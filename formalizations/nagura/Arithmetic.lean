import Mathlib.Data.Nat.Prime.Defs

namespace Nagura

def oneAbove (x d : Nat) : Nat := if d ≤ x then 1 else 0

theorem lowerFloor (x : Nat) :
    x / 2 + x / 3 + x / 5 ≤ x + x / 30 ∧
    x + x / 30 ≤ x / 2 + x / 3 + x / 5 + oneAbove x 1 := by
  have residue : ∀ r : Fin 30,
      r.val / 2 + r.val / 3 + r.val / 5 ≤ r.val ∧
      r.val ≤ r.val / 2 + r.val / 3 + r.val / 5 + 1 := by decide +kernel
  let r := x % 30
  let q := x / 30
  obtain ⟨h₁, h₂⟩ := residue ⟨r, Nat.mod_lt x (by decide)⟩
  change r / 2 + r / 3 + r / 5 ≤ r at h₁
  change r ≤ r / 2 + r / 3 + r / 5 + 1 at h₂
  have hq : x = 30 * q + r := by dsimp [q, r]; omega
  have d2 : x / 2 = 15 * q + r / 2 := by omega
  have d3 : x / 3 = 10 * q + r / 3 := by omega
  have d5 : x / 5 = 6 * q + r / 5 := by omega
  have d30 : x / 30 = q := rfl
  by_cases hx : 1 ≤ x
  · rw [oneAbove, if_pos hx, d2, d3, d5, d30]
    omega
  · have hz : x = 0 := by omega
    rw [hz]
    decide

theorem upperFloor (x : Nat) :
    oneAbove x 1 + (x / 2 + x / 3 + x / 7 + x / 43 + x / 1806) ≤
      x + oneAbove x 1806 := by
  have h₂ : 2 * (x / 2) ≤ x := by omega
  have h₃ : 3 * (x / 3) ≤ x := by omega
  have h₇ : 7 * (x / 7) ≤ x := by omega
  have h₄₃ : 43 * (x / 43) ≤ x := by omega
  have h₁₈₀₆ : 1806 * (x / 1806) ≤ x := by omega
  have weak : x / 2 + x / 3 + x / 7 + x / 43 + x / 1806 ≤ x := by omega
  by_cases h : 1806 ≤ x
  · have hpos : 1 ≤ x := by omega
    simp only [oneAbove, if_pos h, if_pos hpos]
    omega
  · by_cases hx : 1 ≤ x
    · simp only [oneAbove, if_pos hx, if_neg h]
      have hz : x / 1806 = 0 := by omega
      omega
    · have hz : x = 0 := by omega
      rw [hz]
      decide

theorem evenFloor (x : Nat) :
    oneAbove x 1 + (x / 2 + x / 2) ≤ x + oneAbove x 2 := by
  unfold oneAbove
  split <;> split <;> omega

theorem upperConstant : 2 ^ 903 * 3 ^ 602 * 7 ^ 258 * 43 ^ 42 * 1806 ≤
    (2 : Nat) ^ 2821 := by decide +kernel

theorem upperNormalize {L : Nat → Nat} (mono : ∀ a b, a ≤ b → L a ≤ L b)
    (h : ∀ m, L (1806 * m) ≤ 2 ^ (2825 * m)) (x : Nat) (hx : 2000000 ≤ x) :
    L x ^ 300 ≤ 2 ^ (471 * x) := by
  let m := (x + 1805) / 1806
  have hm : x ≤ 1806 * m := by dsimp [m]; omega
  have hm' : 1806 * m ≤ x + 1805 := by dsimp [m]; omega
  have hexp : (2825 * m) * 300 ≤ 471 * x := by omega
  calc
    L x ^ 300 ≤ L (1806 * m) ^ 300 := Nat.pow_le_pow_left (mono _ _ hm) _
    _ ≤ (2 ^ (2825 * m)) ^ 300 := Nat.pow_le_pow_left (h m) _
    _ = 2 ^ ((2825 * m) * 300) := (Nat.pow_mul _ _ _).symm
    _ ≤ 2 ^ (471 * x) := Nat.pow_le_pow_right (by decide) hexp

theorem lowerNormalize {L : Nat → Nat} (mono : ∀ a b, a ≤ b → L a ≤ L b)
    (h : ∀ m, 300 ≤ m → 2 ^ (397 * (m - 300)) ≤ L (30 * m) ^ 10)
    (x : Nat) (hx : 2000000 ≤ x) : 2 ^ (395 * x) ≤ L x ^ 300 := by
  let m := x / 30
  have hm : 30 * m ≤ x := by dsimp [m]; omega
  have hm' : x ≤ 30 * m + 29 := by dsimp [m]; omega
  have hm₀ : 300 ≤ m := by omega
  have hexp : 395 * x ≤ (397 * (m - 300)) * 30 := by omega
  calc
    2 ^ (395 * x) ≤ 2 ^ ((397 * (m - 300)) * 30) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2 ^ (397 * (m - 300))) ^ 30 := Nat.pow_mul _ _ _
    _ ≤ (L (30 * m) ^ 10) ^ 30 := Nat.pow_le_pow_left (h m hm₀) _
    _ = L (30 * m) ^ 300 := (Nat.pow_mul _ _ _).symm
    _ ≤ L x ^ 300 := Nat.pow_le_pow_left (mono _ _ hm) _

theorem largeOfBounds {L : Nat → Nat}
    (upper : ∀ n, 2000000 ≤ n → L n ^ 300 ≤ 2 ^ (471 * n))
    (lower : ∀ n, 2000000 ≤ n → 2 ^ (395 * n) ≤ L n ^ 300)
    (crude : ∀ n, L n ≤ 2 ^ (4 * n))
    (correction : ∀ x y m, y < (m + 1) * (m + 1) →
      (∀ p, p.Prime → x < p → p ≤ y → False) → L y ≤ L x * L m ^ 2)
    (x : Nat) (hx : 2000000 ≤ x) :
    ∃ p : Nat, p.Prime ∧ x < p ∧ 5 * p < 6 * x := by
  let y := (6 * x - 1) / 5
  let m := x / 1000
  have hy : 5 * y < 6 * x := by dsimp [y]; omega
  have hy' : 6 * x ≤ 5 * y + 5 := by dsimp [y]; omega
  have hbig : 2000000 ≤ y := by omega
  have hm : x ≤ 1000 * m + 999 := by dsimp [m]; omega
  have hm' : 1000 * m ≤ x := by dsimp [m]; omega
  have hm₀ : 1200 ≤ m + 1 := by omega
  have hcut : y < 1200 * (m + 1) := by omega
  have hsq : y < (m + 1) * (m + 1) :=
    hcut.trans_le (Nat.mul_le_mul_right (m + 1) hm₀)
  have hexp : 471 * x + 2400 * m < 395 * y := by omega
  apply Classical.byContradiction
  intro absent
  have noPrime (p : Nat) (hprime : p.Prime) (hx' : x < p) (hy' : p ≤ y) : False :=
    absent ⟨p, hprime, hx', by omega⟩
  have bound : 2 ^ (395 * y) ≤ 2 ^ (471 * x + 2400 * m) := calc
    2 ^ (395 * y) ≤ L y ^ 300 := lower y hbig
    _ ≤ (L x * L m ^ 2) ^ 300 := Nat.pow_le_pow_left (correction x y m hsq noPrime) _
    _ = L x ^ 300 * (L m ^ 2) ^ 300 := Nat.mul_pow _ _ _
    _ ≤ 2 ^ (471 * x) * ((2 ^ (4 * m)) ^ 2) ^ 300 :=
      Nat.mul_le_mul (upper x hx) (Nat.pow_le_pow_left (Nat.pow_le_pow_left (crude m) _) _)
    _ = 2 ^ (471 * x + 2400 * m) := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
      congr 1
      omega
  exact (Nat.not_lt_of_ge bound) (Nat.pow_lt_pow_right (by decide) hexp)

end Nagura
