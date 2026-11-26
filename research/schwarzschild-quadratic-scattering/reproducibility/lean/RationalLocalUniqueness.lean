import AdmittedMixtures
import HomogeneousMatrixRank
import RationalHomogeneousBounds
import RationalRowExclusion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Uniqueness of a rational particular row for a fixed source in the
projected equal-frequency Schwarzschild channel. -/
namespace SchwarzschildLaurent

open SchwarzschildMatrix
open scoped BigOperators

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private def angularFactor {A : Type*} [CommRing A] (l : A) : A :=
  259*l^8 + 524*l^7 + 134*l^6 - 280*l^5 - 133*l^4 + 44*l^3 + 28*l^2

private theorem angularFactor_positive (l : ℝ) (hl : 2 ≤ l) : 0 < angularFactor l := by
  let d := l-2
  have hd : 0 ≤ d := sub_nonneg.mpr hl
  have shift :
      angularFactor l = 131328 + 499680*d + 823116*d^2 + 766788*d^3 +
        441907*d^4 + 161376*d^5 + 36478*d^6 + 4668*d^7 + 259*d^8 := by
    dsimp [angularFactor, d]
    ring
  rw [shift]
  positivity

private theorem evaluated_target (k l : ℂ) :
    evalPoly k l homogeneousTarget =
      (-362125209600 : ℂ)*l*(3*l+1)*(1008*k^2-angularFactor l) := by
  norm_num [homogeneousTarget, evalPoly, evalAngular, angularFactor]; ring

theorem homogeneous_target_ne_zero (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    evalPoly k (n : ℂ) homogeneousTarget ≠ 0 := by
  have hr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ang : 0 < angularFactor (n : ℝ) := angularFactor_positive _ hr
  have cast : Complex.ofRealHom (angularFactor (n : ℝ)) = angularFactor (n : ℂ) := by
    simp only [angularFactor, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast]
  have realAng : (angularFactor (n : ℂ)).re = angularFactor (n : ℝ) := by
    rw [← cast]
    rfl
  have negative : (1008*k^2 - angularFactor (n : ℂ)).re < 0 := by
    rw [Complex.sub_re, realAng, pow_two, Complex.mul_re]
    norm_num [Complex.mul_re, ki]
    nlinarith [sq_nonneg k.im]
  have l0 : (n : ℂ) ≠ 0 := by
    intro e
    have h := congrArg Complex.re e
    norm_num at h
    linarith
  have factor0 : (3*(n : ℂ)+1) ≠ 0 := by
    intro e
    have h := congrArg Complex.re e
    norm_num [Complex.add_re, Complex.mul_re] at h
    linarith
  have quadratic0 : (1008*k^2-angularFactor (n : ℂ)) ≠ 0 := by
    intro e
    rw [e, Complex.zero_re] at negative
    exact (lt_irrefl 0) negative
  rw [evaluated_target]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) l0) factor0) quadratic0

private def pad (retained : ℕ) (coeff : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i < retained then coeff i else 0

private theorem padded_span (full retained : ℕ) (fits : retained ≤ full) (coeff : ℕ → ℂ) :
    laurentSpan full (pad retained coeff) = laurentSpan retained coeff := by
  unfold laurentSpan
  calc
    _ = ∑ i ∈ Finset.range retained,
        Cᵣ (pad retained coeff i)*(RatFunc.X : ℂᵣ)^((i : ℤ)-7) := by
      symm
      apply Finset.sum_subset (Finset.range_mono fits)
      intro i _ absent
      have large : ¬ i < retained := fun hi => absent (Finset.mem_range.mpr hi)
      simp [pad, large]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pad, if_pos (Finset.mem_range.mp hi)]

private theorem weight_at_index (a : Row (ℕ → ℂ)) (j i : ℕ) :
    columnWeights a (j, (i : ℤ)-7) = rowComponent j a i := by
  unfold columnWeights
  rw [show ((i : ℤ)-7+7).toNat = i from (by omega)]

private theorem column_in_range (j count i : ℕ) (hi : i < count) :
    (j, (i : ℤ)-7) ∈ (List.range count).map (fun (h : ℕ) => (j, (h : ℤ)-7)) :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem padded_support (a : Row (ℕ → ℂ))
    (col : ℕ × ℤ) (member : col ∈ columnLabels) (absent : col ∉ homogeneousColumns) :
    columnWeights (pad 8 a.1, pad 6 a.2.1, pad 4 a.2.2) col = 0 := by
  simp only [columnLabels, List.mem_append, List.mem_map, List.mem_range] at member
  rcases member with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩
  · have large : ¬ i < 8 := fun hi => absent
      (List.mem_append_left _ (List.mem_append_left _ (column_in_range 0 8 i hi)))
    simp only [weight_at_index, rowComponent, pad, if_neg large]
  · have large : ¬ i < 6 := fun hi => absent
      (List.mem_append_left _ (List.mem_append_right _ (column_in_range 1 6 i hi)))
    simp only [weight_at_index, rowComponent, pad, if_neg large]
  · have large : ¬ i < 4 := fun hi => absent
      (List.mem_append_right _ (column_in_range 2 4 i hi))
    simp only [weight_at_index, rowComponent, pad, if_neg large]

theorem homogeneous_rational_row_zero (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (u : Row ℂᵣ) (homogeneous : rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k u = 0) :
    u = 0 := by
  obtain ⟨a, span⟩ := short_span_for_homogeneous_row _ _ k hk ki u homogeneous
  let b : Row (ℕ → ℂ) := (pad 8 a.1, pad 6 a.2.1, pad 4 a.2.2)
  have expanded : (laurentSpan 12 b.1, laurentSpan 10 b.2.1, laurentSpan 8 b.2.2) = u := by
    rw [span]
    exact Prod.ext (padded_span 12 8 (by decide) a.1)
      (Prod.ext (padded_span 10 6 (by decide) a.2.1) (padded_span 8 4 (by decide) a.2.2))
  have equations := matrix_equations_from_homogeneous_span k n b (by rw [expanded]; exact homogeneous)
  have target0 := homogeneous_target_ne_zero n hn k ki
  have hzero (col : ℕ × ℤ) (hi : col ∈ homogeneousColumns) : columnWeights b col = 0 :=
    (mul_eq_zero.mp (homogeneous_coordinate_certificate k n (columnWeights b)
      (padded_support a) equations col hi)).resolve_left target0
  have a0 (i : ℕ) (hi : i < 8) : a.1 i = 0 := by
    simpa only [b, weight_at_index, rowComponent, pad, if_pos hi] using
      hzero (0, (i : ℤ)-7) (List.mem_append_left _ (List.mem_append_left _ (column_in_range 0 8 i hi)))
  have a1 (i : ℕ) (hi : i < 6) : a.2.1 i = 0 := by
    simpa only [b, weight_at_index, rowComponent, pad, if_pos hi] using
      hzero (1, (i : ℤ)-7) (List.mem_append_left _ (List.mem_append_right _ (column_in_range 1 6 i hi)))
  have a2 (i : ℕ) (hi : i < 4) : a.2.2 i = 0 := by
    simpa only [b, weight_at_index, rowComponent, pad, if_pos hi] using
      hzero (2, (i : ℤ)-7) (List.mem_append_right _ (column_in_range 2 4 i hi))
  have vanishes (count : ℕ) (c : ℕ → ℂ) (hc : ∀ i < count, c i = 0) : laurentSpan count c = 0 := by
    unfold laurentSpan
    exact Finset.sum_eq_zero fun i hi => by rw [hc i (Finset.mem_range.mp hi), map_zero, zero_mul]
  rw [span, vanishes 8 a.1 a0, vanishes 6 a.2.1 a1, vanishes 4 a.2.2 a2]
  rfl

/-- Equality of the daughter sources fixes the rational quadratic jet row. -/
theorem rational_particular_row_unique (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (u v : Row ℂᵣ)
    (same : rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k u =
      rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k v) : u = v := by
  have z := homogeneous_rational_row_zero n hn k hk ki (minus u v) (by
    rw [operator_minus, same]
    simp [minus])
  exact Prod.ext (sub_eq_zero.mp (congrArg Prod.fst z))
    (Prod.ext (sub_eq_zero.mp (congrArg (fun a => a.2.1) z))
      (sub_eq_zero.mp (congrArg (fun a => a.2.2) z)))

theorem admitted_rational_row_exists_unique (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃! u : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k u =
      SchwarzschildMixtures.admittedSource second k n := by
  have solves := SchwarzschildMixtures.admitted_field_solves second n hn k hk ki
  exact ⟨_, solves, fun v h => rational_particular_row_unique n hn k hk ki v _ (h.trans solves.symm)⟩

#print axioms homogeneous_target_ne_zero
#print axioms homogeneous_rational_row_zero
#print axioms rational_particular_row_unique
#print axioms admitted_rational_row_exists_unique

end
end SchwarzschildLaurent
