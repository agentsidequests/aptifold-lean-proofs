import MixtureClassification
import RationalLocalUniqueness

/-! The top daughter multiplet in the polynomial normalization of the
maximal Clebsch–Gordan product. The coefficients of the two parent
profiles include their binomial normalization factors. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "L[" n "," k "]" =>
  rationalOperator ((n : ℂ)*(n+1)) ((2*(n : ℂ))*(2*n+1)) k

/-- Each coefficient measures the non-image part of one angular mode. -/
def angularObstruction (rho : ℂ) (even odd : ℂ[X]) : ℂ[X] :=
  (odd-even)*(odd-C rho*even)

private def admittedCombination (k ell : ℂ) (even odd : ℂ[X]) (m : ℕ)
    (first second : Row ℂᵣ) : Row ℂᵣ :=
  plus (scale (Cᵣ ((even^2).coeff m)) first)
    (scale (Cᵣ ((C ((alternativeRatio k ell-1)⁻¹)*even*(odd-even)).coeff m))
      (minus second first))

/-- One coefficient of the regularized source for the top daughter.
    Its physical harmonic coefficient is obtained by a nonzero angular rescaling. -/
def angularSource (n m : ℕ) (k : ℂ) (even odd : ℂ[X]) : Row ℂᵣ :=
  plus (admittedCombination k n even odd m (admittedSource false k n) (admittedSource true k n))
    (scale (Cᵣ ((angularObstruction (alternativeRatio k n) even odd).coeff m)) (publishedOdd k n))

/-- Weights on the first admitted, second admitted, and pure-odd sources. -/
def angularSourceWeights (n m : ℕ) (k : ℂ) (even odd : ℂ[X]) : Row ℂ :=
  let rho := alternativeRatio k n
  let d := (C ((rho-1)⁻¹)*even*(odd-even)).coeff m
  ((even^2).coeff m-d,d,(angularObstruction rho even odd).coeff m)

theorem angular_source_from_three_rows (n m : ℕ) (k : ℂ) (even odd : ℂ[X]) :
    let w := angularSourceWeights n m k even odd
    angularSource n m k even odd =
      plus (scale (Cᵣ w.1) (admittedSource false k n))
        (plus (scale (Cᵣ w.2.1) (admittedSource true k n))
          (scale (Cᵣ w.2.2) (publishedOdd k n))) := by
  dsimp only [angularSource, admittedCombination, angularSourceWeights]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [plus, scale, minus, map_sub] <;> ring

private theorem angular_coefficient_identity (rho : ℂ) (different : rho ≠ 1)
    (even odd : ℂ[X]) (m : ℕ) :
    let a := (even^2).coeff m
    let d := (C ((rho-1)⁻¹)*even*(odd-even)).coeff m
    let h := (angularObstruction rho even odd).coeff m
    a+(rho-1)*d = (even*odd).coeff m ∧
      a+(rho^2-1)*d+h = (odd^2).coeff m := by
  let d := C ((rho-1)⁻¹)*even*(odd-even)
  have product : C (rho-1)*d = even*(odd-even) := by
    calc
      _ = (C (rho-1)*C ((rho-1)⁻¹))*even*(odd-even) := by dsimp [d]; ring
      _ = _ := by rw [← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr different), map_one, one_mul]
  have mixed : even^2+C (rho-1)*d = even*odd := by rw [product]; ring
  have pure : even^2+C (rho^2-1)*d+angularObstruction rho even odd = odd^2 := by
    rw [show rho^2-1 = (rho+1)*(rho-1) from (by ring), map_mul, mul_assoc,
      product, angularObstruction, map_add, map_one]
    ring
  exact ⟨by simpa only [coeff_add, coeff_C_mul] using congrArg (fun p => p.coeff m) mixed,
    by simpa only [coeff_add, coeff_C_mul] using congrArg (fun p => p.coeff m) pure⟩

/-- Polarizing the top-mode source replaces the three scalar products by
    the same coefficients of the angular polynomial products. -/
theorem angular_source_from_quadratic_coefficients (n m : ℕ) (k : ℂ)
    (even odd : ℂ[X]) (ee eo : Row ℂᵣ) (different : alternativeRatio k n ≠ 1)
    (first : quadraticSource ee eo (publishedOdd k n) 1 1 = admittedSource false k n)
    (second : quadraticSource ee eo (publishedOdd k n) 1 (alternativeRatio k n) =
      admittedSource true k n) :
    angularSource n m k even odd =
      plus (scale (Cᵣ ((even^2).coeff m)) ee)
        (plus (scale (Cᵣ ((even*odd).coeff m)) eo)
          (scale (Cᵣ ((odd^2).coeff m)) (publishedOdd k n))) := by
  obtain ⟨mixed, pure⟩ := angular_coefficient_identity _ different even odd m
  unfold angularSource admittedCombination
  rw [← first, ← second, ← mixed, ← pure]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [quadraticSource, plus, scale, minus, map_add, map_sub, map_mul, map_pow,
      map_one, one_pow, one_mul] <;> ring

private theorem pureOddHasNoRow (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ¬ ∃ row : Row ℂᵣ, L[n,k] row = publishedOdd k n := by
  rintro ⟨row, eq⟩
  have e : publishedForcing k n 0 1 = publishedOdd k n := by
    simp [publishedForcing, interpolatedSource, oddWeight, plus, scale]
  have bad := (rational_mixture_classification n hn k hk ki 0 1).mp ⟨row, eq.trans e.symm⟩
  norm_num at bad

/-- A single daughter mode has a rational row precisely when its
    coefficient of the obstruction polynomial vanishes. -/
theorem angular_mode_rational_iff (n m : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (even odd : ℂ[X]) :
    (∃ row : Row ℂᵣ, L[n,k] row = angularSource n m k even odd) ↔
      (angularObstruction (alternativeRatio k n) even odd).coeff m = 0 := by
  let c := (angularObstruction (alternativeRatio k n) even odd).coeff m
  let base := admittedCombination k n even odd m (admittedField false k n) (admittedField true k n)
  have baseImage :
      L[n,k] base =
        admittedCombination k n even odd m (admittedSource false k n) (admittedSource true k n) := by
    simp only [base, admittedCombination, operator_plus, operator_constant_scale, operator_minus,
      admitted_field_solves _ n hn k hk ki]
  have factor : angularSource n m k even odd = plus (L[n,k] base) (scale (Cᵣ c) (publishedOdd k n)) := by
    unfold angularSource
    rw [baseImage]
  constructor
  · rintro ⟨row, eq⟩
    change c = 0
    by_contra nonzero
    have rem : L[n,k] (minus row base) = scale (Cᵣ c) (publishedOdd k n) := by
      rw [operator_minus, eq, factor]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [plus, minus]
    apply pureOddHasNoRow n hn k hk ki
    refine ⟨scale (Cᵣ c⁻¹) (minus row base), ?_⟩
    rw [operator_constant_scale, rem, scale_scale, ← map_mul, inv_mul_cancel₀ nonzero, map_one]
    simp [scale]
  · intro eq
    refine ⟨base, ?_⟩
    change c = 0 at eq
    rw [factor, eq, map_zero]
    simp [plus, scale]

/-- Rational solvability of the entire top multiplet locks the two parity
    profiles to one common scalar mixture. Every resulting row is unique. -/
theorem angular_multiplet_rational_iff (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (even odd : ℂ[X]) :
    (∀ m : ℕ, ∃! row : Row ℂᵣ, L[n,k] row = angularSource n m k even odd) ↔
      odd = even ∨ odd = C (alternativeRatio k n)*even := by
  constructor
  · intro each
    have zero : angularObstruction (alternativeRatio k n) even odd = 0 := by
      ext m
      rw [coeff_zero]
      obtain ⟨row, eq, _⟩ := each m
      exact (angular_mode_rational_iff n m hn k hk ki even odd).mp ⟨row,eq⟩
    change (odd-even)*(odd-C (alternativeRatio k n)*even) = 0 at zero
    exact (mul_eq_zero.mp zero).imp sub_eq_zero.mp sub_eq_zero.mp
  · intro locked m
    have zero : angularObstruction (alternativeRatio k n) even odd = 0 := by
      rcases locked with h | h <;> simp [angularObstruction, h]
    have hm : (angularObstruction (alternativeRatio k n) even odd).coeff m = 0 := by
      rw [zero, coeff_zero]
    obtain ⟨row, eq⟩ := (angular_mode_rational_iff n m hn k hk ki even odd).mpr hm
    exact ⟨row,eq,fun v ev => rational_particular_row_unique n hn k hk ki v row (ev.trans eq.symm)⟩

theorem angular_multiplet_through_maximum_degree (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (even odd : ℂ[X]) (evenDegree : even.natDegree ≤ 2*n) (oddDegree : odd.natDegree ≤ 2*n) :
    (∀ m ≤ 4*n, ∃! row : Row ℂᵣ, L[n,k] row = angularSource n m k even odd) ↔
      odd = even ∨ odd = C (alternativeRatio k n)*even := by
  have all := angular_multiplet_rational_iff n hn k hk ki even odd
  constructor
  · intro finite
    apply all.mp
    intro m
    by_cases inside : m ≤ 4*n
    · exact finite m inside
    have a : (odd-even).natDegree ≤ 2*n :=
      (natDegree_sub_le _ _).trans (max_le oddDegree evenDegree)
    have b : (odd-C (alternativeRatio k n)*even).natDegree ≤ 2*n :=
      (natDegree_sub_le _ _).trans
        (max_le oddDegree ((natDegree_C_mul_le _ _).trans evenDegree))
    have degree : (angularObstruction (alternativeRatio k n) even odd).natDegree ≤ 4*n := by
      unfold angularObstruction
      exact natDegree_mul_le.trans (by omega)
    have hm := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt degree (lt_of_not_ge inside))
    obtain ⟨row, eq⟩ := (angular_mode_rational_iff n m hn k hk ki even odd).mpr hm
    exact ⟨row,eq,fun v ev => rational_particular_row_unique n hn k hk ki v row (ev.trans eq.symm)⟩
  · intro locked m _
    exact all.mpr locked m

/-- Two pure angular components using different admitted ratios produce
    the obstruction in the cross mode. -/
theorem different_ratios_cross_obstruction (rho a b : ℂ) (p q : ℕ) :
    angularObstruction rho (monomial p a + monomial q b)
        (monomial p a + C rho*monomial q b) =
      monomial (p+q) (-(rho-1)^2*a*b) := by
  have e : angularObstruction rho (monomial p a + monomial q b)
        (monomial p a + C rho*monomial q b) =
      C (-(rho-1)^2)*(monomial p a * monomial q b) := by
    unfold angularObstruction
    rw [map_neg, map_pow, map_sub, map_one]
    ring
  rw [e, monomial_mul_monomial, C_mul_monomial]
  congr 1
  ring

theorem different_ratios_cross_mode_has_no_rational_row (n p q : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let rho := alternativeRatio k n
    let even := monomial p a + monomial q b
    let odd := monomial p a + C rho*monomial q b
    ¬ ∃ row : Row ℂᵣ, L[n,k] row = angularSource n (p+q) k even odd := by
  dsimp only
  intro row
  have h := (angular_mode_rational_iff n (p+q) hn k hk ki _ _).mp row
  rw [different_ratios_cross_obstruction, coeff_monomial, if_pos rfl] at h
  have dr := sub_ne_zero.mpr (alternativeRatio_ne_one n hn k ki)
  exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 dr)) ha) hb) h

theorem angular_source_on_admitted_branch (n m : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (ki : k.re = 0) (second : Bool) (even : ℂ[X]) :
    angularSource n m k even (C (mixtureRatio second k n)*even) =
      scale (Cᵣ ((even^2).coeff m)) (admittedSource second k n) := by
  cases second with
  | false =>
      simp [mixtureRatio, angularSource, admittedCombination, angularObstruction, plus, scale]
  | true =>
      let rho := alternativeRatio k n
      have d : C ((rho-1)⁻¹)*even*(C rho*even-even) = even^2 := by
        calc
          _ = C ((rho-1)⁻¹)*C (rho-1)*even^2 := by rw [map_sub, map_one]; ring
          _ = _ := by
            rw [← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr (alternativeRatio_ne_one n hn k ki)), map_one, one_mul]
      change angularSource n m k even (C rho*even) =
        scale (Cᵣ ((even^2).coeff m)) (admittedSource true k n)
      unfold angularSource admittedCombination
      change plus
          (plus (scale (Cᵣ ((even^2).coeff m)) (admittedSource false k n))
            (scale (Cᵣ ((C ((rho-1)⁻¹)*even*(C rho*even-even)).coeff m))
              (minus (admittedSource true k n) (admittedSource false k n))))
          (scale (Cᵣ ((angularObstruction rho even (C rho*even)).coeff m)) (publishedOdd k n)) = _
      rw [d]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
        simp only [angularObstruction, sub_self, mul_zero, coeff_zero, map_zero, plus, minus, scale,
          zero_mul, add_zero] <;> ring

#print axioms angular_mode_rational_iff
#print axioms angular_source_from_three_rows
#print axioms angular_source_from_quadratic_coefficients
#print axioms angular_multiplet_rational_iff
#print axioms angular_multiplet_through_maximum_degree
#print axioms different_ratios_cross_obstruction
#print axioms different_ratios_cross_mode_has_no_rational_row
#print axioms angular_source_on_admitted_branch

end
end SchwarzschildMixtures
