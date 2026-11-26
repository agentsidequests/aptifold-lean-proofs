import LaurentInfinityBounds
import Mathlib.Algebra.Polynomial.Reverse

namespace SchwarzschildLaurent

open Polynomial
open scoped BigOperators

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

theorem normalized_denominator (u : ℂᵣ) (a : ℂ) :
    ∃ q : ℂ[X], u.denom = localCoordinate a ^ rootMultiplicity a u.denom * q ∧
      q.eval a ≠ 0 ∧ (0 < rootMultiplicity a u.denom → u.num.eval a ≠ 0) := by
  let m := rootMultiplicity a u.denom
  obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd u.denom a
  change u.denom = localCoordinate a ^ m * q at hq
  refine ⟨q, hq, ?_, ?_⟩
  · intro hzero
    obtain ⟨s, hs⟩ := dvd_iff_isRoot.mpr (show IsRoot q a from hzero)
    change q = localCoordinate a * s at hs
    have hdvd : (X-C a) ^ (m+1) ∣ u.denom := by
      change localCoordinate a ^ (m+1) ∣ u.denom
      exact ⟨s, by rw [hq, hs, pow_succ, mul_assoc]⟩
    have hle := (le_rootMultiplicity_iff u.denom_ne_zero).mpr hdvd
    change m + 1 ≤ m at hle
    omega
  · intro hm hn
    have hm0 : m ≠ 0 := Nat.ne_of_gt hm
    have hz : u.denom.eval a = 0 := by simp [hq, localCoordinate, hm0]
    obtain ⟨p,q,hcop⟩ := u.isCoprime_num_denom
    have he := congrArg (Polynomial.eval a) hcop
    simp [hn, hz] at he

/-- A pole order at a is the largest denominator multiplicity among the three
components. A component attaining a nonzero maximum has a nonzero leading coefficient. -/
noncomputable def poleOrder (u : Row ℂᵣ) (a : ℂ) : ℕ :=
  max (rootMultiplicity a u.1.denom) (max (rootMultiplicity a u.2.1.denom)
    (rootMultiplicity a u.2.2.denom))

noncomputable def fractionRow (p : Row ℂ[X]) (q : ℂ[X]) : Row ℂᵣ :=
  (ι p.1 / ι q, ι p.2.1 / ι q, ι p.2.2 / ι q)

private theorem fraction_enlarge (t p q r : ℂ[X]) (ht : t ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (m n : ℕ) (hm : n ≤ m) :
    ι (p * t^(m-n) * r) / ι (t^m * (q*r)) = ι p / ι (t^n * q) := by
  have hpow : t^(m-n)*t^n = t^m := by rw [← pow_add, Nat.sub_add_cancel hm]
  apply (div_eq_div_iff (RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ ht) (mul_ne_zero hq hr)))
    (RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ ht) hq))).2
  simp_rw [← map_mul]
  apply congrArg ι
  calc
    _ = p * (t^(m-n)*t^n) * q * r := by ring
    _ = _ := by rw [hpow]; ring

/-- Every rational row admits a common normalized fraction at each finite point. -/
theorem normalize_at_finite_point (u : Row ℂᵣ) (a : ℂ) :
    ∃ q : ℂ[X], ∃ p : Row ℂ[X], q.eval a ≠ 0 ∧
      u = fractionRow p (localCoordinate a ^ poleOrder u a * q) ∧
      (0 < poleOrder u a → rowEval a p ≠ 0) := by
  let t := localCoordinate a
  let n₀ := rootMultiplicity a u.1.denom
  let n₁ := rootMultiplicity a u.2.1.denom
  let n₂ := rootMultiplicity a u.2.2.denom
  let m := poleOrder u a
  have hm : m = max n₀ (max n₁ n₂) := rfl
  have h₀ : n₀ ≤ m := by omega
  have h₁ : n₁ ≤ m := by omega
  have h₂ : n₂ ≤ m := by omega
  obtain ⟨q₀, hd₀, hq₀, hp₀⟩ := normalized_denominator u.1 a
  obtain ⟨q₁, hd₁, hq₁, hp₁⟩ := normalized_denominator u.2.1 a
  obtain ⟨q₂, hd₂, hq₂, hp₂⟩ := normalized_denominator u.2.2 a
  have v₀ : q₀ ≠ 0 := fun h => hq₀ (by simp [h])
  have v₁ : q₁ ≠ 0 := fun h => hq₁ (by simp [h])
  have v₂ : q₂ ≠ 0 := fun h => hq₂ (by simp [h])
  let q := q₀*(q₁*q₂)
  let p₀ := u.1.num * t^(m-n₀) * (q₁*q₂)
  let p₁ := u.2.1.num * t^(m-n₁) * (q₀*q₂)
  let p₂ := u.2.2.num * t^(m-n₂) * (q₀*q₁)
  exact ⟨q, (p₀,p₁,p₂),
    by simpa [q, eval_mul] using mul_ne_zero hq₀ (mul_ne_zero hq₁ hq₂),
    by
      apply Prod.ext
      · change u.1 = ι p₀ / ι (t^m*q)
        exact (RatFunc.num_div_denom u.1).symm.trans
          (by rw [hd₀]; exact (fraction_enlarge t _ q₀ (q₁*q₂) (localCoordinate_ne_zero a) v₀
              (mul_ne_zero v₁ v₂) m n₀ h₀).symm)
      · apply Prod.ext
        · change u.2.1 = ι p₁ / ι (t^m*q)
          have hq : q = q₁*(q₀*q₂) := by dsimp [q]; ring
          rw [hq]
          exact (RatFunc.num_div_denom u.2.1).symm.trans
            (by rw [hd₁]; exact (fraction_enlarge t _ q₁ (q₀*q₂) (localCoordinate_ne_zero a) v₁
                (mul_ne_zero v₀ v₂) m n₁ h₁).symm)
        · change u.2.2 = ι p₂ / ι (t^m*q)
          have hq : q = q₂*(q₀*q₁) := by dsimp [q]; ring
          rw [hq]
          exact (RatFunc.num_div_denom u.2.2).symm.trans
            (by rw [hd₂]; exact (fraction_enlarge t _ q₂ (q₀*q₁) (localCoordinate_ne_zero a) v₂
                (mul_ne_zero v₀ v₁) m n₂ h₂).symm),
    by
      intro hmpos hzero
      change 0 < m at hmpos
      have attain : m = n₀ ∨ m = n₁ ∨ m = n₂ := by omega
      rcases attain with r | r | r
      · have hz : p₀.eval a = 0 := congrArg (fun u : Row ℂ => u.1) hzero
        have hne : p₀.eval a ≠ 0 := by
          simpa [p₀, r, eval_mul] using
            mul_ne_zero (hp₀ (by change 0 < n₀; omega)) (mul_ne_zero hq₁ hq₂)
        exact hne hz
      · have hz : p₁.eval a = 0 := congrArg (fun u : Row ℂ => u.2.1) hzero
        have hne : p₁.eval a ≠ 0 := by
          simpa [p₁, r, eval_mul] using
            mul_ne_zero (hp₁ (by change 0 < n₁; omega)) (mul_ne_zero hq₀ hq₂)
        exact hne hz
      · have hz : p₂.eval a = 0 := congrArg (fun u : Row ℂ => u.2.2) hzero
        have hne : p₂.eval a ≠ 0 := by
          simpa [p₂, r, eval_mul] using
            mul_ne_zero (hp₂ (by change 0 < n₂; omega)) (mul_ne_zero hq₀ hq₁)
        exact hne hz⟩

/-- The local source identities needed for the finite part of Appendix A.
Each identity concerns a normalized candidate and follows algebraically when
the appropriately cleared source vanishes at that point. -/
structure FiniteSourceEquations (h hD k : ℂ) (u : Row ℂᵣ) : Prop where
  ordinary : ∀ (a : ℂ) (q : ℂ[X]) (p : Row ℂ[X]), a ≠ 0 → a ≠ 2 → 0 < poleOrder u a →
    q.eval a ≠ 0 → u = fractionRow p (localCoordinate a ^ poleOrder u a * q) →
    rowEval a (ordinaryResidual h hD k a (poleOrder u a) q p) = 0
  horizon : ∀ (q : ℂ[X]) (p : Row ℂ[X]), 0 < poleOrder u 2 →
    q.eval 2 ≠ 0 → u = fractionRow p (localCoordinate 2 ^ poleOrder u 2 * q) →
    rowEval 2 (horizonResidual h hD k (poleOrder u 2) q p) = 0
  origin : ∀ (q : ℂ[X]) (p : Row ℂ[X]), 7 < poleOrder u 0 →
    q.eval 0 ≠ 0 → u = fractionRow p (localCoordinate 0 ^ poleOrder u 0 * q) →
    rowEval 0 (originResidual h hD k (poleOrder u 0) q p) = 0

/-- These identities exclude all nonzero finite poles and cap the order at zero. -/
theorem finite_pole_bounds (h hD k : ℂ) (hk : k ≠ 0) (hi : k.re = 0)
    (u : Row ℂᵣ) (eqs : FiniteSourceEquations h hD k u) :
    (∀ a : ℂ, a ≠ 0 → poleOrder u a = 0) ∧ poleOrder u 0 ≤ 7 := by
  constructor
  · intro a ha
    by_contra hnon
    have hm : 0 < poleOrder u a := Nat.pos_of_ne_zero hnon
    by_cases h₂ : a = 2
    · subst a
      obtain ⟨q, p, hq, hp, hlead⟩ := normalize_at_finite_point u 2
      exact hlead hm (horizon_bound_from_residual h hD k hk hi _ hm q p hq
        (eqs.horizon q p hm hq hp))
    · obtain ⟨q, p, hq, hp, hlead⟩ := normalize_at_finite_point u a
      exact hlead hm (ordinary_bound_from_residual h hD k a _ hm ha h₂ q p hq
        (eqs.ordinary a q p ha h₂ hm hq hp))
  · by_contra hnot
    have hm : 7 < poleOrder u 0 := by omega
    obtain ⟨q, p, hq, hp, hlead⟩ := normalize_at_finite_point u 0
    have hpos : 0 < poleOrder u 0 := by omega
    have hmax := origin_bound_from_residual h hD k _ q p hq (hlead hpos)
      (eqs.origin q p hm hq hp) hpos
    omega

def LaurentEnvelope (d : ℕ) (u : ℂᵣ) : Prop :=
  (∀ a : ℂ, a ≠ 0 → u.denom.eval a ≠ 0) ∧
    u.denom.natDegree ≤ 7 ∧ u.num.natDegree ≤ u.denom.natDegree + d

noncomputable def laurentSpan (count : ℕ) (coeff : ℕ → ℂ) : ℂᵣ :=
  ∑ i ∈ Finset.range count, RatFunc.C (coeff i) * (RatFunc.X : ℂᵣ)^((i : ℤ)-7)

/-- Exact spans of all three bounded components in the rescaled matrix basis. -/
theorem matrix_basis_span (u : Row ℂᵣ) (h₀ : LaurentEnvelope 4 u.1)
    (h₁ : LaurentEnvelope 2 u.2.1) (h₂ : LaurentEnvelope 0 u.2.2) :
    ∃ coeff : Row (ℕ → ℂ),
      u = (laurentSpan 12 coeff.1, laurentSpan 10 coeff.2.1, laurentSpan 8 coeff.2.2) := by
  obtain ⟨a, ha⟩ := bounded_laurent_expansion u.1 4 h₀.1 h₀.2.1 h₀.2.2
  obtain ⟨b, hb⟩ := bounded_laurent_expansion u.2.1 2 h₁.1 h₁.2.1 h₁.2.2
  obtain ⟨c, hc⟩ := bounded_laurent_expansion u.2.2 0 h₂.1 h₂.2.1 h₂.2.2
  exact ⟨(a,b,c), Prod.ext ha (Prod.ext hb hc)⟩

private theorem bounds_from_multiplicities (u : ℂᵣ)
    (none : ∀ a : ℂ, a ≠ 0 → rootMultiplicity a u.denom = 0)
    (atOrigin : rootMultiplicity 0 u.denom ≤ 7) :
    (∀ a : ℂ, a ≠ 0 → u.denom.eval a ≠ 0) ∧ u.denom.natDegree ≤ 7 := by
  have hfinite : ∀ a : ℂ, a ≠ 0 → u.denom.eval a ≠ 0 := by
    intro a ha hr
    have hpositive := (rootMultiplicity_pos u.denom_ne_zero).mpr (show IsRoot u.denom a from hr)
    rw [none a ha] at hpositive
    omega
  refine ⟨hfinite, ?_⟩
  have hdvd : (X-C (0 : ℂ)) ^ u.denom.natDegree ∣ u.denom := by
    simp only [C_0, sub_zero]
    rw [← denominator_power u hfinite]
  exact ((le_rootMultiplicity_iff u.denom_ne_zero).mpr hdvd).trans atOrigin

private theorem unscale_degree_bound (u : ℂᵣ) (d n : ℕ) (hn : n ≤ d)
    (bound : (u * (RatFunc.X : ℂᵣ)^n).num.natDegree ≤
      (u * (RatFunc.X : ℂᵣ)^n).denom.natDegree+d) :
    u.num.natDegree ≤ u.denom.natDegree+(d-n) := by
  by_cases h : u = 0
  · simp [h]
  · let v : ℂᵣ := u * (RatFunc.X : ℂᵣ)^n
    have hv : v ≠ 0 := mul_ne_zero h (pow_ne_zero _ RatFunc.X_ne_zero)
    have hvform : v = ι (u.num * X^n) / ι u.denom := by
      calc
        v = (ι u.num / ι u.denom) * (RatFunc.X : ℂᵣ)^n := by rw [RatFunc.num_div_denom]
        _ = _ := by simp only [map_mul, map_pow, RatFunc.algebraMap_X, div_eq_mul_inv]; ring
    have hp := (RatFunc.num_mul_eq_mul_denom_iff u.denom_ne_zero).mpr hvform
    have hdeg := congrArg natDegree hp
    rw [natDegree_mul (RatFunc.num_ne_zero hv) u.denom_ne_zero,
      natDegree_mul (mul_ne_zero (RatFunc.num_ne_zero h) (pow_ne_zero _ Polynomial.X_ne_zero))
        v.denom_ne_zero,
      natDegree_mul (RatFunc.num_ne_zero h) (pow_ne_zero _ Polynomial.X_ne_zero),
      natDegree_X_pow] at hdeg
    change v.num.natDegree ≤ v.denom.natDegree + d at bound
    omega

/-- Given the normalized finite source identities and the growth bound in the
unscaled basis, the rational row belongs to the exact matrix span. -/
theorem matrix_span_from_source_bounds (h hD k : ℂ) (hk : k ≠ 0) (hi : k.re = 0)
    (u : Row ℂᵣ) (eqs : FiniteSourceEquations h hD k u)
    (ha : u.1.num.natDegree ≤ u.1.denom.natDegree+4)
    (hb : (u.2.1 * (RatFunc.X : ℂᵣ)^2).num.natDegree ≤
      (u.2.1 * (RatFunc.X : ℂᵣ)^2).denom.natDegree+4)
    (hc : (u.2.2 * (RatFunc.X : ℂᵣ)^4).num.natDegree ≤
      (u.2.2 * (RatFunc.X : ℂᵣ)^4).denom.natDegree+4) :
    ∃ coeff : Row (ℕ → ℂ),
      u = (laurentSpan 12 coeff.1, laurentSpan 10 coeff.2.1, laurentSpan 8 coeff.2.2) := by
  obtain ⟨finite, origin⟩ := finite_pole_bounds h hD k hk hi u eqs
  unfold poleOrder at finite origin
  have h₀ := bounds_from_multiplicities u.1 (by intro a ha; have hh := finite a ha; omega)
    (by omega)
  have h₁ := bounds_from_multiplicities u.2.1 (by intro a ha; have hh := finite a ha; omega)
    (by omega)
  have h₂ := bounds_from_multiplicities u.2.2 (by intro a ha; have hh := finite a ha; omega)
    (by omega)
  exact matrix_basis_span u ⟨h₀.1,h₀.2,ha⟩
    ⟨h₁.1,h₁.2,unscale_degree_bound u.2.1 4 2 (by decide) hb⟩
    ⟨h₂.1,h₂.2,unscale_degree_bound u.2.2 4 4 (by decide) hc⟩

/-- Substitute the reciprocal radius into a complex rational function. -/
noncomputable def reciprocal (u : ℂᵣ) : ℂᵣ :=
  RatFunc.eval (algebraMap ℂ ℂᵣ) (RatFunc.X : ℂᵣ)⁻¹ u

theorem polynomial_reciprocal (p : ℂ[X]) :
    p.eval₂ (algebraMap ℂ ℂᵣ) (RatFunc.X : ℂᵣ)⁻¹ = ι p.reverse / (RatFunc.X : ℂᵣ)^p.natDegree := by
  letI := invertibleOfNonzero (inv_ne_zero RatFunc.X_ne_zero : (RatFunc.X : ℂᵣ)⁻¹ ≠ 0)
  have h := eval₂_reverse_mul_pow (algebraMap ℂ ℂᵣ) (RatFunc.X : ℂᵣ)⁻¹ p
  have hs : ⅟((RatFunc.X : ℂᵣ)⁻¹) = RatFunc.X := by rw [invOf_eq_inv, inv_inv]
  have he : p.reverse.eval₂ (algebraMap ℂ ℂᵣ) RatFunc.X = ι p.reverse := by
    exact eval₂_algebraMap_X p.reverse (IsScalarTower.toAlgHom ℂ ℂ[X] ℂᵣ)
  rw [hs, he] at h
  simpa [div_eq_mul_inv, inv_pow] using h.symm

private theorem reverse_denom_nonzero (u : ℂᵣ) : u.denom.reverse ≠ 0 :=
  fun h => u.denom_ne_zero (reverse_eq_zero.mp h)

private theorem reciprocal_formula (u : ℂᵣ) :
    reciprocal u = ι (u.num.reverse * X^u.denom.natDegree) /
      ι (X^u.num.natDegree * u.denom.reverse) := by
  rw [reciprocal, RatFunc.eval, polynomial_reciprocal, polynomial_reciprocal]
  simp only [map_mul, map_pow, RatFunc.algebraMap_X]
  field_simp [RatFunc.X_ne_zero, RatFunc.algebraMap_ne_zero (reverse_denom_nonzero u)]

noncomputable def componentGrowth (u : ℂᵣ) : ℕ :=
  u.num.natDegree - u.denom.natDegree

noncomputable def growth (u : Row ℂᵣ) : ℕ :=
  max (componentGrowth u.1) (max (componentGrowth u.2.1) (componentGrowth u.2.2))

noncomputable def reciprocalRow (u : Row ℂᵣ) : Row ℂᵣ :=
  (reciprocal u.1, reciprocal u.2.1, reciprocal u.2.2)

private noncomputable def reversedNumerator (u : ℂᵣ) (d : ℕ) (q : ℂ[X]) : ℂ[X] :=
  u.num.reverse * X^(d+u.denom.natDegree-u.num.natDegree) * q

private theorem reverse_denom_eval_ne_zero (u : ℂᵣ) : u.denom.reverse.eval 0 ≠ 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
  exact leadingCoeff_ne_zero.mpr u.denom_ne_zero

private theorem reciprocal_common_fraction (u : ℂᵣ) (d : ℕ) (h : componentGrowth u ≤ d)
    (q : ℂ[X]) (hq : q ≠ 0) :
    reciprocal u = ι (reversedNumerator u d q) / ι (X^d*(u.denom.reverse*q)) := by
  have den := reverse_denom_nonzero u
  have hpow : (X : ℂ[X])^(d+u.denom.natDegree-u.num.natDegree) * X^u.num.natDegree =
      X^d * X^u.denom.natDegree := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel (by unfold componentGrowth at h; omega)]
  rw [reciprocal_formula, reversedNumerator]
  apply (div_eq_div_iff
    (RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) den))
    (RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (mul_ne_zero den hq)))).2
  simp_rw [← map_mul]
  apply congrArg ι
  linear_combination (-u.num.reverse * q * u.denom.reverse) * hpow

private theorem reversedNumerator_eval_ne_zero (u : ℂᵣ) (d : ℕ) (hd : 0 < d)
    (he : d = componentGrowth u) (q : ℂ[X]) (hq : q.eval 0 ≠ 0) :
    (reversedNumerator u d q).eval 0 ≠ 0 := by
  unfold componentGrowth at he
  have hpow : d+u.denom.natDegree-u.num.natDegree=0 := by omega
  have hu : u.num ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at he
    omega
  simp only [reversedNumerator, hpow, pow_zero, mul_one, eval_mul]
  apply mul_ne_zero _ hq
  rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
  exact leadingCoeff_ne_zero.mpr hu

/-- Every rational row has a normalized representative at reciprocal radius zero. -/
theorem normalize_at_infinity (u : Row ℂᵣ) :
    ∃ q : ℂ[X], ∃ p : Row ℂ[X], q.eval 0 ≠ 0 ∧
      reciprocalRow u = fractionRow p (X^growth u*q) ∧
      (0 < growth u → rowEval 0 p ≠ 0) := by
  let d := growth u
  have hdmax : d = max (componentGrowth u.1) (max (componentGrowth u.2.1)
      (componentGrowth u.2.2)) := rfl
  let q₀ := u.1.denom.reverse
  let q₁ := u.2.1.denom.reverse
  let q₂ := u.2.2.denom.reverse
  have hq₀ : q₀.eval 0 ≠ 0 := reverse_denom_eval_ne_zero u.1
  have hq₁ : q₁.eval 0 ≠ 0 := reverse_denom_eval_ne_zero u.2.1
  have hq₂ : q₂.eval 0 ≠ 0 := reverse_denom_eval_ne_zero u.2.2
  have v₀ : q₀ ≠ 0 := reverse_denom_nonzero u.1
  have v₁ : q₁ ≠ 0 := reverse_denom_nonzero u.2.1
  have v₂ : q₂ ≠ 0 := reverse_denom_nonzero u.2.2
  let q := q₀*(q₁*q₂)
  let p₀ := reversedNumerator u.1 d (q₁*q₂)
  let p₁ := reversedNumerator u.2.1 d (q₀*q₂)
  let p₂ := reversedNumerator u.2.2 d (q₀*q₁)
  refine ⟨q, (p₀,p₁,p₂), ?_, ?_, ?_⟩
  · simpa [q, eval_mul] using mul_ne_zero hq₀ (mul_ne_zero hq₁ hq₂)
  · apply Prod.ext
    · exact reciprocal_common_fraction u.1 d (by omega) (q₁*q₂) (mul_ne_zero v₁ v₂)
    · apply Prod.ext
      · change reciprocal u.2.1 = ι p₁ / ι (X^d*q)
        rw [show q = q₁*(q₀*q₂) by dsimp [q]; ring]
        exact reciprocal_common_fraction u.2.1 d (by omega) (q₀*q₂) (mul_ne_zero v₀ v₂)
      · change reciprocal u.2.2 = ι p₂ / ι (X^d*q)
        rw [show q = q₂*(q₀*q₁) by dsimp [q]; ring]
        exact reciprocal_common_fraction u.2.2 d (by omega) (q₀*q₁) (mul_ne_zero v₀ v₁)
  · intro hd hz
    change 0 < d at hd
    have attain : d = componentGrowth u.1 ∨ d = componentGrowth u.2.1 ∨
        d = componentGrowth u.2.2 := by omega
    rcases attain with he | he | he
    · exact reversedNumerator_eval_ne_zero u.1 d hd he _ (by simpa [eval_mul] using mul_ne_zero hq₁ hq₂)
        (congrArg (fun r : Row ℂ => r.1) hz)
    · exact reversedNumerator_eval_ne_zero u.2.1 d hd he _ (by simpa [eval_mul] using mul_ne_zero hq₀ hq₂)
        (congrArg (fun r : Row ℂ => r.2.1) hz)
    · exact reversedNumerator_eval_ne_zero u.2.2 d hd he _ (by simpa [eval_mul] using mul_ne_zero hq₀ hq₁)
        (congrArg (fun r : Row ℂ => r.2.2) hz)

noncomputable def unscaledRow (u : Row ℂᵣ) : Row ℂᵣ :=
  (u.1, u.2.1 * (RatFunc.X : ℂᵣ)^2, u.2.2 * (RatFunc.X : ℂᵣ)^4)

/-- The normalized source constraint at infinity for degrees above four. -/
def InfinitySourceEquation (h hD k : ℂ) (u : Row ℂᵣ) : Prop :=
  let v := unscaledRow u
  let d := growth v
  ∀ (q : ℂ[X]) (p : Row ℂ[X]), q.eval 0 ≠ 0 →
    reciprocalRow v = fractionRow p (X^d*q) → 4 < d →
    ∃ rest : Row ℂ[X], infinityResidual h hD k d q p = scale (X^2) rest

/-- The normalized source equations force every rational row into the 30-column span. -/
theorem matrix_span_from_normalized_equations (h hD k : ℂ) (hk : k ≠ 0) (hi : k.re = 0)
    (u : Row ℂᵣ) (finite : FiniteSourceEquations h hD k u)
    (infinity : InfinitySourceEquation h hD k u) :
    ∃ coeff : Row (ℕ → ℂ),
      u = (laurentSpan 12 coeff.1, laurentSpan 10 coeff.2.1, laurentSpan 8 coeff.2.2) := by
  let v := unscaledRow u
  obtain ⟨q, p, hq, hrep, hlead⟩ := normalize_at_infinity v
  have hd : growth v ≤ 4 := by
    by_contra h
    have hp : 0 < growth v := by omega
    exact h (infinity_degree_bound _ _ k hk _ q hq p (hlead hp) (infinity q p hq hrep))
  simp only [growth, componentGrowth, v, unscaledRow, Prod.fst, Prod.snd] at hd
  exact matrix_span_from_source_bounds h hD k hk hi u finite (by omega) (by omega) (by omega)

#print axioms normalize_at_finite_point
#print axioms finite_pole_bounds
#print axioms matrix_basis_span
#print axioms normalize_at_infinity
#print axioms matrix_span_from_normalized_equations

end SchwarzschildLaurent
