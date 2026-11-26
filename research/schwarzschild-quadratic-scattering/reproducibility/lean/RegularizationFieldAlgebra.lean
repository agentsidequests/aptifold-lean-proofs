import RegularizationBridgeData
import MetricBareDenominator

/-! Lift the checked numerator identities to the physical rational fields.
The polynomial computations are independent of this field argument. -/
namespace SchwarzschildMixtures.Regularization

open Polynomial SchwarzschildLaurent NumeratorData

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private def evalScalar (k ell : ℂ) (p : Expr) : ℂᵣ := ι (Expr.value k ell p)
private def evalRow (k ell : ℂ) (p : ExprRow) : Row ℂᵣ := mapRow ι (rowValue k ell p)

private theorem value_mul (k ell : ℂ) (p q : Expr) :
    evalScalar k ell (.mul p q) = evalScalar k ell p*evalScalar k ell q := by
  simp [evalScalar]

private theorem value_sub (k ell : ℂ) (p q : Expr) :
    evalScalar k ell (Expr.sub p q) = evalScalar k ell p-evalScalar k ell q := by
  simp [evalScalar]

private theorem value_natural (k ell : ℂ) (m : ℕ) :
    evalScalar k ell (natural m) = (m : ℂᵣ) := by
  simp [evalScalar, natural, c, Expr.value_constant]

private theorem eval_add (k ell : ℂ) (p q : ExprRow) :
    evalRow k ell (addData p q) = plus (evalRow k ell p) (evalRow k ell q) := by
  simp [evalRow, addData, rowValue, mapRow, plus]

private theorem eval_scale (k ell : ℂ) (a : Expr) (p : ExprRow) :
    evalRow k ell (scaleData a p) = scale (evalScalar k ell a) (evalRow k ell p) := by
  simp [evalRow, scaleData, exprRowMap, evalScalar, rowValue, mapRow, scale]

private theorem checked (k ell : ℂ) (pair : ExprRow × ExprRow) (h : RowCheck pair) :
    evalRow k ell pair.1 = evalRow k ell pair.2 :=
  congrArg (mapRow ι) (checked_row_value k ell pair.1 pair.2 h.1 h.2.1 h.2.2)

private def commonDenominator (k ell : ℂ) : ℂᵣ :=
  ι (fieldDenominator (fieldScalar 1 false k ell) ell)

private theorem common_nonzero (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    commonDenominator k n ≠ 0 :=
  RatFunc.algebraMap_ne_zero
    (fieldDenominator_ne_zero _ (fieldScalar_ne_zero 1 n (by decide) hn false k hk ki) n hn)

private theorem second_factor_value (k ell : ℂ) :
    evalScalar k ell secondFactor = Cᵣ ((7*ell-1)^2) := by
  simp only [evalScalar, secondFactor, c, l, Expr.value_sub, Expr.value_mul,
    Expr.value_angular, Expr.value_constant, ← map_sub, ← map_mul,
    Int.cast_ofNat, Int.cast_one, RatFunc.algebraMap_C, pow_two]

private theorem local_field_common (k ell : ℂ) (p : ExprRow) (m : ℕ) (second : Bool) :
    localField p m second k ell =
      scale (((m : ℂᵣ)*(if second then evalScalar k ell secondFactor else 1)*
        commonDenominator k ell)⁻¹) (evalRow k ell p) := by
  let e := if second then (7*ell-1)^2 else (1:ℂ)
  have scalar : fieldScalar m second k ell = ((m:ℂ)*e)*fieldScalar 1 false k ell := by
    cases second <;> simp [e, fieldScalar] <;> ring
  have denominator : fieldDenominator (fieldScalar m second k ell) ell =
      C ((m:ℂ)*e)*fieldDenominator (fieldScalar 1 false k ell) ell := by
    rw [scalar]
    simp only [fieldDenominator, map_mul]
    ring
  have factor : Cᵣ e = if second then evalScalar k ell secondFactor else 1 := by
    cases second <;> simp [e, second_factor_value]
  simp only [localField, denominator, commonDenominator, evalRow, fractionRow, mapRow, scale,
    map_mul, RatFunc.algebraMap_C, map_natCast, factor, div_eq_mul_inv, mul_comm]

private theorem ratio_num_value (k ell : ℂ) :
    evalScalar k ell ratioNumerator = Cᵣ ((9*ell*ell+ell-4)*(12*(gamma ell-k))) := by
  simp only [evalScalar, ratioNumerator, gammaNumerator, c, l, w, Expr.value_sub, Expr.value_add,
    Expr.value_mul, Expr.value_frequency, Expr.value_angular, Expr.value_constant,
    Int.cast_ofNat, Int.cast_one, ← map_add, ← map_sub, ← map_mul, RatFunc.algebraMap_C]
  congr 1
  unfold gamma
  ring

private theorem ratio_den_value (k ell : ℂ) :
    evalScalar k ell ratioDenominator = Cᵣ (ell*(7*ell-1)*(12*(gamma ell+k))) := by
  simp only [evalScalar, ratioDenominator, gammaNumerator, c, l, w, Expr.value_sub, Expr.value_add,
    Expr.value_mul, Expr.value_frequency, Expr.value_angular, Expr.value_constant,
    Int.cast_ofNat, Int.cast_one, ← map_add, ← map_sub, ← map_mul, RatFunc.algebraMap_C]
  congr 1
  unfold gamma
  ring

private theorem ratio_values (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    evalScalar k n ratioDenominator ≠ 0 ∧ evalScalar k n secondFactor ≠ 0 ∧
    Cᵣ (alternativeRatio k n) = evalScalar k n ratioNumerator/evalScalar k n ratioDenominator := by
  let l : ℂ := n
  have hl : l ≠ 0 := by
    change (n : ℂ) ≠ 0
    exact_mod_cast (show n ≠ 0 by omega)
  have hp : l+1 ≠ 0 := by
    change (n : ℂ)+1 ≠ 0
    exact_mod_cast Nat.succ_ne_zero n
  have h7 : 7*l-1 ≠ 0 := by
    change 7*(n : ℂ)-1 ≠ 0
    exact sub_ne_zero.mpr (by exact_mod_cast (show 7*n ≠ 1 by omega))
  have hg : gamma l+k ≠ 0 := by
    intro h
    have nonzero := fieldScalar_ne_zero 1 n (by decide) hn true k hk ki
    change fieldScalar 1 true k l ≠ 0 at nonzero
    rw [add_comm] at h
    exact nonzero (by simp [fieldScalar, h])
  have gap : daughterGamma l - gamma l = l^2*(l+1)*(7*l-1)/12 := by
    unfold daughterGamma gamma
    ring
  have sum : daughterGamma l + gamma l = l*(l+1)*(9*l*l+l-4)/12 := by
    unfold daughterGamma gamma
    ring
  have hden : l*(7*l-1)*(12*(gamma l+k)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hl h7) (mul_ne_zero (by norm_num) hg)
  refine ⟨?_, ?_, ?_⟩
  · rw [ratio_den_value]
    exact (map_ne_zero Cᵣ).2 hden
  · rw [second_factor_value]
    exact (map_ne_zero Cᵣ).2 (pow_ne_zero _ h7)
  · rw [ratio_num_value, ratio_den_value, ← map_div₀]
    congr 1
    change alternativeRatio k l = (9*l*l+l-4)*(12*(gamma l-k))/(l*(7*l-1)*(12*(gamma l+k)))
    have hgap : daughterGamma l-gamma l ≠ 0 := by
      rw [gap]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl) hp) h7) (by norm_num)
    unfold alternativeRatio
    apply (div_eq_div_iff (mul_ne_zero hgap hg) hden).2
    rw [sum, gap]
    ring

private theorem base_coefficient {K : Type*} [Field K] (p b u q mp mb mu : K)
    (hq : q ≠ 0) (hp : mp ≠ 0) (hb : mb ≠ 0) (hu : mu ≠ 0)
    (h : mb*mu*p = mp*mu*b+mp*mb*u) :
    (mp*q)⁻¹*p = (mb*q)⁻¹*b+(mu*q)⁻¹*u := by
  let common := mp*mb*mu*q
  have common_ne : common ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hp hb) hu) hq
  apply mul_right_cancel₀ common_ne
  calc
    _ = mb*mu*p := by dsimp only [common]; field_simp [hp, hq]
    _ = mp*mu*b+mp*mb*u := h
    _ = _ := by dsimp only [common]; field_simp [hb, hu, hq]

private theorem second_coefficient {K : Type*} [Field K] (p first diff ee eo oo q b n d mp mf md mu : K)
    (hq : q ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hp : mp ≠ 0) (hf : mf ≠ 0) (hm : md ≠ 0) (hu : mu ≠ 0)
    (h : (mf*md*mu*(d*d))*p =
      (mp*md*mu*b*(d*d))*first +
      ((mp*mf*mu*(n-d)*d)*diff +
        (mp*mf*md*b)*((d*d)*ee+((n*d)*eo+(n*n)*oo)))) :
    (mp*b*q)⁻¹*p = (mf*q)⁻¹*first +
      ((n/d-1)*((md*b*q)⁻¹*diff) +
        ((mu*q)⁻¹*ee+((n/d)*((mu*q)⁻¹*eo)+(n/d)^2*((mu*q)⁻¹*oo)))) := by
  let common := mp*mf*md*mu*b*d*d*q
  have common_ne : common ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hp hf) hm) hu) hb) hd) hd) hq
  apply mul_right_cancel₀ common_ne
  calc
    _ = (mf*md*mu*(d*d))*p := by dsimp only [common]; field_simp [hp, hb, hq]
    _ = _ := h
    _ = _ := by dsimp only [common]; field_simp [hf, hm, hu, hb, hd, hq]

theorem compare_base_fields (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (published bare regulator : ExprRow) (mp mb mu : ℕ)
    (hp : 0 < mp) (hb : 0 < mb) (hu : 0 < mu)
    (certificate : RowCheck (baseComparison published bare regulator mp mb mu)) :
    localField published mp false k n =
      plus (localField bare mb false k n) (localField regulator mu false k n) := by
  have hq := common_nonzero n hn k hk ki
  have hp' : (mp : ℂᵣ) ≠ 0 := by exact_mod_cast hp.ne'
  have hb' : (mb : ℂᵣ) ≠ 0 := by exact_mod_cast hb.ne'
  have hu' : (mu : ℂᵣ) ≠ 0 := by exact_mod_cast hu.ne'
  have h := checked k n _ certificate
  simp only [baseComparison, eval_add, eval_scale, value_natural, Nat.cast_mul] at h
  simp only [local_field_common, Bool.false_eq_true, if_false, mul_one]
  exact Prod.ext
    (base_coefficient _ _ _ _ _ _ _ hq hp' hb' hu' (congrArg Prod.fst h))
    (Prod.ext
      (base_coefficient _ _ _ _ _ _ _ hq hp' hb' hu' (congrArg (fun r => r.2.1) h))
      (base_coefficient _ _ _ _ _ _ _ hq hp' hb' hu' (congrArg (fun r => r.2.2) h)))

theorem local_field_add (k ell : ℂ) (p q : ExprRow) (m : ℕ) :
    localField (addData p q) m false k ell =
      plus (localField p m false k ell) (localField q m false k ell) := by
  simp only [local_field_common, eval_add, Bool.false_eq_true, if_false, mul_one]
  exact scale_plus _ _ _

theorem compare_second_fields (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (published first difference ee eo oo : ExprRow) (mp mf md mu : ℕ)
    (hp : 0 < mp) (hf : 0 < mf) (hm : 0 < md) (hu : 0 < mu)
    (certificate : RowCheck (secondComparison published first difference ee eo oo mp mf md mu)) :
    let rho := Cᵣ (alternativeRatio k n)
    localField published mp true k n =
      plus (localField first mf false k n)
        (plus (scale (rho-1) (localField difference md true k n))
          (plus (localField ee mu false k n)
            (plus (scale rho (localField eo mu false k n)) (scale (rho^2) (localField oo mu false k n))))) := by
  obtain ⟨hd,hb,rho⟩ := ratio_values n hn k hk ki
  have hq := common_nonzero n hn k hk ki
  have hp' : (mp : ℂᵣ) ≠ 0 := by exact_mod_cast hp.ne'
  have hf' : (mf : ℂᵣ) ≠ 0 := by exact_mod_cast hf.ne'
  have hm' : (md : ℂᵣ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu' : (mu : ℂᵣ) ≠ 0 := by exact_mod_cast hu.ne'
  have h := checked k n _ certificate
  simp only [secondComparison, eval_add, eval_scale, value_mul, value_sub, value_natural,
    Nat.cast_mul] at h
  dsimp only
  simp only [rho, local_field_common, Bool.false_eq_true, if_false, if_true, mul_one]
  exact Prod.ext
    (second_coefficient _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hb hd hp' hf' hm' hu' (congrArg Prod.fst h))
    (Prod.ext
      (second_coefficient _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hb hd hp' hf' hm' hu' (congrArg (fun r => r.2.1) h))
      (second_coefficient _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hb hd hp' hf' hm' hu' (congrArg (fun r => r.2.2) h)))

#print axioms compare_base_fields
#print axioms local_field_add
#print axioms compare_second_fields

end
end SchwarzschildMixtures.Regularization
