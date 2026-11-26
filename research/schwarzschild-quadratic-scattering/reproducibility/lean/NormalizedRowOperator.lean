import ReciprocalOperator

/-! The normalized numerator equations follow from the rational row operator. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative

theorem fractionRow_plus (p s : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (plus p s) q = plus (fractionRow p q) (fractionRow s q) := by
  simp [fractionRow, plus, add_div]

theorem fractionRow_minus (p s : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (minus p s) q = minus (fractionRow p q) (fractionRow s q) := by
  simp [fractionRow, minus, sub_div]

theorem fractionRow_scale (a : ℂ[X]) (p : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (scale a p) q = scale (ι a) (fractionRow p q) := by
  simp [fractionRow, scale, mul_div_assoc]

theorem fractionRow_jet (a b c : ℂ[X]) (p : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (jet a b c p) q = jet (ι a) (ι b) (ι c) (fractionRow p q) := by
  simp [fractionRow, jet, add_div, mul_div_assoc, map_ofNat]

theorem fractionRow_cancel (a : ℂ[X]) (ha : a ≠ 0) (p : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (scale a p) (a*q) = fractionRow p q := by
  simp [fractionRow, scale, mul_div_mul_left _ _ (RatFunc.algebraMap_ne_zero ha)]

theorem fractionRow_cross (p s : Row ℂ[X]) (q d : ℂ[X]) (hq : q ≠ 0) (hd : d ≠ 0)
    (eq : fractionRow p q = fractionRow s d) : scale d p = scale q s := by
  have cross (a b : ℂ[X]) (hab : ι a / ι q = ι b / ι d) : d * a = q * b := by
    apply RatFunc.algebraMap_injective ℂ
    simp only [map_mul, mul_comm (ι d), mul_comm (ι q)]
    exact (div_eq_div_iff (RatFunc.algebraMap_ne_zero hq) (RatFunc.algebraMap_ne_zero hd)).mp hab
  apply Prod.ext
  · exact cross p.1 s.1 (congrArg Prod.fst eq)
  · apply Prod.ext
    · exact cross p.2.1 s.2.1 (congrArg (fun v => v.2.1) eq)
    · exact cross p.2.2 s.2.2 (congrArg (fun v => v.2.2) eq)

@[simp] theorem localCoordinate_zero : localCoordinate 0 = (X : ℂ[X]) := by simp [localCoordinate]

private theorem derivative_localCoordinate (a : ℂ) : δ (ι (localCoordinate a)) = 1 := by
  rw [rationalDerivative_algebraMap]
  simp [localCoordinate]

theorem euler_twice_minus (a : ℂ) (u : Row ℂᵣ) :
    minus (localEulerRow a (localEulerRow a u)) (localEulerRow a u) =
      scale (ι (localCoordinate a)^2) (rationalRowDerivative (rationalRowDerivative u)) := by
  simp [localEulerRow, euler, mapRow, rationalRowDerivative, scale, minus, rationalDerivative_mul,
    derivative_localCoordinate, pow_two, mul_add, mul_assoc]

theorem eulerRow_fraction (a : ℂ) (m : ℕ) (p : Row ℂ[X]) (q : ℂ[X]) (hq : q ≠ 0) :
    localEulerRow a (fractionRow p (localCoordinate a^m*q)) =
      fractionRow (rowEuler a m q p) (localCoordinate a^m*q^2) := by
  apply Prod.ext
  · exact euler_fraction a m p.1 q hq
  · exact Prod.ext (euler_fraction a m p.2.1 q hq) (euler_fraction a m p.2.2 q hq)

private theorem pad_fraction (t : ℂ[X]) (m : ℕ) (s s' : ℂ[X]) (hs' : s' ≠ 0)
    (p : Row ℂ[X]) :
    fractionRow (scale s' p) (t^m*(s*s')) = fractionRow p (t^m*s) := by
  rw [show t^m*(s*s') = s'*(t^m*s) by ring, fractionRow_cancel _ hs']

theorem eulerResidual_correct (a : ℂ) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0)
    (p : Row ℂ[X]) (α : ℂ[X]) (β γ : Row ℂ[X] → Row ℂ[X]) (βr γr : Row ℂᵣ → Row ℂᵣ)
    (hβ : ∀ v d, fractionRow (β v) d = βr (fractionRow v d))
    (hγ : ∀ v d, fractionRow (γ v) d = γr (fractionRow v d)) :
    let u := fractionRow p (localCoordinate a^m*q)
    fractionRow (eulerResidual a m q p α β γ) (localCoordinate a^m*q^4) =
      plus (scale (ι α) (minus (localEulerRow a (localEulerRow a u)) (localEulerRow a u)))
        (plus (βr (localEulerRow a u)) (γr u)) := by
  have padFirst : fractionRow (scale (q^2) (rowEuler a m q p)) (localCoordinate a^m*q^4)
      = localEulerRow a (fractionRow p (localCoordinate a^m*q)) := by
    rw [eulerRow_fraction _ _ _ _ hq, show q^4 = q^2*q^2 by ring]
    exact pad_fraction _ _ _ _ (pow_ne_zero 2 hq) _
  have padZero : fractionRow (scale (q^3) p) (localCoordinate a^m*q^4)
      = fractionRow p (localCoordinate a^m*q) := by
    rw [show q^4 = q*q^3 by ring]
    exact pad_fraction _ _ _ _ (pow_ne_zero 3 hq) _
  have second := eulerRow_fraction a m (rowEuler a m q p) (q^2) (pow_ne_zero 2 hq)
  rw [← pow_mul, show 2*2=4 by decide, ← eulerRow_fraction a m p q hq] at second
  dsimp only
  rw [eulerResidual, fractionRow_plus, fractionRow_scale, fractionRow_minus, fractionRow_plus,
    hβ, hγ, padFirst, padZero, ← second]

private theorem fractionRow_first (h k : ℂ) (p : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (firstCoefficient h k p) q = firstRationalCoefficient h k (fractionRow p q) := by
  simp only [firstCoefficient, firstRationalCoefficient, jetNumerator, fractionRow_scale,
    fractionRow_plus, fractionRow_jet, shiftedRadius, map_one, map_mul, map_sub,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat]

private theorem fractionRow_zeroCoeff (h hD k : ℂ) (p : Row ℂ[X]) (q : ℂ[X]) :
    fractionRow (zeroCoefficient h hD k p) q = zeroRationalCoefficient h hD k (fractionRow p q) := by
  simp only [zeroCoefficient, zeroRationalCoefficient, daughterNumerator, jetNumerator,
    jetNumeratorDerivative, fractionRow_plus, fractionRow_minus, fractionRow_scale, fractionRow_jet,
    map_one, map_zero, shiftedRadius, map_sub, map_ofNat, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

theorem ordinaryResidual_correct (h hD k a : ℂ) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0)
    (p : Row ℂ[X]) :
    fractionRow (ordinaryResidual h hD k a m q p) (localCoordinate a^m*q^4) =
      scale (ι (localCoordinate a)^2 * R^4)
        (rationalOperator h hD k (fractionRow p (localCoordinate a^m*q))) := by
  rw [ordinaryResidual, eulerResidual_correct
    (βr := fun u => scale (ι (localCoordinate a)) (firstRationalCoefficient h k u))
    (γr := fun u => scale (ι (localCoordinate a)^2) (zeroRationalCoefficient h hD k u))
    a m q hq p secondCoefficient _ _
    (by intros; rw [fractionRow_scale, fractionRow_first])
    (by intros; rw [fractionRow_scale, fractionRow_zeroCoeff, map_pow])]
  rw [euler_twice_minus, localEulerRow_correct]
  rw [← scale_scale, cleared_operator_correct]
  simp only [firstRationalCoefficient, jet_scale, ← scale_plus, scale_scale, clearedRationalOperator,
    scale_plus]
  apply Prod.ext
  · simp only [plus, scale]; ring
  · apply Prod.ext <;> simp only [plus, scale] <;> ring

theorem originResidual_correct (h hD k : ℂ) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0)
    (p : Row ℂ[X]) :
    fractionRow (originResidual h hD k m q p) (X^m*q^4) =
      scale (R^4) (rationalOperator h hD k (fractionRow p (X^m*q))) := by
  simp only [← localCoordinate_zero]
  rw [originResidual, eulerResidual_correct
    (βr := fun u => scale (ι (2*shiftedRadius)) (plus u (jet (ι (jetA h k)) (ι jetB) 1 u)))
    (γr := zeroRationalCoefficient h hD k)
    0 m q hq p _ _ _
    (by intros; simp only [fractionRow_scale, fractionRow_plus, jetNumerator, fractionRow_jet, map_one])
    (fractionRow_zeroCoeff h hD k)]
  rw [euler_twice_minus, localEulerRow_correct, cleared_operator_correct]
  simp only [localCoordinate_zero, RatFunc.algebraMap_X, firstRationalCoefficient, jet_scale, ← scale_plus,
    scale_scale, clearedRationalOperator, secondCoefficient, shiftedRadius, map_mul, map_sub, map_pow,
    map_ofNat, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  apply Prod.ext
  · simp only [plus, scale]; ring
  · apply Prod.ext <;> simp only [plus, scale] <;> ring

theorem horizonResidual_correct (h hD k : ℂ) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0)
    (p : Row ℂ[X]) :
    fractionRow (horizonResidual h hD k m q p) (localCoordinate 2^m*q^4) =
      scale (R^4) (rationalOperator h hD k (fractionRow p (localCoordinate 2^m*q))) := by
  rw [horizonResidual, eulerResidual_correct
    (βr := fun u => scale (ι (2*X)) (plus u (jet (ι (jetA h k)) (ι jetB) 1 u)))
    (γr := zeroRationalCoefficient h hD k)
    2 m q hq p _ _ _
    (by intros; simp only [fractionRow_scale, fractionRow_plus, jetNumerator, fractionRow_jet, map_one])
    (fractionRow_zeroCoeff h hD k)]
  rw [euler_twice_minus, localEulerRow_correct, cleared_operator_correct]
  simp only [firstRationalCoefficient, jet_scale, ← scale_plus, scale_scale, clearedRationalOperator,
    secondCoefficient, shiftedRadius, localCoordinate, map_mul, map_sub, map_pow, map_ofNat,
    RatFunc.algebraMap_X]

private theorem infinityStep_fraction (h k : ℂ) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0) (p : Row ℂ[X]) :
    fractionRow (infinityDerivativeNumerator h k m q p) (X^m*q^2) =
      infinityStep h k (fractionRow p (X^m*q)) := by
  have pad : fractionRow (scale q p) (X^m*q^2) = fractionRow p (X^m*q) := by
    simpa only [localCoordinate_zero, pow_two] using pad_fraction X m q q hq p
  have e : fractionRow (rowEulerZero m q p) (X^m*q^2) =
      localEulerRow 0 (fractionRow p (X^m*q)) := by
    simpa only [localCoordinate_zero, rowEulerZero, rowEuler] using (eulerRow_fraction 0 m p q hq).symm
  simp only [infinityDerivativeNumerator, infinityStep, fractionRow_plus, fractionRow_scale, e,
    fractionRow_jet, map_zero, map_one]
  have jetPad := congrArg (jet (ι (infinityJetA h k)) 0 1) pad
  rw [fractionRow_scale] at jetPad
  rw [jetPad]

theorem infinityResidual_correct (h hD k : ℂ) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0) (p : Row ℂ[X]) :
    fractionRow (infinityResidual h hD k m q p) (X^m*q^4) =
      infinityOperator h hD k (fractionRow p (X^m*q)) := by
  have e := infinityStep_fraction h k m (q^2) (pow_ne_zero 2 hq) (infinityDerivativeNumerator h k m q p)
  rw [← pow_mul, show 2*2=4 by decide, infinityStep_fraction _ _ _ _ hq] at e
  have pad : fractionRow (scale (q^3) p) (X^m*q^4) = fractionRow p (X^m*q) := by
    simpa only [localCoordinate_zero, ← pow_succ'] using pad_fraction X m q (q^3) (pow_ne_zero 3 hq) p
  rw [infinityResidual, fractionRow_minus, e, infinityOperator, ← scale_scale, fractionRow_scale, pad]

#print axioms ordinaryResidual_correct
#print axioms originResidual_correct
#print axioms horizonResidual_correct
#print axioms infinityResidual_correct

end

end SchwarzschildLaurent
