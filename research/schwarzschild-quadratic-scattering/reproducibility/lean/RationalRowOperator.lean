import RationalCalculus
import LaurentReduction

/-! The rational Schwarzschild row operator and its polynomial form. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

def mapRow {A B : Type*} (g : A → B) (u : Row A) : Row B :=
  (g u.1, g u.2.1, g u.2.2)

theorem mapRow_plus {A B : Type*} [Semiring A] [Semiring B]
    (g : A →+* B) (u v : Row A) : mapRow g (plus u v) = plus (mapRow g u) (mapRow g v) := by
  simp [mapRow, plus]

theorem mapRow_minus {A B : Type*} [Ring A] [Ring B]
    (g : A →+* B) (u v : Row A) : mapRow g (minus u v) = minus (mapRow g u) (mapRow g v) := by
  simp [mapRow, minus]

theorem mapRow_scale {A B : Type*} [Semiring A] [Semiring B]
    (g : A →+* B) (c : A) (u : Row A) : mapRow g (scale c u) = scale (g c) (mapRow g u) := by
  simp [mapRow, scale]

theorem mapRow_jet {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (a b c : A) (u : Row A) :
    mapRow g (jet a b c u) = jet (g a) (g b) (g c) (mapRow g u) := by
  have ht : g (2 : A) = (2 : B) := map_ofNat g 2
  simp [mapRow, jet, ht]

theorem jet_scale {A : Type*} [CommRing A] (a b c s : A) (u : Row A) :
    jet a b c (scale s u) = scale s (jet a b c u) := by
  apply Prod.ext
  · simp only [jet, scale]; ring
  · apply Prod.ext <;> simp only [jet, scale] <;> ring

theorem scale_scale {A : Type*} [CommRing A] (a b : A) (u : Row A) :
    scale a (scale b u) = scale (a*b) u := by simp [scale, mul_assoc]

theorem scale_plus {A : Type*} [CommRing A] (a : A) (u v : Row A) :
    scale a (plus u v) = plus (scale a u) (scale a v) := by simp [scale, plus, mul_add]

theorem scale_minus {A : Type*} [CommRing A] (a : A) (u v : Row A) :
    scale a (minus u v) = minus (scale a u) (scale a v) := by simp [scale, minus, mul_sub]

def rationalRowDerivative (u : Row ℂᵣ) : Row ℂᵣ := mapRow δ u

theorem rationalRowDerivative_plus (u v : Row ℂᵣ) :
    rationalRowDerivative (plus u v) = plus (rationalRowDerivative u) (rationalRowDerivative v) := by
  simp [rationalRowDerivative, mapRow, plus, rationalDerivative_add]

theorem rationalRowDerivative_scale (c : ℂᵣ) (u : Row ℂᵣ) :
    rationalRowDerivative (scale c u) =
      plus (scale (δ c) u) (scale c (rationalRowDerivative u)) := by
  simp [rationalRowDerivative, mapRow, plus, scale, rationalDerivative_mul]

private theorem rationalDerivative_two : δ (2 : ℂᵣ) = 0 := by
  have h : Cᵣ 2 = (2 : ℂᵣ) := map_ofNat Cᵣ 2
  rw [← h]
  exact rationalDerivative_constant 2

theorem rationalRowDerivative_jet (a b c : ℂᵣ) (u : Row ℂᵣ) :
    rationalRowDerivative (jet a b c u) =
      plus (jet (δ a) (δ b) (δ c) u) (jet a b c (rationalRowDerivative u)) := by
  apply Prod.ext
  · simp [rationalRowDerivative, mapRow, jet, plus, rationalDerivative_mul]
  · apply Prod.ext <;> simp [rationalRowDerivative, mapRow, jet, plus,
      rationalDerivative_mul, rationalDerivative_add, rationalDerivative_two] <;> ring

def radialFactor : ℂᵣ := (R-2)/R

def oddPotential (h : ℂ) : ℂᵣ := radialFactor * (Cᵣ h/R^2 - 6/R^3)

def rationalStep (h k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  plus (scale radialFactor (rationalRowDerivative u))
    (jet (ι (jetA h k)/R^2) (ι jetB/R^2) (1/R^2) u)

def rationalOperator (h hD k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  minus (rationalStep h k (rationalStep h k u)) (scale (Cᵣ (4*k^2)+oddPotential hD) u)

/-- The rescaled jet used in the matrix proof. -/
theorem rationalStep_physical (h k : ℂ) (u : Row ℂᵣ) :
    rationalStep h k u = plus (scale radialFactor (rationalRowDerivative u))
      (jet (R^2*(Cᵣ (k^2)+oddPotential h)) (2*radialFactor/R) (1/R^2) u) := by
  have ha : ι (jetA h k)/R^2 = R^2*(Cᵣ (k^2)+oddPotential h) := by
    simp only [jetA, map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, radialFactor, oddPotential, map_ofNat]
    field_simp [RatFunc.X_ne_zero] <;> ring
  have hb : ι jetB/R^2 = 2*radialFactor/R := by
    simp only [jetB, shiftedRadius, map_mul, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat,
      radialFactor]
    field_simp [RatFunc.X_ne_zero] <;> ring
  rw [rationalStep, ha, hb]

def firstRationalCoefficient (h k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  scale (2 * R * (R-2)) (plus u (jet (ι (jetA h k)) (ι jetB) 1 u))

def daughterNumerator (hD k : ℂ) : ℂ[X] :=
  C (4*k^2)*X^4 + shiftedRadius*(C hD*X-6)

def zeroRationalCoefficient (h hD k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  let j := jet (ι (jetA h k)) (ι jetB) 1
  let dj := jet (ι (jetA h k).derivative) (ι jetB.derivative) 0
  plus (scale (R-2) (minus (scale R (dj u)) (scale 2 (j u))))
    (minus (j (j u)) (scale (ι (daughterNumerator hD k)) u))

def clearedRationalOperator (h hD k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  plus (scale (ι secondCoefficient) (rationalRowDerivative (rationalRowDerivative u)))
    (plus (firstRationalCoefficient h k (rationalRowDerivative u)) (zeroRationalCoefficient h hD k u))

private theorem radialFactor_derivative : δ radialFactor = 2/R^2 := by
  simp only [radialFactor, rationalDerivative_div, rationalDerivative_sub, rationalDerivative_radius,
    rationalDerivative_two, sub_zero, one_mul, mul_one]
  ring

private theorem derivative_radius_squared_denominator (c : ℂᵣ) :
    δ (c/R^2) = δ c/R^2 - 2*c/R^3 := by
  rw [rationalDerivative_div, rationalDerivative_pow, rationalDerivative_radius]
  norm_num
  field_simp [RatFunc.X_ne_zero] <;> ring

private theorem daughterNumerator_correct (hD k : ℂ) :
    ι (daughterNumerator hD k) = R^4*(Cᵣ (4*k^2)+oddPotential hD) := by
  simp only [daughterNumerator, shiftedRadius, map_mul, map_add, map_sub, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, oddPotential, radialFactor]
  field_simp [RatFunc.X_ne_zero] <;> ring

/-- The polynomial equation is the rational equation multiplied by r⁴. -/
theorem cleared_operator_correct (h hD k : ℂ) (u : Row ℂᵣ) :
    scale (R^4) (rationalOperator h hD k u) = clearedRationalOperator h hD k u := by
  simp only [rationalOperator, rationalStep, rationalRowDerivative_plus, rationalRowDerivative_scale,
    rationalRowDerivative_jet, radialFactor_derivative, derivative_radius_squared_denominator,
    rationalDerivative_algebraMap, rationalDerivative_one, clearedRationalOperator,
    firstRationalCoefficient, zeroRationalCoefficient, daughterNumerator_correct, secondCoefficient,
    shiftedRadius, map_mul, map_pow, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  simp only [radialFactor, map_ofNat]
  apply Prod.ext
  · simp only [scale, plus, minus, jet]
    field_simp [RatFunc.X_ne_zero] <;> ring
  · apply Prod.ext <;> simp only [scale, plus, minus, jet] <;>
    field_simp [RatFunc.X_ne_zero] <;> ring

def unscaledStep (h k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  plus (scale radialFactor (rationalRowDerivative u)) (jet (Cᵣ (k^2)+oddPotential h) 0 1 u)

def unscaledOperator (h hD k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  minus (unscaledStep h k (unscaledStep h k u)) (scale (Cᵣ (4*k^2)+oddPotential hD) u)

theorem unscaled_step_correct (h k : ℂ) (u : Row ℂᵣ) :
    unscaledRow (rationalStep h k u) = unscaledStep h k (unscaledRow u) := by
  rw [rationalStep_physical]
  apply Prod.ext
  · simp only [unscaledRow, unscaledStep, plus, scale, jet, rationalRowDerivative, mapRow]
    ring
  · apply Prod.ext <;> simp only [unscaledRow, unscaledStep, plus, scale, jet, rationalRowDerivative,
      mapRow, rationalDerivative_mul, rationalDerivative_pow, rationalDerivative_radius] <;>
    norm_num <;> field_simp [RatFunc.X_ne_zero] <;> ring

private theorem unscaled_minus (u v : Row ℂᵣ) :
    unscaledRow (minus u v) = minus (unscaledRow u) (unscaledRow v) := by simp [unscaledRow, minus, sub_mul]

private theorem unscaled_scale (a : ℂᵣ) (u : Row ℂᵣ) :
    unscaledRow (scale a u) = scale a (unscaledRow u) := by simp [unscaledRow, scale, mul_assoc]

theorem unscaled_operator_correct (h hD k : ℂ) (u : Row ℂᵣ) :
    unscaledRow (rationalOperator h hD k u) = unscaledOperator h hD k (unscaledRow u) := by
  simp only [rationalOperator, unscaled_minus, unscaled_scale, unscaled_step_correct, unscaledOperator]

#print axioms rationalStep_physical
#print axioms cleared_operator_correct
#print axioms unscaled_operator_correct

end

end SchwarzschildLaurent
