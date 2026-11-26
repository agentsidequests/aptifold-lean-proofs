import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NoncommRing

/-! Coordinate expansion at order two in the perturbation parameter.
The coordinate derivatives act on the coefficients, leaving that parameter
fixed. The curvature convention is the one used by the native source replay. -/
namespace SchwarzschildEinstein

open PowerSeries
open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [Field A]

abbrev Tensor (ι A : Type*) := Matrix ι ι A
abbrev Connection (ι A : Type*) := ι → ι → ι → A

def tensorCoeff (n : ℕ) (g : Tensor ι A⟦X⟧) : Tensor ι A :=
  fun a b => coeff n (g a b)

private theorem coeff_mul_zero (p q : A⟦X⟧) :
    coeff 0 (p*q) = coeff 0 p * coeff 0 q := by
  simp [coeff_zero_eq_constantCoeff_apply]

private theorem coeff_mul_one (p q : A⟦X⟧) :
    coeff 1 (p*q) = coeff 0 p * coeff 1 q + coeff 1 p * coeff 0 q := by
  rw [PowerSeries.coeff_one_mul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
  ring

private theorem coeff_mul_two (p q : A⟦X⟧) :
    coeff 2 (p*q) = coeff 0 p * coeff 2 q + coeff 1 p * coeff 1 q + coeff 2 p * coeff 0 q := by
  rw [PowerSeries.coeff_mul]
  rw [show Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} by decide]
  simp [add_assoc]

private theorem tensorCoeff_mul_one (p q : Tensor ι A⟦X⟧) :
    tensorCoeff 1 (p*q) = tensorCoeff 0 p * tensorCoeff 1 q + tensorCoeff 1 p * tensorCoeff 0 q := by
  ext a b
  simp only [tensorCoeff, Matrix.mul_apply, Matrix.add_apply, map_sum, coeff_mul_one,
    Finset.sum_add_distrib]

private theorem tensorCoeff_mul_two (p q : Tensor ι A⟦X⟧) :
    tensorCoeff 2 (p*q) = tensorCoeff 0 p * tensorCoeff 2 q +
      tensorCoeff 1 p * tensorCoeff 1 q + tensorCoeff 2 p * tensorCoeff 0 q := by
  ext a b
  simp only [tensorCoeff, Matrix.mul_apply, Matrix.add_apply, map_sum, coeff_mul_two,
    Finset.sum_add_distrib]

omit [Fintype ι] in
private theorem tensorCoeff_one_succ [DecidableEq ι] (n : ℕ) :
    tensorCoeff (n+1) (1 : Tensor ι A⟦X⟧) = 0 := by
  ext a b
  by_cases h : a = b <;> simp [tensorCoeff, Matrix.one_apply, PowerSeries.coeff_one, h]

/-- An inverse series forces the usual negative first variation and the
quadratic inverse term, including the separate contribution of the order-two metric. -/
theorem inverse_coefficients [DecidableEq ι] (g B : Tensor ι A⟦X⟧) (inverse : B*g = 1)
    (right : tensorCoeff 0 g * tensorCoeff 0 B = 1) :
    let H := tensorCoeff 1 g
    let Ginv := tensorCoeff 0 B
    tensorCoeff 1 B = -(Ginv*H*Ginv) ∧
      tensorCoeff 2 B = Ginv*H*Ginv*H*Ginv - Ginv*tensorCoeff 2 g*Ginv := by
  dsimp
  have first := congrArg (tensorCoeff 1) inverse
  have second := congrArg (tensorCoeff 2) inverse
  rw [tensorCoeff_mul_one, tensorCoeff_one_succ 0] at first
  rw [tensorCoeff_mul_two, tensorCoeff_one_succ 1] at second
  have first' := congrArg (fun M : Tensor ι A => M * tensorCoeff 0 B) first
  have second' := congrArg (fun M : Tensor ι A => M * tensorCoeff 0 B) second
  simp only [add_mul, mul_assoc, right, mul_one, zero_mul] at first' second'
  have h := eq_neg_of_add_eq_zero_right first'
  refine ⟨by simpa only [mul_assoc] using h, ?_⟩
  rw [h] at second'
  calc
    tensorCoeff 2 B = -((tensorCoeff 0 B * (tensorCoeff 2 g * tensorCoeff 0 B)) +
        -(tensorCoeff 0 B * (tensorCoeff 1 g * tensorCoeff 0 B)) *
          (tensorCoeff 1 g * tensorCoeff 0 B)) := eq_neg_of_add_eq_zero_right second'
    _ = _ := by noncomm_ring

def seriesPartial (d : ι → A → A) (a : ι) (p : A⟦X⟧) : A⟦X⟧ :=
  PowerSeries.mk fun n => d a (coeff n p)

omit [Fintype ι] in
@[simp] theorem coeff_partial (d : ι → A → A) (a : ι) (p : A⟦X⟧) (n : ℕ) :
    coeff n (seriesPartial d a p) = d a (coeff n p) := by
  simp [seriesPartial]

def metricDerivative {S : Type*} [Ring S] (d : ι → S → S)
    (g : Tensor ι S) (a b c : ι) : S :=
  d b (g a c) + d c (g a b) - d a (g b c)

def christoffel {S : Type*} [CommRing S] (half : S) (d : ι → S → S)
    (B g : Tensor ι S) : Connection ι S :=
  fun a b c => half * ∑ j, B a j * metricDerivative d g j b c

private theorem christoffel_inverse_add (half : A) (d : ι → A → A) (B C g : Tensor ι A) :
    christoffel half d (B+C) g = christoffel half d B g + christoffel half d C g := by
  funext a b c
  simp only [christoffel, Matrix.add_apply, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

def connectionCoeff (n : ℕ) (G : Connection ι A⟦X⟧) : Connection ι A :=
  fun a b c => coeff n (G a b c)

local notation "½" => (1/2 : A)

private theorem connection_zero (d : ι → A → A) (B g : Tensor ι A⟦X⟧) :
    connectionCoeff 0 (christoffel (C ½) (seriesPartial d) B g) =
      christoffel ½ d (tensorCoeff 0 B) (tensorCoeff 0 g) := by
  funext a b c
  simp only [connectionCoeff, christoffel, metricDerivative, tensorCoeff, PowerSeries.coeff_C_mul,
    map_sum, coeff_mul_zero, map_add, map_sub, coeff_partial]

private theorem connection_one (d : ι → A → A) (B g : Tensor ι A⟦X⟧) :
    connectionCoeff 1 (christoffel (C ½) (seriesPartial d) B g) =
      christoffel ½ d (tensorCoeff 0 B) (tensorCoeff 1 g) +
      christoffel ½ d (tensorCoeff 1 B) (tensorCoeff 0 g) := by
  funext a b c
  simp only [connectionCoeff, christoffel, metricDerivative, tensorCoeff, PowerSeries.coeff_C_mul,
    map_sum, coeff_mul_one, map_add, map_sub, coeff_partial, Pi.add_apply,
    Finset.sum_add_distrib, mul_add]

private theorem connection_two (d : ι → A → A) (B g : Tensor ι A⟦X⟧) :
    connectionCoeff 2 (christoffel (C ½) (seriesPartial d) B g) =
      christoffel ½ d (tensorCoeff 0 B) (tensorCoeff 2 g) +
      christoffel ½ d (tensorCoeff 1 B) (tensorCoeff 1 g) +
      christoffel ½ d (tensorCoeff 2 B) (tensorCoeff 0 g) := by
  funext a b c
  simp only [connectionCoeff, christoffel, metricDerivative, tensorCoeff, PowerSeries.coeff_C_mul,
    map_sum, coeff_mul_two, map_add, map_sub, coeff_partial, Pi.add_apply,
    Finset.sum_add_distrib, mul_add]

def connectionDivergence {S : Type*} [Ring S] (d : ι → S → S)
    (g : Connection ι S) : Tensor ι S :=
  fun a b => ∑ c, (d c (g c a b) - d b (g c a c))

def connectionProduct {S : Type*} [Ring S] (g h : Connection ι S) : Tensor ι S :=
  fun a b => ∑ c, ∑ j, (g c c j * h j a b - g c b j * h j a c)

private theorem divergence_add (d : ι → A →+ A) (g h : Connection ι A) :
    connectionDivergence (fun a => d a) (g+h) =
      connectionDivergence (fun a => d a) g + connectionDivergence (fun a => d a) h := by
  ext a b
  simp only [connectionDivergence, Matrix.add_apply, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem product_add_left (g h j : Connection ι A) :
    connectionProduct (g+h) j = connectionProduct g j + connectionProduct h j := by
  ext a b
  simp only [connectionProduct, Matrix.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

private theorem product_add_right (g h j : Connection ι A) :
    connectionProduct g (h+j) = connectionProduct g h + connectionProduct g j := by
  ext a b
  simp only [connectionProduct, Matrix.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

def ricci {S : Type*} [Ring S] (d : ι → S → S) (g : Connection ι S) : Tensor ι S :=
  connectionDivergence d g + connectionProduct g g

theorem ricci_second (d : ι → A → A) (G : Connection ι A⟦X⟧) :
    tensorCoeff 2 (ricci (seriesPartial d) G) =
      connectionDivergence d (connectionCoeff 2 G) +
      (connectionProduct (connectionCoeff 0 G) (connectionCoeff 2 G) +
       connectionProduct (connectionCoeff 1 G) (connectionCoeff 1 G) +
       connectionProduct (connectionCoeff 2 G) (connectionCoeff 0 G)) := by
  ext a b
  simp only [tensorCoeff, connectionCoeff, ricci, Matrix.add_apply, connectionDivergence,
    connectionProduct, map_add, map_sub, map_sum, coeff_partial, coeff_mul_two]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

def linearConnection (d : ι → A → A) (g B H : Tensor ι A) : Connection ι A :=
  christoffel ½ d B H + christoffel ½ d (-(B*H*B)) g

def quadraticConnection (d : ι → A → A) (g B H : Tensor ι A) : Connection ι A :=
  christoffel ½ d (-(B*H*B)) H + christoffel ½ d (B*H*B*H*B) g

def linearRicci (d : ι → A → A) (g B H : Tensor ι A) : Tensor ι A :=
  let G0 := christoffel ½ d B g
  let G1 := linearConnection d g B H
  connectionDivergence d G1 + (connectionProduct G0 G1 + connectionProduct G1 G0)

def quadraticRicci (d : ι → A → A) (g B H : Tensor ι A) : Tensor ι A :=
  let G0 := christoffel ½ d B g
  let G1 := linearConnection d g B H
  let G2 := quadraticConnection d g B H
  connectionDivergence d G2 +
    (connectionProduct G0 G2 + connectionProduct G1 G1 + connectionProduct G2 G0)

theorem ricci_from_parent_metric [DecidableEq ι] (d : ι → A → A) (d_zero : ∀ a, d a 0 = 0)
    (g B : Tensor ι A⟦X⟧) (inverse : B*g = 1)
    (right : tensorCoeff 0 g * tensorCoeff 0 B = 1) (source : tensorCoeff 2 g = 0) :
    tensorCoeff 2 (ricci (seriesPartial d) (christoffel (C ½) (seriesPartial d) B g)) =
      quadraticRicci d (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 1 g) := by
  obtain ⟨first, second⟩ := inverse_coefficients g B inverse right
  have z (I : Tensor ι A) : christoffel ½ d I 0 = 0 := by
    funext a b c
    simp [christoffel, metricDerivative, d_zero]
  rw [ricci_second, connection_zero, connection_one, connection_two, first, second, source]
  simp only [quadraticRicci, linearConnection, quadraticConnection, z, zero_add, mul_zero, zero_mul,
    sub_zero]

/-- The order-two Ricci coefficient contains the first variation on the
daughter plus the quadratic term on the parent. -/
theorem ricci_parent_daughter_split [DecidableEq ι] (d : ι → A →+ A)
    (g B : Tensor ι A⟦X⟧) (inverse : B*g = 1)
    (right : tensorCoeff 0 g * tensorCoeff 0 B = 1) :
    let d' : ι → A → A := fun a => d a
    let R := ricci (seriesPartial d') (christoffel (C ½) (seriesPartial d') B g)
    tensorCoeff 2 R =
      linearRicci d' (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 2 g) +
      quadraticRicci d' (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 1 g) := by
  dsimp only
  obtain ⟨first, second⟩ := inverse_coefficients g B inverse right
  rw [ricci_second, connection_zero, connection_one, connection_two, first, second, sub_eq_add_neg,
    christoffel_inverse_add]
  have reorder (x y z w : Connection ι A) : x+y+(z+w) = (x+w)+(y+z) := by abel
  rw [reorder, divergence_add]
  simp only [linearRicci, quadraticRicci, linearConnection, quadraticConnection, product_add_left,
    product_add_right]
  abel

def contraction {S : Type*} [Ring S] (B R : Tensor ι S) : S :=
  ∑ a, ∑ b, B a b * R a b

def einstein {S : Type*} [CommRing S] (half : S) (g B R : Tensor ι S) : Tensor ι S :=
  fun a b => R a b - half * (g a b * contraction B R)

private theorem einstein_add (half : A) (g B R S : Tensor ι A) :
    einstein half g B (R+S) = einstein half g B R + einstein half g B S := by
  ext a b
  simp only [einstein, contraction, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- In vacuum the lower Ricci coefficients vanish. Hence at order two
trace reversal uses only the background metric and its inverse. -/
theorem einstein_second_of_vacuum (g B Ric : Tensor ι A⟦X⟧)
    (vacuum : tensorCoeff 0 Ric = 0) (linearVacuum : tensorCoeff 1 Ric = 0) :
    tensorCoeff 2 (einstein (C ½) g B Ric) =
      einstein ½ (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 2 Ric) := by
  have zero (a b : ι) : coeff 0 (Ric a b) = 0 := congrFun (congrFun vacuum a) b
  have one (a b : ι) : coeff 1 (Ric a b) = 0 := congrFun (congrFun linearVacuum a) b
  ext a b
  simp [tensorCoeff, einstein, contraction, PowerSeries.coeff_C_mul, coeff_mul_zero,
    coeff_mul_one, coeff_mul_two, zero, one]

/-- Quadratic forcing in the linear equation for the daughter metric. The
parent supplies only the constant and first variations of the metric. -/
theorem forcing_from_parent_metric [DecidableEq ι] (d : ι → A → A) (d_zero : ∀ a, d a 0 = 0)
    (g B : Tensor ι A⟦X⟧) (inverse : B*g = 1)
    (right : tensorCoeff 0 g * tensorCoeff 0 B = 1) (source : tensorCoeff 2 g = 0)
    (vacuum : tensorCoeff 0 (ricci (seriesPartial d)
      (christoffel (C ½) (seriesPartial d) B g)) = 0)
    (linearVacuum : tensorCoeff 1 (ricci (seriesPartial d)
      (christoffel (C ½) (seriesPartial d) B g)) = 0) :
    -(tensorCoeff 2 (einstein (C ½) g B (ricci (seriesPartial d)
      (christoffel (C ½) (seriesPartial d) B g)))) =
      -(einstein ½ (tensorCoeff 0 g) (tensorCoeff 0 B)
        (quadraticRicci d (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 1 g))) := by
  rw [einstein_second_of_vacuum _ _ _ vacuum linearVacuum, ricci_from_parent_metric d d_zero
    g B inverse right source]

#print axioms forcing_from_parent_metric

/-- The vacuum Einstein equation at order two is a linear sourced equation
for the daughter, with the negative quadratic Einstein tensor as source. -/
theorem sourced_linear_einstein [DecidableEq ι] (d : ι → A →+ A) (g B : Tensor ι A⟦X⟧)
    (inverse : B*g = 1) (right : tensorCoeff 0 g * tensorCoeff 0 B = 1) :
    let d' : ι → A → A := fun a => d a
    let R := ricci (seriesPartial d') (christoffel (C ½) (seriesPartial d') B g)
    let g0 := tensorCoeff 0 g
    let B0 := tensorCoeff 0 B
    tensorCoeff 0 R = 0 → tensorCoeff 1 R = 0 →
    (tensorCoeff 2 (einstein (C ½) g B R) = 0 ↔
      einstein ½ g0 B0 (linearRicci d' g0 B0 (tensorCoeff 2 g)) =
        -(einstein ½ g0 B0 (quadraticRicci d' g0 B0 (tensorCoeff 1 g)))) := by
  dsimp only
  intro vacuum parentVacuum
  rw [einstein_second_of_vacuum _ _ _ vacuum parentVacuum,
    ricci_parent_daughter_split d g B inverse right, einstein_add]
  exact ⟨eq_neg_of_add_eq_zero_left, fun h => by rw [h, neg_add_cancel]⟩

#print axioms sourced_linear_einstein

end

end SchwarzschildEinstein
