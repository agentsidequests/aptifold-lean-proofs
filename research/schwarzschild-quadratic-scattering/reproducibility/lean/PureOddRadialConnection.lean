import PureOddCoordinates

/-! The quadratic connection entry with upper polar and lower radial
and azimuthal indices. Its polar derivative occurs in the divergence
part of the radial–azimuthal Ricci component. -/
namespace SchwarzschildEinstein.PureOdd

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def quadraticConnection (r k ell : K) (T P : RadialJet K) : Connection Axis (FirstJet K) :=
  let g := background r
  let B := backgroundInverse r
  let H := parentMetric k ell T P
  let h : FirstMetric K := fun a b => (H a b).toFirstJet
  let BhB := jetMatMul (jetMatMul B h) B
  let BhBhB := jetMatMul (jetMatMul BhB h) B
  jetConnectionAdd (jetChristoffel (jetMatNeg BhB) H) (jetChristoffel BhBhB g)

/-- Select a Ricci component before evaluating any of its connections. -/
theorem quadratic_ricci_at (r k ell : K) (T P : RadialJet K) (a b : Axis) :
    quadraticJetRicci (background r) (backgroundInverse r) (parentMetric k ell T P) a b =
      let g := background r
      let B := backgroundInverse r
      let H := parentMetric k ell T P
      let h : FirstMetric K := fun i j => (H i j).toFirstJet
      let B₁ := jetMatNeg (jetMatMul (jetMatMul B h) B)
      let G₀ := jetChristoffel B g
      let G₁ := jetConnectionAdd (jetChristoffel B H) (jetChristoffel B₁ g)
      let G₂ := quadraticConnection r k ell T P
      (∑ c, ((G₂ c a b).gradient c - (G₂ c a c).gradient b)) +
        (connectionProduct (values G₀) (values G₂) a b +
          connectionProduct (values G₁) (values G₁) a b +
          connectionProduct (values G₂) (values G₀) a b) := rfl

theorem sum_axes {S : Type*} [AddCommMonoid S] (x : Axis → S) :
    ∑ i, x i = x 0 + x 1 + x 2 + x 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero]
  change x 0 + (x 1 + (x 2 + x 3)) = _
  ac_rfl

macro "reduce_quadratic_connection" : tactic =>
  `(tactic|
    (simp only [quadraticConnection, jetConnectionAdd, backgroundInverse,
       jetDiagonal_mul, mul_jetDiagonal, jetMatNeg, jetMatMul, jetChristoffel,
       FirstJet.add, FirstJet.mul, FirstJet.neg, FirstJet.constant, FirstJet.sum, sum_axes]
     simp [Fin.ext_iff, -Fin.val_eq_zero_iff, jetDiagonal, inverseDiagonal, background, parentMetric,
       jetMetricDerivative, carrier, radial, polar, oneAxis, SecondJet.constant,
       SecondJet.derivative, SecondJet.mul, SecondJet.neg, FirstJet.add, FirstJet.mul,
       FirstJet.sub, FirstJet.neg, FirstJet.constant]))

theorem polar_connection_at_equator (r k ell : K) (T P : RadialJet K) :
    (quadraticConnection r k ell T P 2 1 3).value = 0 := by
  reduce_quadratic_connection

theorem polar_connection_gradient [CharZero K] (r k ell : K) (T P : RadialJet K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) :
    (quadraticConnection r k ell T P 2 1 3).gradient 2 =
      -(ell^2*T.val*(T.first+k*P.val))/(2*r*(r-2)) +
        ell^2*T.val^2/(r^2*(r-2)) -
        ell^2*(r-2)*P.val^2/r^4 := by
  reduce_quadratic_connection
  field_simp [hr, hh]
  ring

#print axioms quadratic_ricci_at
#print axioms polar_connection_at_equator
#print axioms polar_connection_gradient

end
end SchwarzschildEinstein.PureOdd
