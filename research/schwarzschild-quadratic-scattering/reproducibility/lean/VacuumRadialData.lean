import VacuumAngularData
import MixedProgram

/-! After the angular numerator is grouped by powers of cos θ, each
radial coefficient is linear in the same parent jets as the source. -/
namespace SchwarzschildEinstein.PureOdd.Vacuum

open AngularArithmetic SchwarzschildMixtures.ExactRational

structure RadialMonomial where
  radius : Nat
  frequency : Nat
  angular : Nat
  jet : Nat
  coefficient : Rat

abbrev AngularNumerator := List (Nat × List RadialMonomial)

def RadialMonomial.polynomial (t : RadialMonomial) (cPower : Nat) : Polynomial :=
  (((((Polynomial.constant t.coefficient).mul ((Polynomial.indeterminate 0).power t.radius)).mul
    ((Polynomial.indeterminate 1).power cPower)).mul
    ((Polynomial.indeterminate 2).power t.frequency)).mul
    ((Polynomial.indeterminate 3).power t.angular)).mul (Polynomial.indeterminate (4+t.jet))

def groupPolynomial (cPower : Nat) (terms : List RadialMonomial) : Polynomial :=
  terms.foldr (fun t p => (t.polynomial cPower).add p) []

def numeratorPolynomial (rows : AngularNumerator) : Polynomial :=
  rows.foldr (fun row p => (groupPolynomial row.1 row.2).add p) []

def jetEntry {A : Type} (zero : A) (T P : RadialJet A) (E : Mixed.PolarParentJets A) : Nat → A
  | 0 => T.val
  | 1 => T.first
  | 2 => T.second
  | 3 => P.val
  | 4 => P.first
  | 5 => P.second
  | 6 => E.tt.val
  | 7 => E.tt.first
  | 8 => E.tt.second
  | 9 => E.tr.val
  | 10 => E.tr.first
  | 11 => E.tr.second
  | 12 => E.rr.val
  | 13 => E.rr.first
  | 14 => E.rr.second
  | 15 => E.sphere.val
  | 16 => E.sphere.first
  | 17 => E.sphere.second
  | _ => zero

section Coefficients
variable {K : Type} [NatCast K] [Add K] [Sub K] [Neg K] [Mul K] [Div K] [Pow K Nat]

def reconstructedEntry (d : K → K) (r k ell : K) : Nat → Linear K :=
  jetEntry (Nat.cast 0, Nat.cast 0)
    (parentJet d r k ell (timeAmplitude r)) (parentJet d r k ell (radiusAmplitude r k))
    (Mixed.polarReconstruction d r k ell)

def radialWeight (cast : Rat → K) (r k ell : K) (t : RadialMonomial) : K :=
  cast t.coefficient * r^t.radius * k^t.frequency * ell^t.angular

def radialCoefficient (cast : Rat → K) (r k ell : K)
    (jets : Nat → Linear K) (terms : List RadialMonomial) : Linear K :=
  terms.foldr (fun t p => Mixed.linearAdd (Mixed.linearScale (radialWeight cast r k ell t) (jets t.jet)) p)
    (Nat.cast 0, Nat.cast 0)

end Coefficients

def coefficientProgram (terms : List RadialMonomial) : Linear Formula :=
  radialCoefficient Mixed.rationalConstant .radius .frequency .angular
    (reconstructedEntry Formula.dr .radius .frequency .angular) terms

def zeroCertificate (f : Formula) : Prop :=
  ∃ p : SchwarzschildMixtures.ExactRational.Fraction,
    Reduced f p ∧ SchwarzschildMixtures.Expr.Check p.num (.constant 0)

def vanishingCertificate (terms : List RadialMonomial) : Prop :=
  let p := coefficientProgram terms
  zeroCertificate p.1 ∧ zeroCertificate p.2

end SchwarzschildEinstein.PureOdd.Vacuum
