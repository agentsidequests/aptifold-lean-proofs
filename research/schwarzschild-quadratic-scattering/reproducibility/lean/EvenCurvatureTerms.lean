import MixedVectorFormulas

/-! Quadratic curvature terms in the free jets of a polar parent.
Jet slots are tt, tr, rr and the sphere amplitude (including r²),
with value, first derivative and second derivative in each group. -/
namespace SchwarzschildEinstein.PureOdd.Polar

open Mixed

structure RadialMonomial where
  radius : Nat
  frequency : Nat
  angular : Nat
  coefficient : Rat

structure JetProduct where
  left : Fin 12
  right : Fin 12
  radiusDenominator : Nat
  horizonDenominator : Nat
  numerator : List RadialMonomial

structure Curvature (A : Type u) where
  tt : A
  rr : A
  rq : A
  vv : A
  qq : A

def jetValue {A : Type u} (E : PolarParentJets A) (i : Fin 12) : A :=
  if i = 0 then E.tt.val else if i = 1 then E.tt.first else if i = 2 then E.tt.second
  else if i = 3 then E.tr.val else if i = 4 then E.tr.first else if i = 5 then E.tr.second
  else if i = 6 then E.rr.val else if i = 7 then E.rr.first else if i = 8 then E.rr.second
  else if i = 9 then E.sphere.val else if i = 10 then E.sphere.first else E.sphere.second

def power {A : Type u} [Mul A] (one x : A) : Nat → A
  | 0 => one
  | n+1 => power one x n*x

def weight {A : Type u} [Add A] [Mul A] (C : Rat → A) (r rInv hInv k ell : A)
    (t : JetProduct) : A :=
  let p := power (C 1)
  let numerator := t.numerator.foldr (fun m total =>
    C m.coefficient*p r m.radius*p k m.frequency*p ell m.angular+total) (C 0)
  numerator*p rInv t.radiusDenominator*p hInv t.horizonDenominator

def evaluateWith {A B : Type u} (zero : B) (add : B → B → B) (scale : A → B → B)
    (product : Fin 12 → Fin 12 → B) (w : JetProduct → A) (terms : List JetProduct) : B :=
  terms.foldr (fun t sum => add (scale (w t) (product t.left t.right)) sum) zero

def evaluate {A : Type u} [Add A] [Mul A] (C : Rat → A) (w : JetProduct → A)
    (jet : Fin 12 → A) (terms : List JetProduct) : A :=
  evaluateWith (C 0) (·+·) (·*·) (fun i j => jet i*jet j) w terms

/-- Trace reversal and the daughter harmonic readout are linear in
the five curvature entries. Apply the same calculation to point values
and to the coefficient rows of J², JZ and Z². -/
def sourceFromCurvature {A B : Type u} [Add A] [Neg A] [Mul A] [Div A]
    (C : Rat → A) (add : B → B → B) (scale : A → B → B) (r ell : A)
    (R : Curvature B) : EvenSource B :=
  let f := (r+ -(C 2))/r
  let L := C 2*ell
  let angularTrace := add R.vv (scale (-(C 1)) R.qq)
  let trace := add (scale (-(C 1/f)) R.tt)
    (add (scale f R.rr) (scale (C 1/(r*r)) angularTrace))
  ⟨add (scale (-(C 1)) R.tt) (scale (-(f/C 2)) trace),
   add (scale (-(C 1)) R.rr) (scale (C 1/(C 2*f)) trace),
   scale (-(C 1/L)) R.rq,
   scale (C 1/C 2) (add (scale (-(C 1)) angularTrace) (scale (r*r) trace)),
   scale (-(C 1/(L*(L+ -(C 1))))) (add R.vv R.qq)⟩

end SchwarzschildEinstein.PureOdd.Polar
