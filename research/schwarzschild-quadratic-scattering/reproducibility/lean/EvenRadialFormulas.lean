import EvenCurvatureTable
import MixedRadialFormulas

/-! Form the polar curvature and master source as quadratic rows in
the shared Regge–Wheeler parent J and Z = r² dJ/dr*. -/
namespace SchwarzschildEinstein.PureOdd.Polar

open Mixed

variable {K : Type u} [NatCast K] [Add K] [Sub K] [Mul K] [Div K] [Neg K] [Pow K Nat]

def productRow (a b : Linear K) : Quadratic K :=
  (a.1*b.1,a.1*b.2+a.2*b.1,a.2*b.2)

def tableCurvature {A : Type u} (entry : List JetProduct → A) : Curvature A :=
  ⟨entry ttTerms, entry rrTerms, entry rqTerms, entry vvTerms, entry qqTerms⟩

def curveRows (C : Rat → K) (w : JetProduct → K) (E : PolarParentJets (Linear K)) :
    Curvature (Quadratic K) :=
  tableCurvature (evaluateWith (C 0,C 0,C 0) plus scale
    (fun i j => productRow (jetValue E i) (jetValue E j)) w)

def evenSourceRows (C : Rat → K) (dr : K → K) (r k ell : K) : EvenSource (Quadratic K) :=
  let w := weight C r (C 1/r) (C 1/(r-C 2)) k ell
  sourceFromCurvature C plus scale r ell (curveRows C w (polarReconstruction dr r k ell))

def bareEvenRows (C : Rat → K) (dr : K → K) (r k ell : K) : Quadratic K :=
  projectedMaster dr r k ell (evenSourceRows C dr r k ell)

end SchwarzschildEinstein.PureOdd.Polar
