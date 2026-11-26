import QuadraticOrbitData
import EvenRadialFormulas
import ParityReconstructionData

/-! Complete polar source rows and their three conservation equations
in the shared parent basis J², JZ, Z². -/
namespace SchwarzschildEinstein.PureOdd.Master

def purePolarSource {A : Type u} (zero : A) (p : EvenSource A)
    (cross timeVector : A) : ModeSource A :=
  ⟨p,cross,timeVector,⟨zero,zero⟩,zero⟩

def pureAxialSource {A : Type u} (zero : A) (vector : Mixed.AxialVector A)
    (angular : A) : ModeSource A :=
  ⟨⟨zero,zero,zero,zero,zero⟩,zero,zero,vector,angular⟩

def mapModeSource {A B : Type u} (g : A → B) (s : ModeSource A) : ModeSource B :=
  ⟨⟨g s.polar.tt,g s.polar.rr,g s.polar.radialVector,g s.polar.sphereTrace,g s.polar.traceFree⟩,
    g s.tr,g s.timeVector,⟨g s.axial.time,g s.axial.radius⟩,g s.axialTensor⟩

section
variable {S : Type u} [NatCast S] [Add S] [Sub S] [Mul S] [Div S] [Neg S] [Pow S Nat]

def polarExtraRows (q : Rat → S) (D : S → S) (r k ell : S) (terms : List Polar.JetProduct) :
    Quadratic S :=
  let E := Mixed.polarReconstruction D r k ell
  Polar.evaluateWith (q 0,q 0,q 0) plus scale
    (fun i j => Polar.productRow (Polar.jetValue E i) (Polar.jetValue E j))
    (Polar.weight q r (q 1/r) (q 1/(r-q 2)) k ell) terms

def evenParentSourceRows (q : Rat → S) (D : S → S) (r k ell : S) : ModeSource (Quadratic S) :=
  purePolarSource (q 0,q 0,q 0) (Polar.evenSourceRows q D r k ell)
    (scale (-(q 1)) (polarExtraRows q D r k ell Polar.trTerms))
    (scale (-(q 1/(q 2*ell))) (polarExtraRows q D r k ell Polar.tqTerms))

def oddParentSourceRows (q : Rat → S) (D : S → S) (r k ell : S) : ModeSource (Quadratic S) :=
  let T := parentJet D r k ell (timeAmplitude r)
  let P := parentJet D r k ell (radiusAmplitude r k)
  let ri := q 1/r
  let hi := q 1/(r-q 2)
  purePolarSource (q 0,q 0,q 0) (sourceRows D r k ell)
    (rows (oddParentCross q r k ell ri hi) T P)
    (rows (oddParentTimeVector q r k ell ri hi) T P)

def polarConservationRows (q : Rat → S) (D : S → S) (r k ell : S) (s : ModeSource (Quadratic S)) :
    Quadratic S × Quadratic S × Quadratic S :=
  let w := q 2*k
  let m := q 2*ell
  let L := m*(m+q 1)
  let mu := (m-q 1)*(m+q 2)
  let r2 := r*r
  let f := lapse r
  let vectorFactor := q 2/r2+q 2*f/r
  let derivative := rowDerivative D r k ell
  let time := plus (scale (w/f) s.polar.tt)
    (plus (scale f (derivative s.tr))
      (plus (scale vectorFactor s.tr) (scale (-(L/r2)) s.timeVector)))
  let radius := plus (scale f (derivative s.polar.rr))
    (plus (scale (q 3/r2+q 2*f/r) s.polar.rr)
      (plus (scale (q 1/(r2*(f*f))) s.polar.tt)
        (plus (scale (w/f) s.tr)
          (plus (scale (-(L/r2)) s.polar.radialVector)
            (scale (-(q 2/(r2*r))) s.polar.sphereTrace)))))
  let angular := plus (scale (w/f) s.timeVector)
    (plus (scale f (derivative s.polar.radialVector))
      (plus (scale vectorFactor s.polar.radialVector)
        (plus (scale (q 1/r2) s.polar.sphereTrace)
          (scale (-(mu/(q 2*r2))) s.polar.traceFree))))
  (time,radius,angular)

end
end SchwarzschildEinstein.PureOdd.Master
