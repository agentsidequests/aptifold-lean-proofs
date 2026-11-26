import ParityMasterData
import VacuumAngularData

/-! The finite coordinate calculation for the linearized metric.
Use the same equatorial harmonic readout as the manuscript's source. -/
namespace SchwarzschildEinstein.PureOdd.Master

open AngularArithmetic AngularCalculation

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

def polarInputs : Mixed.PolarParentJets Fraction :=
  let jet (i : Nat) : RadialJet Fraction := ⟨X i,X (i+1),X (i+2)⟩
  ⟨jet 10,jet 13,jet 16,jet 19⟩

def axialTimeInput : RadialJet Fraction := ⟨X 4,X 5,X 6⟩
def axialRadiusInput : RadialJet Fraction := ⟨X 7,X 8,X 9⟩

def combinedInput (a b : Axis) : SecondJet Fraction :=
  Mixed.addJets (Mixed.polarParent (Q 0) a b) (affineParent (Q 0) a b)

def ricciAtEquator (a b : Axis) : Fraction :=
  Vacuum.parentRicci (Q (1/2)) (affineBackground (Q 0)) (affineInverse (Q 0) (Q 1))
    combinedInput a b

/-- The azimuthal vector and angular sum are left undivided until the
mode normalization is applied. This keeps the arithmetic in the chart. -/
def unnormalizedPolarReadouts {S : Type u} [Add S] [Neg S] [Mul S]
    (q : Rat → S) (r ri hi : S) (R : Axis → Axis → S) : EvenSource S :=
  let f := (r+ -(q 2))*ri
  let angular := R 2 2 + -(R 3 3)
  let trace := -(r*hi*R 0 0) + f*R 1 1 + ri*ri*angular
  ⟨R 0 0 + q (1/2)*f*trace,
    R 1 1 + -(q (1/2)*r*hi*trace),
    R 1 3,
    q (1/2)*(angular + -(r*r*trace)),
    R 2 2 + R 3 3⟩

def polarCoordinateData : EvenSource Fraction :=
  unnormalizedPolarReadouts Q (X 0) (rInv 1) (hInv 1) ricciAtEquator

def polarFormulaData : EvenSource Fraction :=
  let m := X 3
  let s := polarEinstein Q (X 0) (X 2) m (rInv 1) (hInv 1) polarInputs
  ⟨s.tt,s.rr,m*s.radialVector,s.sphereTrace,m*(m+ -(Q 1))*s.traceFree⟩

def axialCoordinateData : Mixed.AxialVector Fraction :=
  ⟨ricciAtEquator 0 2,ricciAtEquator 1 2⟩

def axialFormulaData : Mixed.AxialVector Fraction :=
  let m := X 3
  let s := axialEinstein Q (X 0) (X 2) m (rInv 1) (hInv 1) axialTimeInput axialRadiusInput
  ⟨m*s.time,m*s.radius⟩

end SchwarzschildEinstein.PureOdd.Master
