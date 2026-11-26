import ParityReconstructionData
import ParityMasterAngular

/-! Bind the ten radial source coefficients to every entry of the
linear Einstein tensor in the full angular chart. -/
namespace SchwarzschildEinstein.PureOdd.Master

open AngularArithmetic AngularCalculation
local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

def angularCosine : Fraction := X 1
def angularInverseSine : Fraction := Fraction.inverse ⟨0,0,1⟩

def combinedChartInput (c : Fraction) (a b : Axis) : SecondJet Fraction :=
  Mixed.addJets (Mixed.polarParent c a b) (affineParent c a b)

def modeTrace {S : Type u} [Add S] [Neg S] [Mul S] (q : Rat → S)
    (r ri hi : S) (source : ModeSource S) : S :=
  -(r*hi*source.polar.tt)+(r+ -(q 2))*ri*source.polar.rr+q 2*ri*ri*source.polar.sphereTrace

def angularRicciTerms (a b : Axis) : Fraction × Fraction × Fraction :=
  let g := affineBackground angularCosine
  let B := affineInverse angularCosine angularInverseSine
  let H := combinedChartInput angularCosine
  let half := Q (1/2)
  let background := christoffelDiag half B g
  let linear := connectionAdd (christoffelDiag half B H)
    (christoffel half (matNeg (inverseOne B (fun i j => (H i j).toFirstJet))) g)
  ⟨divergence linear a b,product background linear a b,product linear background a b⟩

def angularCoordinateRicci (a b : Axis) : Fraction :=
  let parts := angularRicciTerms a b
  parts.1 + (parts.2.1 + parts.2.2)

def modeCoefficientData : ModeSource Fraction :=
  modeEinstein Q (X 0) (X 2) (X 3) (rInv 1) (hInv 1)
    polarInputs axialTimeInput axialRadiusInput

def angularFormulaTensor (a b : Axis) : Fraction :=
  modeTensor Q (X 3) angularCosine modeCoefficientData a b

-- Undo trace reversal on the formula side so each check computes only
-- one coordinate Ricci component.
def angularFormulaRicci (a b : Axis) : Fraction :=
  let g := affineBackground angularCosine
  let trace := modeTrace Q (X 0) (rInv 1) (hInv 1) modeCoefficientData
  angularFormulaTensor a b + -(Q (1/2)*(g a b).value*trace)

end SchwarzschildEinstein.PureOdd.Master
