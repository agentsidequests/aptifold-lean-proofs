import MixedTensorFormulas
import Mathlib.Data.Rat.Cast.Defs

/-! The scalar axial coefficients of the mixed Einstein source.
These definitions are shared by the tensor projection and conservation proof. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

noncomputable section

variable {K : Type*} [DivisionRing K]

def vectorValue (r k ell : K) (T P : RadialJet K) (E : PolarParentJets K) : AxialVector K :=
  vectorCoefficients (fun q : Rat => (q : K)) r (1/r) (lapse r) (r/(r-2)) k ell T P E

def angularRicciValue (r k ell : K) (T P : RadialJet K) (E : PolarParentJets K) : K :=
  angularRicciCoefficient (fun q : Rat => (q : K)) r (1/r) (lapse r) (r/(r-2)) k ell T P E

def axialAngularCoefficient (r k ell : K) (T P : RadialJet K) (E : PolarParentJets K) : K :=
  let L := 2*ell
  2*angularRicciValue r k ell T P E/(L*(L-1))

end
end SchwarzschildEinstein.PureOdd.Mixed
