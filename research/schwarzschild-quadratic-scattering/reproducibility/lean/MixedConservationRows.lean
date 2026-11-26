import MixedProgram
import MixedTensorFormulas

/-! The radial rows for the mixed axial conservation balance. The angular
row is the equatorial Ricci coefficient C. Its contribution to the
balance is -(ell+1)/ell times C in the reference axial convention. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

section
variable {K : Type u} [NatCast K] [Add K] [Sub K] [Mul K] [Div K] [Neg K] [Pow K Nat]
local instance (n : Nat) : OfNat K n := ⟨Nat.cast n⟩

def evaluateAngular (C : Rat → K) (r k ell : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) (val : Linear K → K) : K :=
  angularRicciCoefficient C r (1/r) (lapse r) (r/(r-2)) k ell
    (mapJet val T) (mapJet val P) (mapPolarJets val E)

def interpolateAngular (C : Rat → K) (r k ell : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) : Quadratic K :=
  let sample := evaluateAngular C r k ell T P E
  recoverRow (sample Prod.fst) (sample (fun p => p.1+p.2)) (sample Prod.snd)

def reconstructedAngular (C : Rat → K) (dr : K → K) (r k ell : K) : Quadratic K :=
  interpolateAngular C r k ell (parentJet dr r k ell (timeAmplitude r))
    (parentJet dr r k ell (radiusAmplitude r k)) (polarReconstruction dr r k ell)

def conservationRows (C : Rat → K) (dr : K → K) (r k ell : K) : Quadratic K :=
  let f := lapse r
  let vector := reconstructedVector C dr r k ell
  let angular := reconstructedAngular C dr r k ell
  let radial := rowDerivative dr r k ell (scale (r*r*f) vector.radius)
  let temporal := scale (2*k*r*r/f) vector.time
  let tensor := scale (-((ell+1)/ell)) angular
  plus radial (plus temporal tensor)

end

open SchwarzschildMixtures.ExactRational

def conservationCoefficients : Quadratic Formula :=
  conservationRows rationalConstant Formula.dr .radius .frequency .angular

end SchwarzschildEinstein.PureOdd.Mixed
