import ParityMasterRadial
import ParityReconstructionData

/-! Local sourced reconstruction in Regge–Wheeler gauge.
See Hopper and Evans, arXiv:1006.4907, Eqs. (5.5), (5.15).
Here the source is covariant and the Fourier rate is minus w. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

local notation "f" => radialLapse

def sphereFromMaster (r m e tt : K) : K :=
  let lam := modeLambda m
  let pole := lam*r+3
  let A := (lam*(lam+1)*r^2+3*lam*r+6)/(r^2*pole)
  f r*D e + A*e - 2*r^3/(m*(m+1)*pole)*tt

def crossFromMaster (r w m e tt tr : K) : K :=
  let lam := modeLambda m
  let pole := lam*r+3
  let B := (lam*r^2-3*lam*r-3)/(r^2*f r*pole)
  let vacuum := -(w*r)*(D e+B*e)
  vacuum+2*r^2/(m*(m+1))*(tr+r^2*w/(pole*f r)*tt)

def reconstructPolar (r w m e : K) (s : ModeSource K) : PolarAmplitudes K :=
  let pole := modeLambda m*r+3
  let scalar := sphereFromMaster D r m e s.polar.tt
  let rr := (m*(m+1)*pole/(2*r^2)*e-pole/r*scalar+r*f r*D scalar)/(f r)^2
  ⟨(f r)^2*rr+2*f r*s.polar.traceFree,
    crossFromMaster D r w m e s.polar.tt s.tr, rr, r^2*scalar⟩

def reconstructAxial (r w m o : K) (s : Mixed.AxialVector K) : Mixed.AxialVector K :=
  let mu := (m-1)*(m+2)
  ⟨f r/2*D (r*o)+2*r^2/mu*s.time,
    -(w*r)/(2*f r)*o + 2*r^2/mu*s.radius⟩

def radialModeEinstein (r w m : K) (P : PolarAmplitudes K) (A : Mixed.AxialVector K) : ModeSource K :=
  modeEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2))
    ⟨Mixed.radialJet D P.tt,Mixed.radialJet D P.tr,Mixed.radialJet D P.rr,Mixed.radialJet D P.sphere⟩
    (Mixed.radialJet D A.time) (Mixed.radialJet D A.radius)

end
end SchwarzschildEinstein.PureOdd.Master
