import ParityMasterData
import CoordinateJetTypes

/-! Source and metric coefficients in one highest-weight harmonic.
The axial sign and the sphere amplitude agree with ParityMasterData. -/
namespace SchwarzschildEinstein.PureOdd.Master

structure ModeSource (K : Type u) where
  polar : EvenSource K
  tr : K
  timeVector : K
  axial : Mixed.AxialVector K
  axialTensor : K

structure PolarAmplitudes (K : Type u) where
  tt : K
  tr : K
  rr : K
  sphere : K

def modeEinstein {S : Type u} [Add S] [Neg S] [Mul S]
    (q : Rat → S) (r w m ri hi : S) (E : Mixed.PolarParentJets S)
    (T P : RadialJet S) : ModeSource S :=
  let f := (r+ -(q 2))*ri
  let ri2 := ri*ri
  let K := ri2*E.sphere.val
  let Kp := ri2*E.sphere.first + -(q 2*ri*K)
  let tr := q (1/2)*m*(m+q 1)*ri2*E.tr.val + -(w*f*ri*E.rr.val) +
    w*Kp + w*(r+ -(q 3))*ri*hi*K
  let timeVector := ri2*E.tr.val + q (1/2)*(f*E.tr.first+f*w*E.rr.val+w*K)
  let axial := axialEinstein q r w m ri hi T P
  let axialTensor := w*r*hi*T.val + q 2*ri2*P.val + f*P.first
  ⟨polarEinstein q r w m ri hi E,tr,timeVector,⟨-axial.time,-axial.radius⟩,axialTensor⟩

/-- Tensor divided by the common mode carrier, in the scaled chart.
The orbit components, vector and angular terms share this convention. -/
def modeTensor {S : Type u} [Zero S] [Add S] [Neg S] [Mul S]
    (q : Rat → S) (m c : S) (source : ModeSource S) (a b : Axis) : S :=
  let s := source.polar
  let sinSq := q 1 + -(c*c)
  let norm := m*(m+ -(q 1))
  let diagonal := q (1/2)*norm*(q 1+c*c)
  let cross := norm*c
  let shape := diagonal*s.traceFree + -(cross*source.axialTensor)
  match a.val, b.val with
  | 0, 0 => s.tt
  | 0, 1 | 1, 0 => source.tr
  | 1, 1 => s.rr
  | 0, 2 | 2, 0 => m*(c*source.timeVector + -source.axial.time)
  | 0, 3 | 3, 0 => m*(source.timeVector + -(c*source.axial.time))
  | 1, 2 | 2, 1 => m*(c*s.radialVector + -source.axial.radius)
  | 1, 3 | 3, 1 => m*(s.radialVector + -(c*source.axial.radius))
  | 2, 2 => sinSq*s.sphereTrace+shape
  | 3, 3 => -(sinSq*s.sphereTrace)+shape
  | 2, 3 | 3, 2 => cross*s.traceFree + -(diagonal*source.axialTensor)
  | _, _ => 0

end SchwarzschildEinstein.PureOdd.Master
