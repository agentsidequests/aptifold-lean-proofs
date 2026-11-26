import MixedVectorFormulas

/-! Equatorial linear Einstein readouts in Regge–Wheeler gauge.
The sphere entry in the input jets is r² times the usual polar K.
The angular projections on the output use the daughter label itself. -/
namespace SchwarzschildEinstein.PureOdd.Master

variable {S : Type u} [Add S] [Neg S] [Mul S]

def polarEinstein (q : Rat → S) (r w m ri hi : S) (E : Mixed.PolarParentJets S) : EvenSource S :=
  let h := r + -(q 2)
  let r2 := r*r
  let r3 := r2*r
  let f := h*ri
  let f2 := f*f
  let L := m*(m+q 1)
  let mu := L + -(q 2)
  let ri2 := ri*ri
  let hi2 := hi*hi
  let a := E.tt
  let b := E.tr
  let c := E.rr
  let s := E.sphere
  let K := ri2*s.val
  let Kp := ri2*s.first + -(q 2*ri2*ri*s.val)
  let Kpp := ri2*s.second + -(q 4*ri2*ri*s.first) + q 6*ri2*ri2*s.val
  let tt := q (1/2)*f2*ri2*ri*(r*(L+q 2)+q 4)*c.val + f2*f*ri*c.first +
    q (1/2)*mu*f*ri2*K + -(f*(q 3*r + -(q 5))*ri2*Kp) + -(f2*Kpp)
  let rr := q (1/2)*(r*L+q 4)*ri*hi2*a.val + -(hi*a.first) + -(q 2*w*hi*b.val) +
    -(ri2*c.val) + -(q (1/2)*(q 2*r3*w*w+h*mu)*ri*hi2*K) + (r+ -(q 1))*ri*hi*Kp
  let vector := -(q (1/2)*(r+ -(q 1))*hi2*a.val) + q (1/2)*r*hi*a.first +
    q (1/2)*r*w*hi*b.val + q (1/2)*(r+ -(q 1))*ri2*c.val + -(q (1/2)*Kp)
  let circ := q (1/4)*(r*h*L + -(q 4*r)+q 4)*hi2*a.val +
    -(q (1/2)*r*(r+ -(q 3))*hi*a.first) + -(q (1/2)*r2*a.second) +
    -(w*r*(r+ -(q 1))*hi*b.val) + -(w*r2*b.first) +
    -(q (1/4)*(q 2*r3*r*w*w+r*h*L+q 4*r+ -(q 4))*ri2*c.val) +
    -(q (1/2)*h*(r+ -(q 1))*ri*c.first) +
    -(q (1/2)*w*w*r3*hi*K) + (r+ -(q 1))*Kp + q (1/2)*r*h*Kpp
  let sharp := q (1/2)*(r*hi*a.val + -(f*c.val))
  ⟨tt, rr, vector, circ, sharp⟩

/-- The actual Einstein vector components divided by m. The standard
source coefficients have the opposite sign because the metric carrier
is minus the rephased axial covector. -/
def axialEinstein (q : Rat → S) (r w m ri hi : S) (T P : RadialJet S) : Mixed.AxialVector S :=
  let f := (r + -(q 2))*ri
  let L := m*(m+q 1)
  let ri2 := ri*ri
  ⟨q (1/2)*f*T.second + (q 2*ri2*ri + -(q (1/2)*L*ri2))*T.val +
      f*w*(q (1/2)*P.first+ri*P.val),
   w*hi*T.val + -(q (1/2)*w*r*hi*T.first) +
      -((q (1/2)*w*w*r*hi + q (1/2)*(L+ -(q 2))*ri2)*P.val)⟩

end SchwarzschildEinstein.PureOdd.Master
