import MixedVectorFormulas

/-! The two remaining polar source coefficients for an axial parent.
The sign is that of the Einstein forcing, and the time vector is
divided by the daughter mode label 2ℓ. -/
namespace SchwarzschildEinstein.PureOdd.Master

variable {S : Type u} [Add S] [Neg S] [Mul S]

def oddParentCross (q : Rat → S) (r k ell ri hi : S) (T P : RadialJet S) : S :=
  let h := r + -(q 2)
  let r2 := r*r
  let ri2 := ri*ri
  let ri3 := ri2*ri
  let a := ell+q 1
  ell*ell*(
    q (1/2)*ri3*ri2*hi*(h*(r*a*a+q 4) + -(r2*r2*k*k))*T.val*P.val +
    q (1/2)*h*ri3*(T.second*P.val+k*P.val*P.first) +
    -(h*k*ri2*ri2*P.val*P.val) +
    k*ri2*hi*T.val*T.val + -(q (1/2)*k*ri*hi*T.val*T.first))

def oddParentTimeVector (q : Rat → S) (r k ell ri hi : S) (T P : RadialJet S) : S :=
  let h := r + -(q 2)
  let ri2 := ri*ri
  let ri3 := ri2*ri
  let L := ell*(ell+q 1)
  let first := -(q (1/2)*(r+ -(q 3))*L*ri3*ri*T.val*P.val)
  first +
    q (1/4)*h*L*ri3*(T.first*P.val+T.val*P.first) +
    q (1/4)*h*k*ell*(q 3*ell+q 1)*ri3*P.val*P.val +
    -(q (1/4)*k*ell*(ell+ -(q 1))*ri*hi*T.val*T.val)

end SchwarzschildEinstein.PureOdd.Master
