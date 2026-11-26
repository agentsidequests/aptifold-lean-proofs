import PureOddFormulas

/-! Polar parent jets and the mixed axial vector of the daughter.
The vector uses the reference `-hatX` harmonic. Each component is a
radial coefficient after the daughter carrier has been factored out. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

structure PolarParentJets (K : Type u) where
  tt : RadialJet K
  tr : RadialJet K
  rr : RadialJet K
  sphere : RadialJet K

structure AxialVector (K : Type u) where
  time : K
  radius : K

def vectorCoefficients {K : Type u} [Add K] [Neg K] [Mul K]
    (C : Rat → K) (r invR f invF k ell : K) (T P : RadialJet K)
    (even : PolarParentJets K) : AxialVector K :=
  let A := even.tt
  let B := even.tr.val
  let H := even.rr
  let U := even.sphere
  let q := T.first+k*P.val
  let dq := T.second+k*P.first
  let R2 := invR*invR
  let R4 := R2*R2
  let f2 := f*f
  let L := ell*(ell+C 1)
  let D := ell*(ell+ -(C 1))
  let e := ell*(ell+ -(C 3))
  let t := q*(A.first + -(f2*H.first) + -(C 2*k*B))
    + -(C 2*f2*H.val*dq)
    + C 2*f*D*R2*P.val*B
    + -(f*R2*H.val*(C 2*(T.first+k*(C 2*r+ -(C 3))*P.val)+(L+C 8*invR)*T.val))
    + -(C 4*invR*T.val*A.first)
    + -(invF*R2*A.val*(C 2*q+(e+ -(C 8*invR))*T.val))
    + R2*U.val*(-(C 2*k*k*invF*T.val) + (C 4*L+ -(C 8*invR))*R2*T.val
      + -(C 2*k*f*(P.first+C 2*invR*P.val)))
    + C 4*R4*T.val*U.first
  let z := invF*R2*(L+C 4*invR)*P.val*A.val
    + C 3*k*invF*invF*A.val*(C 2*invR*T.val+ -q)
    + f*R2*(e+ -(C 4)+ -(C 4*invR))*P.val*H.val
    + k*H.val*(q+ -(C 2*invR*T.val))
    + -(C 2*B*(dq+C 4*k*invR*P.val+invF*R2*(D+ -(C 2*f))*T.val))
    + -(C 2*invR*P.val*(A.first+f2*H.first))
    + R2*(C 4*k*invF*T.val*U.first + -(C 2*k*invF*(T.first+C 2*invR*T.val)*U.val)
      + C 2*f*P.val*U.second)
    + C 4*R4*P.val*((L+ -(C 1))*U.val+U.first)
  ⟨C (1/8)*t, C (1/8)*z⟩

end SchwarzschildEinstein.PureOdd.Mixed
