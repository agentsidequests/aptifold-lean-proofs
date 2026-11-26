import MixedVectorFormulas

/-! The linear parent reconstruction and mixed odd master source in
the common Regge–Wheeler basis. Z is r² times the tortoise derivative
of J. The mixed source has no daughter Darboux conversion because
its daughter is already odd. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

variable {K : Type u} [NatCast K] [Add K] [Sub K] [Mul K] [Div K] [Neg K] [Pow K Nat]

local instance (n : Nat) : OfNat K n := ⟨Nat.cast n⟩

def linearAdd (u v : Linear K) : Linear K := (u.1+v.1,u.2+v.2)
def linearScale (a : K) (u : Linear K) : Linear K := (a*u.1,a*u.2)

def halfAngularEigenvalue (ell : K) : K := (ell-1)*(ell+2)/2
def parentAlgebraicFrequency (ell : K) : K :=
  let lam := halfAngularEigenvalue ell
  lam*(lam+1)/3

def parentSuperpotential (r ell : K) : K :=
  parentAlgebraicFrequency ell+3*lapse r/(r*(halfAngularEigenvalue ell*r+3))

/-- The even parent is (W J + dJ/dr*)/(g+k), with g the parent's
algebraic frequency and k the signed frequency. -/
def evenParentAmplitude (r k ell : K) : Linear K :=
  let gap := parentAlgebraicFrequency ell+k
  (parentSuperpotential r ell/gap, 1/(r^2*gap))

def evenSphereCoefficient (r ell : K) : K :=
  let lam := halfAngularEigenvalue ell
  (lam*(lam+1)*r^2+3*lam*r+6)/(r^2*(lam*r+3))

def evenCrossCoefficient (r ell : K) : K :=
  let lam := halfAngularEigenvalue ell
  (lam*r^2-3*lam*r-3)/(r^2*lapse r*(lam*r+3))

def polarReconstruction (dr : K → K) (r k ell : K) : PolarParentJets (Linear K) :=
  let f := lapse r
  let L := ell*(ell+1)
  let cap := (ell-1)*(ell+2)+6/r
  let D := linearDerivative dr r k ell
  let E := evenParentAmplitude r k ell
  let S := linearAdd (linearScale f (D E)) (linearScale (evenSphereCoefficient r ell) E)
  let radial := linearScale (1/f^2)
    (linearAdd (linearAdd (linearScale (L*cap/(4*r)) E) (linearScale (-(cap/2)) S))
      (linearScale (r*f) (D S)))
  let cross := linearScale (-(k*r)) (linearAdd (D E) (linearScale (evenCrossCoefficient r ell) E))
  let jet := parentJet dr r k ell
  ⟨jet (linearScale (f^2) radial), jet cross, jet radial, jet (linearScale (r^2) S)⟩

def mapPolarJets {A B : Type u} (g : A → B) (E : PolarParentJets A) : PolarParentJets B :=
  ⟨mapJet g E.tt, mapJet g E.tr, mapJet g E.rr, mapJet g E.sphere⟩

def radialJet (d : K → K) (u : K) : RadialJet K := ⟨u, d u, d (d u)⟩

def scalarPolarReconstruction (d : K → K) (r k ell E : K) : PolarParentJets K :=
  let f := lapse r
  let cap := (ell-1)*(ell+2)+6/r
  let S := f*d E+evenSphereCoefficient r ell*E
  let H := (1/f^2)*(ell*(ell+1)*cap/(4*r)*E+(-(cap/2))*S+r*f*d S)
  let B := -(k*r)*(d E+evenCrossCoefficient r ell*E)
  ⟨radialJet d (f^2*H),radialJet d B,radialJet d H,radialJet d (r^2*S)⟩

def evaluateVector (C : Rat → K) (r k ell : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) (val : Linear K → K) : AxialVector K :=
  vectorCoefficients C r (1/r) (lapse r) (r/(r-2)) k ell
    (mapJet val T) (mapJet val P) (mapPolarJets val E)

def vectorSamples (C : Rat → K) (r k ell : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) (J Z : K) : AxialVector K :=
  evaluateVector C r k ell T P E (fun p => p.1*J+p.2*Z)

def recoverRow (a b c : K) : Quadratic K := (a,b-a-c,c)

def interpolateVector (C : Rat → K) (r k ell : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) : AxialVector (Quadratic K) :=
  let sample := evaluateVector C r k ell T P E
  let a := sample Prod.fst
  let b := sample (fun p => p.1+p.2)
  let c := sample Prod.snd
  ⟨recoverRow a.time b.time c.time, recoverRow a.radius b.radius c.radius⟩

def reconstructedVector (C : Rat → K) (dr : K → K) (r k ell : K) :
    AxialVector (Quadratic K) :=
  interpolateVector C r k ell (parentJet dr r k ell (timeAmplitude r))
    (parentJet dr r k ell (radiusAmplitude r k)) (polarReconstruction dr r k ell)

/-- The negative of the native odd master-source coefficient after
the manuscript's reference-odd rephasing. Both cross terms of the
quadratic Einstein tensor are already present in the vector. -/
def oddMasterScale (r ell : K) : K := 4*r*lapse r/((2*ell-1)*(2*ell+2))

def mixedMaster (dr : K → K) (r k ell : K) (s : AxialVector K) : K :=
  oddMasterScale r ell*(dr s.time+2*k*s.radius)

def bareMixedRows (C : Rat → K) (dr : K → K) (r k ell : K) : Quadratic K :=
  let s := reconstructedVector C dr r k ell
  scale (oddMasterScale r ell) (plus (rowDerivative dr r k ell s.time) (scale (2*k) s.radius))

end SchwarzschildEinstein.PureOdd.Mixed
