import Init

/-! The pure-odd source formulas are shared between the field proof and
the arithmetic certificate. The symbols and their denominators are bound
to the Schwarzschild radial operator by the soundness proof. -/
namespace SchwarzschildEinstein.PureOdd

universe u v
variable {K : Type u}

/-- The first two radial derivatives of a radial amplitude. -/
structure RadialJet (K : Type u) where
  val : K
  first : K
  second : K

/-- The radial coefficients needed by the even daughter equation. -/
structure EvenSource (K : Type u) where
  tt : K
  rr : K
  radialVector : K
  sphereTrace : K
  traceFree : K

variable [NatCast K] [Add K] [Sub K] [Mul K] [Div K] [Neg K] [Pow K Nat]

local instance (n : Nat) : OfNat K n := ⟨Nat.cast n⟩

/-- Coefficients before using the parent wave equation. This expression
keeps radial derivatives of both axial amplitudes independent. -/
def compactTT (r k ell : K) (T P : RadialJet K) : K :=
    -(r-2)*ell^2*(r^4*k^2-5*r^2*ell^2-4*r^2*ell+r^2+10*r*ell^2+8*r*ell-26*r+48)*P.val^2/(4*r^7)
    + (r-2)*ell^2*(2*k*T.val*P.first+2*T.val*T.second+T.first^2)/(4*r^3)
    + (r-2)*ell^2*(k*T.val*P.val-T.val*T.first)/r^4
    + 2*ell^2*(r-2)^3*P.val*P.first/r^6
    - 3*(ell-1)*(ell+1)*ell^2*T.val^2/(4*r^4)

def compactRR (r k ell : K) (T P : RadialJet K) : K :=
    -(3*r^3*k^2+3*r*ell^2+r-6*ell^2-2)*ell^2*P.val^2/(4*(r-2)*r^4)
    + ell^2*(2*k*T.val*P.first-4*k*T.first*P.val+2*T.val*T.second-T.first^2)/(4*r*(r-2))
    - ell^2*(k*T.val*P.val+T.val*T.first)/((r-2)*r^2)
    + (5*r*ell^2+4*r*ell+3*r+8)*ell^2*T.val^2/(4*(r-2)^2*r^3)

def compactRadialVector (r k ell : K) (T P : RadialJet K) : K :=
    ell*(ell+1)*k*T.val*P.val/(2*r*(r-2))
    + ell*(3*ell+1)*T.val*T.first/(4*r*(r-2))
    - ell*(ell-1)*(r-2)*P.val*P.first/(4*r^3)
    - ell*(2*r*ell+r-3*ell-2)*T.val^2/(2*r^2*(r-2)^2)
    + ell*(r*ell-2*ell+1)*P.val^2/(2*r^4)

def compactSphereTrace (r k ell : K) (T P : RadialJet K) : K :=
    -(4*r^4*k^2+r^2*ell^2+2*r^2*ell-r^2-2*r*ell^2-4*r*ell+10*r-12)*ell^2*P.val^2/(4*r^4)
    - ell^2*(3*k*T.val*P.first+k*T.first*P.val+T.val*T.second+T.first^2)/2
    + (r-1)*ell^2*T.val*T.first/(r*(r-2))
    - (r-2)*(r-1)*ell^2*P.val*P.first/r^3
    - 2*k*ell^2*T.val*P.val/(r*(r-2))
    + (r^2*ell^2+2*r^2*ell-r^2-2*r*ell^2-4*r*ell+2*r-4)*ell^2*T.val^2/(4*r^2*(r-2)^2)

def compactTraceFree (r k ell : K) (T P : RadialJet K) : K :=
    (ell/(2*ell-1)) *
      ((r^3*k^2-2*r*ell^2-2*r*ell+2*r+4*ell^2+4*ell-4)*P.val^2/(4*r^3)
      + (2*k*T.first*P.val+T.first^2)/4
      - (k*T.val*P.val+T.val*T.first)/r
      + (r*ell^2+r*ell+r-4)*T.val^2/(2*(r-2)*r^2))

abbrev Linear (K : Type u) := K × K
abbrev Quadratic (K : Type u) := K × K × K

def lapse (r : K) : K := (r-2)/r
def parentPotential (r ell : K) : K := lapse r*(ell*(ell+1)/r^2-6/r^3)

/-- In the basis J, Z = r² f J', the radial derivatives are
J' = u Z and Z' = v J + w Z. -/
def jetU (r : K) : K := 1/(r^2*lapse r)
def jetV (r k ell : K) : K := r^2*(k^2+parentPotential r ell)/lapse r
def jetW (r : K) : K := 2/r

def linearDerivative (dr : K → K) (r k ell : K) (p : Linear K) : Linear K :=
  let (a,b) := p
  (dr a+b*jetV r k ell, dr b+a*jetU r+b*jetW r)

def rowDerivative (dr : K → K) (r k ell : K) (p : Quadratic K) : Quadratic K :=
  let (a,b,c) := p
  (dr a+b*jetV r k ell,
   dr b+2*a*jetU r+b*jetW r+2*c*jetV r k ell,
   dr c+b*jetU r+2*c*jetW r)

def parentJet (dr : K → K) (r k ell : K) (p : Linear K) : RadialJet (Linear K) :=
  let first := linearDerivative dr r k ell p
  ⟨p, first, linearDerivative dr r k ell first⟩

def timeAmplitude (r : K) : Linear K := (lapse r/2, 1/(2*r))
def radiusAmplitude (r k : K) : Linear K := (-(k*r)/(2*lapse r), 0)

def mapJet {A : Type u} {B : Type v} (f : A → B) (j : RadialJet A) : RadialJet B :=
  ⟨f j.val, f j.first, f j.second⟩

def mapRow {A : Type u} {B : Type v} (f : A → B) (p : Quadratic A) : Quadratic B :=
  (f p.1, f p.2.1, f p.2.2)

def rows (cmp : RadialJet K → RadialJet K → K)
    (T P : RadialJet (Linear K)) : Quadratic K :=
  let a := cmp (mapJet Prod.fst T) (mapJet Prod.fst P)
  let c := cmp (mapJet Prod.snd T) (mapJet Prod.snd P)
  let combine : Linear K → K := fun v => v.1+v.2
  let sum := cmp (mapJet combine T) (mapJet combine P)
  (a, sum-a-c,c)

def sourceRows (dr : K → K) (r k ell : K) : EvenSource (Quadratic K) :=
  let T := parentJet dr r k ell (timeAmplitude r)
  let P := parentJet dr r k ell (radiusAmplitude r k)
  ⟨rows (compactTT r k ell) T P,
   rows (compactRR r k ell) T P,
   rows (compactRadialVector r k ell) T P,
   rows (compactSphereTrace r k ell) T P,
   rows (compactTraceFree r k ell) T P⟩

def scale (a : K) (p : Quadratic K) : Quadratic K := mapRow (fun b => a*b) p
def plus (p q : Quadratic K) : Quadratic K := (p.1+q.1,p.2.1+q.2.1,p.2.2+q.2.2)
def minus (p q : Quadratic K) : Quadratic K := (p.1-q.1,p.2.1-q.2.1,p.2.2-q.2.2)

def evenMaster (dr : K → K) (r k ell : K) (s : EvenSource (Quadratic K)) : Quadratic K :=
  let L := 2*ell
  let L2 := L*(L+1)
  let mu := (L-1)*(L+2)
  let cap := mu+6/r
  let f := lapse r
  let bullet := plus (scale (-(1/(2*f))) s.tt) (scale (f/2) s.rr)
  let inside := plus (scale (24*f^2/cap) s.rr)
    (plus (scale (-(4*r^2*f)) (rowDerivative dr r k ell bullet))
      (plus (scale (4*f/r) s.sphereTrace)
        (scale (2*r/cap*(mu*(mu-2)+12*(mu-3)/r+84/r^2)) bullet)))
  scale f (plus (scale (8*f/cap) s.radialVector)
    (plus (scale (-(2/r)) s.traceFree) (scale (2/(L2*cap)) inside)))

def projectedMaster (dr : K → K) (r k ell : K) (s : EvenSource (Quadratic K)) : Quadratic K :=
  let L := 2*ell
  let lam := (L-1)*(L+2)/2
  let gamma := lam*(lam+1)/3
  let W := gamma+3*lapse r/(r*(lam*r+3))
  let even := evenMaster dr r k ell s
  let dEven := rowDerivative dr r k ell even
  scale (1/(gamma-2*k)) (minus (scale W even) (scale (lapse r) dEven))

def bareForcing (dr : K → K) (r k ell : K) : Quadratic K :=
  projectedMaster dr r k ell (sourceRows dr r k ell)

end SchwarzschildEinstein.PureOdd
