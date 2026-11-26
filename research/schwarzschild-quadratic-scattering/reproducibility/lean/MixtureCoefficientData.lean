import Init

/-! Coefficient data and integer checks. Keeping this module free of
Mathlib imports lets the kernel check the large inputs in a small process. -/

namespace SchwarzschildMixtures

structure Term where
  radial : Nat
  frequency : Nat
  angular : Nat
  coefficient : Int

def Term.multiply (a b : Term) : Term :=
  ⟨a.radial + b.radial, a.frequency + b.frequency, a.angular + b.angular,
    a.coefficient * b.coefficient⟩

def Term.index (t : Term) : Nat := 1024*t.radial + 64*t.frequency + t.angular

abbrev Poly := List Term

namespace Poly

def single (a : Int) (r k ell : Nat) : Poly := [⟨r, k, ell, a⟩]

def neg (p : Poly) : Poly := p.map fun t => {t with coefficient := -t.coefficient}

def derivative : Poly → Poly
  | [] => []
  | ⟨0, _, _, _⟩::p => derivative p
  | ⟨r+1, k, ell, a⟩::p => ⟨r, k, ell, a * (r+1 : Nat)⟩ :: derivative p

def mass (p : Poly) : Nat := (p.map (fun t => t.coefficient.natAbs)).sum

def powerOfBase (bits index : Nat) : Int := ((1 : Nat) <<< (bits * index) : Nat)

def lowIndex : Poly → Nat
  | [] => 0
  | [t] => t.index
  | t::u::ts => min t.index (lowIndex (u::ts))

def encodeRelative (bits anchor : Nat) : Poly → Int
  | [] => 0
  | t::p => t.coefficient * powerOfBase bits (t.index-anchor) + encodeRelative bits anchor p

def encodeBlock (bits : Nat) (p : Poly) : Int :=
  let low := lowIndex p
  powerOfBase bits low * encodeRelative bits low p

end Poly

/-- One angular polynomial at fixed radius and frequency powers. Positive
and negative digits are stored separately in base 2^112. -/
structure CoefficientBand where
  radial : Nat
  frequency : Nat
  count : Nat
  positive : Nat
  negative : Nat
  weight : Nat := 1

namespace CoefficientBand

def base : Nat := 2^112

def digits (r k weight : Nat) : Nat → Nat → Nat → Nat → Poly
  | 0, _, _, _ => []
  | n+1, i, positive, negative =>
    let digit : Int := (↑(positive % base) : Int) - ↑(negative % base)
    ⟨r, k, i, weight * digit⟩ :: digits r k weight n (i+1) (positive/base) (negative/base)

def terms (g : CoefficientBand) : Poly :=
  digits g.radial g.frequency g.weight g.count 0
    (g.positive % base^g.count) (g.negative % base^g.count)

def encode (g : CoefficientBand) : Int :=
  g.weight * ((↑(g.positive % base^g.count) : Int) - ↑(g.negative % base^g.count)) *
    Poly.powerOfBase 112 (1024*g.radial + 64*g.frequency)

def derivative (g : CoefficientBand) : Option CoefficientBand :=
  match g.radial with
  | 0 => none
  | r+1 => some {g with radial := r, weight := g.weight*(r+1)}

def atHorizon (g : CoefficientBand) : CoefficientBand :=
  {g with radial := 0, weight := g.weight * 2^g.radial}

end CoefficientBand

inductive Expr where
  | coefficients (blocks : List Poly)
  | bands (rows : List CoefficientBand)
  | add (p q : Expr)
  | neg (p : Expr)
  | mul (p q : Expr)

namespace Expr

def single (a : Int) (r k ell : Nat) : Expr := .coefficients [Poly.single a r k ell]
def constant (a : Int) : Expr := single a 0 0 0
def frequency : Expr := single 1 0 1 0
def angular : Expr := single 1 0 0 1

def sub (p q : Expr) : Expr := .add p (.neg q)

def derivative : Expr → Expr
  | .coefficients ps => .coefficients (ps.map Poly.derivative)
  | .bands rows => .bands (rows.filterMap CoefficientBand.derivative)
  | .add p q => .add (derivative p) (derivative q)
  | .neg p => .neg (derivative p)
  | .mul p q => .add (.mul (derivative p) q) (.mul p (derivative q))

def substituteTwo (p : Poly) : Poly :=
  p.map fun t => {t with radial := 0, coefficient := t.coefficient * (2:Int)^t.radial}

def atHorizon : Expr → Expr
  | .coefficients ps => .coefficients (ps.map substituteTwo)
  | .bands rows => .bands (rows.map CoefficientBand.atHorizon)
  | .add p q => .add (atHorizon p) (atHorizon q)
  | .neg p => .neg (atHorizon p)
  | .mul p q => .mul (atHorizon p) (atHorizon q)

structure Bounds where
  frequency : Nat
  angular : Nat
  mass : Nat

def mergeBounds (a b : Bounds) : Bounds :=
  ⟨max a.frequency b.frequency, max a.angular b.angular, a.mass+b.mass⟩

def multiplyBounds (a b : Bounds) : Bounds :=
  ⟨a.frequency+b.frequency, a.angular+b.angular, a.mass*b.mass⟩

def termBounds (t : Term) : Bounds := ⟨t.frequency, t.angular, t.coefficient.natAbs⟩
def boundsOfList (p : Poly) : Bounds :=
  p.foldr (mergeBounds ∘ termBounds) ⟨0,0,0⟩

def bounds : Expr → Bounds
  | .coefficients ps => ps.foldr (mergeBounds ∘ boundsOfList) ⟨0,0,0⟩
  | .bands rows => rows.foldr (mergeBounds ∘ boundsOfList ∘ CoefficientBand.terms) ⟨0,0,0⟩
  | .add p q => mergeBounds (bounds p) (bounds q)
  | .neg p => bounds p
  | .mul p q => multiplyBounds (bounds p) (bounds q)

def encode : Expr → Int
  | .coefficients ps => (ps.map (Poly.encodeBlock 112)).sum
  | .bands rows => (rows.map CoefficientBand.encode).sum
  | .add p q => encode p + encode q
  | .neg p => -encode p
  | .mul p q => encode p * encode q

abbrev Check (p q : Expr) : Prop :=
  let b := bounds (sub p q)
  b.frequency < 16 ∧ b.angular < 64 ∧ b.mass < 2^112 ∧ encode p = encode q

end Expr

abbrev ExprRow := Expr × Expr × Expr

def exprRowMap (f : Expr → Expr) (p : ExprRow) : ExprRow :=
  (f p.1, f p.2.1, f p.2.2)

namespace NumeratorData


local infixl:65 " +ₚ " => Expr.add
local infixl:65 " -ₚ " => Expr.sub
local infixl:70 " *ₚ " => Expr.mul

def c := Expr.constant
def x (degree : Nat) := Expr.single 1 degree 0 0
def w := Expr.frequency
def l := Expr.angular
def u := c 2 *ₚ l
def h := l *ₚ (l +ₚ c 1)
def hD := u *ₚ (u +ₚ c 1)
def xh := x 1 -ₚ c 2

def sparseParentPole := x 1 *ₚ ((l -ₚ c 1) *ₚ (l +ₚ c 2)) +ₚ c 6
def sparseDaughterPole := x 1 *ₚ ((u -ₚ c 1) *ₚ (l +ₚ c 1)) +ₚ c 3
def sparsePoles := sparseParentPole *ₚ sparseDaughterPole
def rate (a b d : Int) : Expr :=
  c a *ₚ xh *ₚ sparsePoles +ₚ x 1 *ₚ sparsePoles +ₚ
    (x 1 *ₚ xh) *ₚ (c b *ₚ Expr.derivative sparseParentPole *ₚ sparseDaughterPole +ₚ
      c d *ₚ sparseParentPole *ₚ Expr.derivative sparseDaughterPole)

def jetAData := x 4 *ₚ (w *ₚ w) +ₚ x 2 *ₚ h -ₚ x 1 *ₚ (c 2 *ₚ h +ₚ c 6) +ₚ c 12
def jetBData := c 2 *ₚ xh
def daughterData := c 4 *ₚ (w *ₚ w) *ₚ x 4 +ₚ xh *ₚ (hD *ₚ x 1 -ₚ c 6)

def scaleData (p : Expr) (v : ExprRow) : ExprRow := exprRowMap (Expr.mul p) v
def subData (v w : ExprRow) : ExprRow :=
  (v.1 -ₚ w.1, v.2.1 -ₚ w.2.1, v.2.2 -ₚ w.2.2)

def jetData (p : ExprRow) : ExprRow :=
  (jetAData *ₚ p.2.1,
    c 2 *ₚ p.1 +ₚ jetBData *ₚ p.2.1 +ₚ (c 2 *ₚ jetAData) *ₚ p.2.2,
    p.2.1 +ₚ (c 2 *ₚ jetBData) *ₚ p.2.2)

def stepData (a b d : Int) (p : ExprRow) : ExprRow :=
  let derivativePart := scaleData (x 1 *ₚ xh *ₚ sparsePoles) (exprRowMap Expr.derivative p)
  let jetPart := scaleData sparsePoles (jetData p)
  let logarithmicPart := scaleData (rate a b d) p
  (derivativePart.1 +ₚ jetPart.1 -ₚ logarithmicPart.1,
    derivativePart.2.1 +ₚ jetPart.2.1 -ₚ logarithmicPart.2.1,
    derivativePart.2.2 +ₚ jetPart.2.2 -ₚ logarithmicPart.2.2)

def sourceData (p : ExprRow) : ExprRow :=
  subData (stepData 13 6 2 (stepData 11 5 1 p))
    (scaleData sparsePoles (scaleData sparsePoles (scaleData daughterData p)))

end NumeratorData

export NumeratorData (sourceData)

/-- The numerator of the possible simple pole, using the ingoing limit Z/J = -4k. -/
def horizonData (p : ExprRow) : Expr :=
  Expr.add (Expr.sub (Expr.atHorizon p.1)
    (.mul (Expr.single 4 0 1 0) (Expr.atHorizon p.2.1)))
    (.mul (Expr.single 16 0 2 0) (Expr.atHorizon p.2.2))

end SchwarzschildMixtures
