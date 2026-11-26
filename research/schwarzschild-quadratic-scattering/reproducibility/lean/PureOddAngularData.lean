import CoordinateJetTypes
import Init.Data.Rat

/-! Executable sparse fractions and the finite quadratic Ricci
calculation. This module and its closed certificates need only Lean's
core evaluator. The interpretation proofs live in the geometry replay. -/
namespace SchwarzschildEinstein.PureOdd

namespace AngularArithmetic

abbrev Powers := List Nat
abbrev Polynomial := List (Powers × Rat)

def addPowers : Powers → Powers → Powers
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::addPowers p q

def Polynomial.insert (w : Powers) (a : Rat) : Polynomial → Polynomial
  | [] => if a = 0 then [] else [(w,a)]
  | (v,b)::ps =>
    if w = v then
      if a+b = 0 then ps else (v,a+b)::ps
    else (v,b)::insert w a ps

def Polynomial.merge : Nat → Polynomial → Polynomial → Polynomial
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, (u,a)::p, (v,b)::q =>
    if u = v then
      if a+b = 0 then merge n p q else (u,a+b)::merge n p q
    else if compare u v = .lt then (u,a)::merge n p ((v,b)::q)
    else (v,b)::merge n ((u,a)::p) q

def Polynomial.add (p q : Polynomial) : Polynomial := merge (p.length+q.length) p q

def Polynomial.neg (p : Polynomial) : Polynomial :=
  p.map fun (w,a) => (w,-a)

def Polynomial.shift (w : Powers) (a : Rat) (p : Polynomial) : Polynomial :=
  p.map fun (v,b) => (addPowers w v,a*b)

def Polynomial.convolve (p q : Polynomial) : Polynomial :=
  p.foldr (fun (w,a) ps => (shift w a q).add ps) []

def Polynomial.mul : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | _, [] => []
  | [(w,a)], q => shift w a q
  | p, [(w,a)] => shift w a p
  | p, q => convolve p q

def Polynomial.constant (a : Rat) : Polynomial := insert [] a []
def variablePowers : Nat → Powers
  | 0 => [1]
  | i+1 => 0::variablePowers i
def Polynomial.indeterminate (i : Nat) : Polynomial := [(variablePowers i,1)]

def Polynomial.power (p : Polynomial) : Nat → Polynomial
  | 0 => constant 1
  | n+1 => (power p n).mul p

structure Denominator where
  radius : Nat
  horizon : Nat
  angular : Nat
  deriving DecidableEq

def Denominator.add (d e : Denominator) : Denominator :=
  ⟨d.radius+e.radius, d.horizon+e.horizon, d.angular+e.angular⟩

def Denominator.join (d e : Denominator) : Denominator :=
  ⟨max d.radius e.radius, max d.horizon e.horizon, max d.angular e.angular⟩

def Denominator.extra (d e : Denominator) : Denominator :=
  ⟨e.radius-d.radius, e.horizon-d.horizon, e.angular-d.angular⟩

def Denominator.poly (d : Denominator) : Polynomial :=
  let r := Polynomial.indeterminate 0
  let c := Polynomial.indeterminate 1
  let h := r.add (Polynomial.constant (-2))
  let s := (Polynomial.constant 1).add (c.mul c).neg
  ((r.power d.radius).mul (h.power d.horizon)).mul (s.power d.angular)

def Denominator.scale (d : Denominator) (p : Polynomial) : Polynomial :=
  if d.radius = 0 ∧ d.horizon = 0 ∧ d.angular = 0 then p else p.mul d.poly

structure Fraction where
  num : Polynomial
  den : Denominator
  deriving DecidableEq

def Fraction.constant (a : Rat) : Fraction := ⟨Polynomial.constant a, ⟨0,0,0⟩⟩
def Fraction.indeterminate (i : Nat) : Fraction := ⟨Polynomial.indeterminate i, ⟨0,0,0⟩⟩
def Fraction.inverse (d : Denominator) : Fraction := ⟨Polynomial.constant 1, d⟩

instance : Zero Fraction := ⟨Fraction.constant 0⟩
def Fraction.addNonempty (a b : Fraction) : Fraction :=
  let d := a.den.join b.den
  ⟨((a.den.extra d).scale a.num).add ((b.den.extra d).scale b.num),d⟩

instance : Add Fraction := ⟨fun a b =>
  if a.num = [] then b else if b.num = [] then a else a.addNonempty b⟩
instance : Neg Fraction := ⟨fun a => ⟨a.num.neg,a.den⟩⟩
instance : Mul Fraction := ⟨fun a b =>
  if a.num = [] then a else if b.num = [] then b else ⟨a.num.mul b.num,a.den.add b.den⟩⟩

end AngularArithmetic

namespace AngularCalculation

universe u

variable {S : Type u} [Zero S] [Add S] [Neg S] [Mul S]

def sumFour (f : Axis → S) : S := f 0 + f 1 + f 2 + f 3

def firstConstant (a : S) : FirstJet S := ⟨a, fun _ => 0⟩
def firstAdd (u v : FirstJet S) : FirstJet S :=
  ⟨u.value+v.value, fun i => u.gradient i+v.gradient i⟩
def firstNeg (u : FirstJet S) : FirstJet S :=
  ⟨-u.value, fun i => -u.gradient i⟩
def firstMul (u v : FirstJet S) : FirstJet S :=
  ⟨u.value*v.value, fun i => u.gradient i*v.value+u.value*v.gradient i⟩
def firstSum (f : Axis → FirstJet S) : FirstJet S :=
  ⟨sumFour fun i => (f i).value, fun a => sumFour fun i => (f i).gradient a⟩
def secondNeg (u : SecondJet S) : SecondJet S :=
  ⟨firstNeg u.toFirstJet, fun i j => -(u.second i j)⟩
def secondMul (u v : SecondJet S) : SecondJet S :=
  ⟨firstMul u.toFirstJet v.toFirstJet,
    fun i j => u.second i j*v.value+u.gradient j*v.gradient i+
      u.gradient i*v.gradient j+u.value*v.second i j⟩

def axisJet (i : Axis) (a b c : S) : SecondJet S :=
  ⟨⟨a, fun x => if x = i then b else 0⟩, fun x y => if x = i ∧ y = i then c else 0⟩

def derivative (u : SecondJet S) (i : Axis) : FirstJet S :=
  ⟨u.gradient i, fun j => u.second j i⟩

def metricDerivative (g : SecondMetric S) (a b c : Axis) : FirstJet S :=
  firstAdd (firstAdd (derivative (g a c) b) (derivative (g a b) c))
    (firstNeg (derivative (g b c) a))

def christoffel (half : S) (B : FirstMetric S) (g : SecondMetric S) :
    (Axis → Axis → Axis → FirstJet S) :=
  fun a b c => firstMul (firstConstant half) (firstSum fun j =>
    firstMul (B a j) (metricDerivative g j b c))

def christoffelDiag (half : S) (B : Axis → FirstJet S) (g : SecondMetric S) :
    Axis → Axis → Axis → FirstJet S :=
  fun a b c => firstMul (firstConstant half) (firstMul (B a) (metricDerivative g a b c))

def connectionAdd (g h : (Axis → Axis → Axis → FirstJet S)) : (Axis → Axis → Axis → FirstJet S) :=
  fun i j k => firstAdd (g i j k) (h i j k)

def product (g h : (Axis → Axis → Axis → FirstJet S)) (a b : Axis) : S :=
  sumFour fun c => sumFour fun j =>
    (g c c j).value*(h j a b).value + -((g c b j).value*(h j a c).value)

def divergence (G : (Axis → Axis → Axis → FirstJet S)) (a b : Axis) : S :=
  sumFour fun i => (G i a b).gradient i + -(G i a i).gradient b

def matNeg (A : FirstMetric S) : FirstMetric S := fun i j => firstNeg (A i j)

def inverseOne (B : Axis → FirstJet S) (h : FirstMetric S) : FirstMetric S :=
  fun i j => firstMul (firstMul (B i) (h i j)) (B j)

def inverseTwo (B : Axis → FirstJet S) (h : FirstMetric S) : FirstMetric S :=
  fun i j => firstMul (firstSum fun a => firstMul (inverseOne B h i a) (h a j)) (B j)

def ricciParts (half : S) (g : SecondMetric S) (B : Axis → FirstJet S) (H : SecondMetric S)
    (a b : Axis) : Axis → S :=
  let h : FirstMetric S := fun i j => (H i j).toFirstJet
  let BhB := inverseOne B h
  let G₀ := christoffelDiag half B g
  let G₁ := connectionAdd (christoffelDiag half B H) (christoffel half (matNeg BhB) g)
  let G₂ := connectionAdd (christoffel half (matNeg BhB) H)
    (christoffel half (inverseTwo B h) g)
  fun i =>
    if i = 0 then divergence G₂ a b
    else if i = 1 then product G₀ G₂ a b
    else if i = 2 then product G₁ G₁ a b
    else product G₂ G₀ a b

def ricci (half : S) (g : SecondMetric S) (B : Axis → FirstJet S) (H : SecondMetric S)
    (a b : Axis) : S :=
  let parts := ricciParts half g B H a b
  parts 0 + (parts 1 + parts 2 + parts 3)

end AngularCalculation

open AngularArithmetic AngularCalculation

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

def rInv (n : Nat) : Fraction := Fraction.inverse ⟨n,0,0⟩
def hInv (n : Nat) : Fraction := Fraction.inverse ⟨0,n,0⟩

def sin2 (c : Fraction) : Fraction := Q 1 + -(c*c)

def affineBackground (c : Fraction) : SecondMetric Fraction :=
  let r := X 0
  let h := r + -(Q 2)
  let s := sin2 c
  let radius := axisJet 1 (r*r) (Q 2*r) (Q 2)
  fun a b =>
    if a ≠ b then axisJet 2 0 0 0
    else if a = 0 then axisJet 1 (-(h*rInv 1)) (-(Q 2*rInv 2)) (Q 4*rInv 3)
    else if a = 1 then axisJet 1 (r*hInv 1) (-(Q 2*hInv 2)) (Q 4*hInv 3)
    else if a = 2 then secondMul radius (axisJet 2 s (Q 2*(c + -(Q 1))*s)
      ((Q 4*c*c + -(Q 10*c) + Q 6 + -(Q 2*s))*s))
    else secondMul radius (axisJet 2 (-s) (-(Q 2*c*s)) (-(Q 2*(Q 2*c*c + -c + -s)*s)))

def affineInverse (c inverseSine : Fraction) : Axis → FirstJet Fraction :=
  let r := X 0
  let h := r + -(Q 2)
  let radius := axisJet 1 (rInv 2) (-(Q 2*rInv 3)) 0
  fun a =>
    if a = 0 then (axisJet 1 (-(r*hInv 1)) (Q 2*hInv 2) 0).toFirstJet
    else if a = 1 then (axisJet 1 (h*rInv 1) (Q 2*rInv 2) 0).toFirstJet
    else if a = 2 then (secondMul radius (axisJet 2 inverseSine
      (-(Q 2*(c + -(Q 1))*inverseSine)) 0)).toFirstJet
    else (secondMul radius (axisJet 2 (-inverseSine) (Q 2*c*inverseSine) 0)).toFirstJet

def affineCarrier (c : Fraction) : SecondJet Fraction :=
  let ell := X 3
  let rate : Axis → Fraction := fun a =>
    if a = 0 then -(X 2) else if a = 3 then ell else if a = 2 then ell*c else 0
  ⟨⟨Q 1, rate⟩, fun a b => rate a*rate b + -(if a = 2 ∧ b = 2 then ell*(sin2 c+c) else 0)⟩

def affineParent (c : Fraction) : SecondMetric Fraction :=
  let ell := X 3
  let T := axisJet 1 (X 4) (X 5) (X 6)
  let P := axisJet 1 (X 7) (X 8) (X 9)
  let Y := affineCarrier c
  let v := secondMul Y (axisJet 2 ell (-ell) (Q 2*ell))
  let q := secondMul Y (axisJet 2 (ell*c) (-(ell*sin2 c)) (ell*(Q 1 + -(Q 2*c))*sin2 c))
  fun a b =>
    if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then secondNeg (secondMul T v)
    else if (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) then secondNeg (secondMul T q)
    else if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then secondNeg (secondMul P v)
    else if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then secondNeg (secondMul P q)
    else axisJet 2 0 0 0

def angularRicciFractions (c inverseSine : Fraction) : Axis → Axis → Fraction :=
  AngularCalculation.ricci (Q (1/2)) (affineBackground c) (affineInverse c inverseSine) (affineParent c)

def angularRicciParts (c inverseSine : Fraction) (a b : Axis) : Axis → Fraction :=
  AngularCalculation.ricciParts (Q (1/2)) (affineBackground c) (affineInverse c inverseSine)
    (affineParent c) a b

theorem angularFractionsFromParts (c u : Fraction) (a b : Axis) :
    angularRicciFractions c u a b =
      let parts := angularRicciParts c u a b
      parts 0 + (parts 1 + parts 2 + parts 3) := rfl

theorem angularCombineParts (c u : Fraction) (a b : Axis)
    (w x y z : Fraction)
    (hw : angularRicciParts c u a b 0 = w)
    (hx : angularRicciParts c u a b 1 = x)
    (hy : angularRicciParts c u a b 2 = y)
    (hz : angularRicciParts c u a b 3 = z) :
    angularRicciFractions c u a b = w + (x+y+z) := by
  rewrite [angularFractionsFromParts]
  dsimp only
  rw [hw,hx,hy,hz]

theorem angularResidualCongr {a b w x : Fraction} (left : a = w) (right : b = x)
    (zero : (w + -x).num = []) : (a + -b).num = [] := by
  subst a
  subst b
  exact zero

def daughterShape {S : Type u} [Add S] [Neg S] [Mul S]
    (one half c : S) (E : (Axis → Axis → S)) : (Axis → Axis → S) :=
  let C := half*(E 2 2 + -(E 3 3))
  let B := half*(E 2 2 + E 3 3)
  let s := one + -(c*c)
  let z := one + c*c
  fun a b =>
    if a = 2 ∧ b = 2 then s*C+z*B
    else if a = 3 ∧ b = 3 then -(s*C)+z*B
    else if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then (c+c)*B
    else if a = 2 then c*E b 3
    else if b = 2 then c*E a 3
    else if a = 3 then E b 3
    else if a = 1 ∧ b = 0 then E 0 1
    else E a b

def atAngle : (Axis → Axis → Fraction) :=
  angularRicciFractions (Fraction.indeterminate 1) (Fraction.inverse ⟨0,0,1⟩)

def onEquator : (Axis → Axis → Fraction) :=
  angularRicciFractions (Fraction.constant 0) (Fraction.constant 1)

def reconstructed : (Axis → Axis → Fraction) :=
  daughterShape (Fraction.constant 1) (Fraction.constant (1/2)) (Fraction.indeterminate 1) onEquator

end SchwarzschildEinstein.PureOdd
