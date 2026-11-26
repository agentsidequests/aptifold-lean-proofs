import MixtureCoefficientData

/-! Syntax and normalization certificates for the three-variable rational
calculation. Arithmetic witnesses are checked with the existing packed
polynomial equality test. -/
namespace SchwarzschildMixtures.ExactRational

inductive Formula where
  | integer (z : Int)
  | radius
  | frequency
  | angular
  | add (a b : Formula)
  | neg (a : Formula)
  | mul (a b : Formula)
  | div (a b : Formula)
  | dr (a : Formula)
  deriving BEq, Hashable

namespace Formula
instance : NatCast Formula := ⟨fun n => .integer n⟩
instance : Add Formula := ⟨.add⟩
instance : Neg Formula := ⟨.neg⟩
instance : Sub Formula := ⟨fun a b => .add a (.neg b)⟩
instance : Mul Formula := ⟨.mul⟩
instance : Div Formula := ⟨.div⟩
def power (a : Formula) : Nat → Formula
  | 0 => .integer 1
  | n+1 => if n = 0 then a else (power a n).mul a
instance : Pow Formula Nat := ⟨power⟩
end Formula

structure Fraction where
  num : Expr
  den : Expr

namespace Fraction

def polynomial (p : Expr) : Fraction := ⟨p, Expr.constant 1⟩

def add (a b : Fraction) : Fraction :=
  ⟨.add (.mul a.num b.den) (.mul b.num a.den), .mul a.den b.den⟩
def neg (a : Fraction) : Fraction := ⟨.neg a.num, a.den⟩
def mul (a b : Fraction) : Fraction := ⟨.mul a.num b.num, .mul a.den b.den⟩
def div (a b : Fraction) : Fraction := ⟨.mul a.num b.den, .mul a.den b.num⟩
def dr (a : Fraction) : Fraction :=
  ⟨Expr.sub (.mul a.num.derivative a.den) (.mul a.num a.den.derivative), .mul a.den a.den⟩

end Fraction

inductive Factor where
  | integer (z : Int)
  | radius
  | horizon
  | angular
  | angularPlus
  | twiceMinus
  | twicePlus
  | daughterPole
  | daughterGap
  | parentPole
  | parentGap
  | sevenMinus

def Factor.data : Factor → Expr
  | .integer z => Expr.constant z
  | .radius => NumeratorData.x 1
  | .horizon => NumeratorData.xh
  | .angular => NumeratorData.l
  | .angularPlus => .add NumeratorData.l (Expr.constant 1)
  | .twiceMinus => Expr.sub NumeratorData.u (Expr.constant 1)
  | .twicePlus => .add NumeratorData.u (Expr.constant 1)
  | .daughterPole => NumeratorData.sparseDaughterPole
  | .daughterGap =>
      let e := NumeratorData.l
      let j := NumeratorData.u
      Expr.sub (.mul (.mul (.mul e (.add e (Expr.constant 1))) (Expr.sub j (Expr.constant 1)))
        (.add j (Expr.constant 1))) (.mul (Expr.constant 6) NumeratorData.w)
  | .parentPole => NumeratorData.sparseParentPole
  | .parentGap =>
      let e := NumeratorData.l
      .add (.mul (.mul (.mul (Expr.sub e (.constant 1)) e) (.add e (.constant 1)))
        (.add e (.constant 2))) (.mul (.constant 12) NumeratorData.w)
  | .sevenMinus => Expr.sub (.mul (.constant 7) NumeratorData.l) (.constant 1)

def Factor.valid : Factor → Bool
  | .integer z => z != 0
  | _ => true

def factorProduct (xs : List Factor) : Expr :=
  xs.foldr (fun factor product => .mul factor.data product) (Expr.constant 1)

/-- Both sides were divided by the same polynomial. This also certifies
nonvanishing of the reduced denominator wherever the original is defined. -/
structure Cancellation (raw out : Fraction) : Type where
  quotient : Expr
  numerator : Expr.Check (.mul out.num quotient) raw.num
  denominator : Expr.Check (.mul out.den quotient) raw.den

inductive Reduced : Formula → Fraction → Prop where
  | integer (z : Int) : Reduced (.integer z) (Fraction.polynomial (Expr.constant z))
  | radius : Reduced .radius (Fraction.polynomial (NumeratorData.x 1))
  | frequency : Reduced .frequency (Fraction.polynomial Expr.frequency)
  | angular : Reduced .angular (Fraction.polynomial Expr.angular)
  | add {a b p q out} : Reduced a p → Reduced b q →
      Cancellation (p.add q) out → Reduced (.add a b) out
  | neg {a p} : Reduced a p → Reduced (.neg a) p.neg
  | mul {a b p q out} : Reduced a p → Reduced b q →
      Cancellation (p.mul q) out → Reduced (.mul a b) out
  | div {a b p q out} : Reduced a p → Reduced b q →
      (factors : List Factor) → factors.all Factor.valid = true →
      Expr.Check q.num (factorProduct factors) →
      Cancellation (p.div q) out → Reduced (.div a b) out
  | dr {a p out} : Reduced a p →
      Cancellation p.dr out → Reduced (.dr a) out

end SchwarzschildMixtures.ExactRational
