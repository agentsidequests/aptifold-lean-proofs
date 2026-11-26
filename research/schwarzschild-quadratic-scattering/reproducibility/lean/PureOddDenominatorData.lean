import ArchivedOddData
import ExactRationalData

/-! The same denominator used by the archived row link, expressed in
the certificate's polynomial data type. -/
namespace SchwarzschildMixtures.PureOddProgram

open NumeratorData ArchivedOddData ExactRational

local infixl:65 " +ₚ " => Expr.add
local infixl:65 " -ₚ " => Expr.sub
local infixl:70 " *ₚ " => Expr.mul

def matrixDenominatorData : Expr :=
  c SchwarzschildMatrix.sourceScale *ₚ (u +ₚ c 1) *ₚ (u -ₚ c 1) *ₚ (l +ₚ c 1) *ₚ
    Expr.neg Factor.daughterGap.data *ₚ x 6

def sourceDenominatorData (m : Nat) : Expr := padding m *ₚ matrixDenominatorData

end SchwarzschildMixtures.PureOddProgram
