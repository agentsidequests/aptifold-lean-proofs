import ExactRationalData

/-! The denominator of the bare coefficient identity in the syntax
used by the exact arithmetic certificates. -/
namespace SchwarzschildMixtures.MetricBare

open NumeratorData ExactRational

local infixl:65 " +ₚ " => Expr.add
local infixl:65 " -ₚ " => Expr.sub
local infixl:70 " *ₚ " => Expr.mul

def exprPow (a : Expr) : Nat → Expr
  | 0 => c 1
  | n + 1 => exprPow a n *ₚ a

def metricScalar (multiplier : Nat) (second : Bool) : Expr :=
  c multiplier *ₚ l *ₚ exprPow (l -ₚ c 1) 2 *ₚ exprPow (l +ₚ c 2) 2 *ₚ (u +ₚ c 1) *ₚ
    exprPow (l +ₚ c 1) 5 *ₚ exprPow (u -ₚ c 1) 5 *ₚ exprPow w 2 *ₚ
    exprPow Factor.parentGap.data 2 *ₚ Expr.neg Factor.daughterGap.data *ₚ
    (if second then exprPow Factor.sevenMinus.data 2 else c 1)

def metricSourceDenominator (multiplier : Nat) (second : Bool) : Expr :=
  let step := x 2 *ₚ sparsePoles
  let q := metricScalar multiplier second *ₚ x 11 *ₚ xh *ₚ
    exprPow sparseParentPole 5 *ₚ sparseDaughterPole
  step *ₚ (step *ₚ q)

def metricSecondStep (field intermediate : ExprRow) : ExprRow :=
  subData (stepData 13 6 2 intermediate)
    (scaleData sparsePoles (scaleData sparsePoles (scaleData daughterData field)))

end SchwarzschildMixtures.MetricBare
