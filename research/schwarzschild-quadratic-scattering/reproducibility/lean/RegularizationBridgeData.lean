import MixtureCoefficientData

/-! Integer numerator comparisons for the two admitted fields and the
pure-odd shift. All fields share the same radial denominator, with the
second field carrying the additional factor (7ℓ-1)^2. -/
namespace SchwarzschildMixtures.Regularization

open NumeratorData

local infixl:65 " +ₚ " => Expr.add
local infixl:65 " -ₚ " => Expr.sub
local infixl:70 " *ₚ " => Expr.mul

def addData (a b : ExprRow) : ExprRow :=
  (a.1 +ₚ b.1, a.2.1 +ₚ b.2.1, a.2.2 +ₚ b.2.2)

def natural (m : Nat) : Expr := c (Int.ofNat m)

def gammaNumerator : Expr := (l -ₚ c 1) *ₚ l *ₚ (l +ₚ c 1) *ₚ (l +ₚ c 2)

def ratioNumerator : Expr :=
  (c 9 *ₚ l *ₚ l +ₚ l -ₚ c 4) *ₚ (gammaNumerator -ₚ c 12 *ₚ w)

def ratioDenominator : Expr :=
  l *ₚ (c 7 *ₚ l -ₚ c 1) *ₚ (gammaNumerator +ₚ c 12 *ₚ w)

def secondFactor : Expr := (c 7 *ₚ l -ₚ c 1) *ₚ (c 7 *ₚ l -ₚ c 1)

def baseComparison (published bare regulator : ExprRow) (mp mb mu : Nat) : ExprRow × ExprRow :=
  (scaleData (natural (mb*mu)) published,
    addData (scaleData (natural (mp*mu)) bare) (scaleData (natural (mp*mb)) regulator))

def secondComparison (published first difference ee eo oo : ExprRow)
    (mp mf md mu : Nat) : ExprRow × ExprRow :=
  let n := ratioNumerator
  let d := ratioDenominator
  let d2 := d *ₚ d
  let regulators := addData (scaleData d2 ee)
    (addData (scaleData (n *ₚ d) eo) (scaleData (n *ₚ n) oo))
  (scaleData (natural (mf*md*mu) *ₚ d2) published,
    addData (scaleData (natural (mp*md*mu) *ₚ secondFactor *ₚ d2) first)
      (addData (scaleData (natural (mp*mf*mu) *ₚ (n -ₚ d) *ₚ d) difference)
        (scaleData (natural (mp*mf*md) *ₚ secondFactor) regulators)))

abbrev RowCheck (pair : ExprRow × ExprRow) : Prop :=
  Expr.Check pair.1.1 pair.2.1 ∧
    Expr.Check pair.1.2.1 pair.2.2.1 ∧
    Expr.Check pair.1.2.2 pair.2.2.2

end SchwarzschildMixtures.Regularization
