import MixtureCoefficientData
import MatrixCertificateData

/-! Put the matrix's Laurent source coefficients over the same denominator
as the regularized odd source. The matrix table supplies the remainder. -/
namespace SchwarzschildMixtures
namespace ArchivedOddData

open NumeratorData

local infixl:65 " +ₚ " => Expr.add
local infixl:65 " -ₚ " => Expr.sub
local infixl:70 " *ₚ " => Expr.mul

def tableLabel (i : Nat) : Nat × Int :=
  (SchwarzschildMatrix.rowLabels[i]?).getD (0, 0)

def tableTerms (j i : Nat) : Poly :=
  let label := tableLabel i
  if label.1 = j then
    ((SchwarzschildMatrix.clearedSource[i]?).getD []).map fun m =>
      ⟨(label.2 + 6).toNat, m.1, m.2.1, m.2.2⟩
  else []

def tableComponent (j : Nat) : Expr :=
  .coefficients (List.ofFn fun i : Fin 41 => tableTerms j i.val)

def tableNumerators : ExprRow := (tableComponent 0, tableComponent 1, tableComponent 2)

def power (p : Expr) : Nat → Expr
  | 0 => c 1
  | n+1 => power p n *ₚ p

def parentFrequency := c 12 *ₚ w +ₚ ((l -ₚ c 1) *ₚ l *ₚ (l +ₚ c 1) *ₚ (l +ₚ c 2))

/-- The ratio of the operator denominator to the matrix's denominator,
which already contains r⁶, the daughter frequency and one angular factor. -/
def padding (multiplier : Nat) : Expr :=
  c (Int.ofNat multiplier) *ₚ l *ₚ power (l -ₚ c 1) 2 *ₚ power (l +ₚ c 2) 2 *ₚ
    power (l +ₚ c 1) 4 *ₚ power (u -ₚ c 1) 4 *ₚ power w 2 *ₚ power parentFrequency 2 *ₚ
    x 9 *ₚ xh *ₚ power sparseParentPole 7 *ₚ power sparseDaughterPole 3

def restoredNumerators (multiplier : Nat) (field : ExprRow) : ExprRow :=
  let applied := sourceData field
  let remainder := scaleData (padding multiplier) tableNumerators
  (applied.1 +ₚ remainder.1, applied.2.1 +ₚ remainder.2.1, applied.2.2 +ₚ remainder.2.2)

end ArchivedOddData
end SchwarzschildMixtures
