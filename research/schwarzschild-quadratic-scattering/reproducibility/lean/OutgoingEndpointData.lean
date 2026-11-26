import MixtureCoefficientData

/-! The two leading reciprocal coefficients of the actual field rows.
The caps \(18,16,14\) account for \(Z=r^2 D J\) in the three terms. -/
namespace SchwarzschildMixtures.OutgoingData

open NumeratorData

local infixl:65 " +ₚ " => Expr.add
local infixl:65 " -ₚ " => Expr.sub
local infixl:70 " *ₚ " => Expr.mul

def withinRadialCap (n : Nat) : Expr → Bool
  | .bands rows => rows.all (fun b => decide (b.radial ≤ n))
  | _ => false

def coefficientAt (n : Nat) : Expr → Expr
  | .bands rows => .bands ((rows.filter (fun b => b.radial == n)).map fun b => {b with radial := 0})
  | _ => c 0

def topA (p : ExprRow) := coefficientAt 18 p.1
def topB (p : ExprRow) := coefficientAt 16 p.2.1
def topC (p : ExprRow) := coefficientAt 14 p.2.2

def outgoingLead (p : ExprRow) := topA p +ₚ w *ₚ topB p +ₚ w *ₚ w *ₚ topC p
def incomingLead (p : ExprRow) := topA p -ₚ w *ₚ topB p +ₚ w *ₚ w *ₚ topC p
def mixedLead (p : ExprRow) := topA p -ₚ w *ₚ w *ₚ topC p
def mixedNext (p : ExprRow) := coefficientAt 17 p.1 -ₚ w *ₚ w *ₚ coefficientAt 13 p.2.2

def square (p : Expr) := p *ₚ p
def fifth (p : Expr) := p *ₚ p *ₚ p *ₚ p *ₚ p

def parityPolynomial := c 20 *ₚ l *ₚ l *ₚ l +ₚ c 35 *ₚ l *ₚ l +ₚ l -ₚ c 8
def factorNumerator := parityPolynomial *ₚ square l *ₚ square (l -ₚ c 1) *ₚ (l +ₚ c 1) *ₚ (l +ₚ c 2)
def factorDenominator := c 288 *ₚ (u -ₚ c 1)

def gammaTwelve := (l -ₚ c 1) *ₚ l *ₚ (l +ₚ c 1) *ₚ (l +ₚ c 2)
def daughterSix := (u -ₚ c 1) *ₚ l *ₚ (u +ₚ c 1) *ₚ (l +ₚ c 1)
def gammaGapTwelve := c 2 *ₚ daughterSix -ₚ gammaTwelve

/-- Leading common denominator with the \((12k+12g)^2\) and
\(6k-6\Gamma\) factors kept outside. -/
def denominatorBase (multiplier : Nat) (second : Bool) :=
  c multiplier *ₚ l *ₚ square (l -ₚ c 1) *ₚ square (l +ₚ c 2) *ₚ (u +ₚ c 1) *ₚ
    fifth (l +ₚ c 1) *ₚ fifth (u -ₚ c 1) *ₚ square w *ₚ
    fifth ((l -ₚ c 1) *ₚ (l +ₚ c 2)) *ₚ (u -ₚ c 1) *ₚ (l +ₚ c 1) *ₚ
    (if second then square (c 7 *ₚ l -ₚ c 1) else c 1)

def firstIncoming (m : Nat) :=
  Expr.neg (c 864 *ₚ factorNumerator *ₚ square w *ₚ denominatorBase m false)

def secondOutgoing (m : Nat) :=
  c 144 *ₚ factorNumerator *ₚ w *ₚ (c 24 *ₚ daughterSix *ₚ w -ₚ square gammaTwelve) *ₚ
    denominatorBase m true *ₚ (c 6 *ₚ w -ₚ daughterSix)

def secondIncoming (m : Nat) :=
  Expr.neg (c 144 *ₚ factorNumerator *ₚ daughterSix *ₚ w *ₚ square (gammaTwelve -ₚ c 12 *ₚ w) *ₚ
    denominatorBase m true)

def factorTimes (p : Expr) := factorDenominator *ₚ p
def factorGapTimes (p : Expr) := factorDenominator *ₚ square gammaGapTwelve *ₚ p

end SchwarzschildMixtures.OutgoingData
