import OddCase

/-! Exact endpoint checks for the published pure-odd projected source. -/
namespace SchwarzschildMixtures.OddCase

open NumeratorData

set_option maxRecDepth 12000
set_option maxHeartbeats 10000000

def radialLabelsAtMost (p : Expr) (degree : Nat) : Bool :=
  match p with
  | .bands rows => rows.all fun band => decide (band.radial ≤ degree)
  | _ => false

theorem sourceA_degree : radialLabelsAtMost sourceA 24 = true := by decide +kernel
theorem sourceB_degree : radialLabelsAtMost sourceB 22 = true := by decide +kernel
theorem sourceC_degree : radialLabelsAtMost sourceC 20 = true := by decide +kernel

theorem sourceA_horizon : Expr.Check (Expr.atHorizon sourceA) (Expr.constant 0) := by decide +kernel
theorem sourceB_horizon : Expr.Check (Expr.atHorizon sourceB) (Expr.constant 0) := by decide +kernel
theorem sourceC_horizon : Expr.Check (Expr.atHorizon sourceC) (Expr.constant 0) := by decide +kernel

theorem source_ingoing_slope_horizon : Expr.Check (horizonData
    (Expr.derivative sourceA,Expr.derivative sourceB,Expr.derivative sourceC)) (Expr.constant 0) := by
  decide +kernel

#print axioms sourceA_degree
#print axioms sourceB_degree
#print axioms sourceC_degree
#print axioms sourceA_horizon
#print axioms sourceB_horizon
#print axioms sourceC_horizon
#print axioms source_ingoing_slope_horizon

end SchwarzschildMixtures.OddCase
