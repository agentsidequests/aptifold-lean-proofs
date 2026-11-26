import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenAngularDerivativeSquare : Vacuum.zeroCertificate (conservationProgram true).2.2.2.2 := by
  have syntax_eq : (conservationProgram true).2.2.2.2 = f2136 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2136, h2136, by decide +kernel⟩
#print axioms zeroEvenAngularDerivativeSquare

end SchwarzschildEinstein.PureOdd.Master
