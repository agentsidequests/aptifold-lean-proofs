import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddAngularDerivativeSquare : Vacuum.zeroCertificate (conservationProgram false).2.2.2.2 := by
  have syntax_eq : (conservationProgram false).2.2.2.2 = f2956 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2956, h2956, by decide +kernel⟩
#print axioms zeroOddAngularDerivativeSquare

end SchwarzschildEinstein.PureOdd.Master
