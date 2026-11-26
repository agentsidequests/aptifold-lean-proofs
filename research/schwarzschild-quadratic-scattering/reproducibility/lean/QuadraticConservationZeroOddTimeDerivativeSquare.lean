import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddTimeDerivativeSquare : Vacuum.zeroCertificate (conservationProgram false).1.2.2 := by
  have syntax_eq : (conservationProgram false).1.2.2 = f2500 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2500, h2500, by decide +kernel⟩
#print axioms zeroOddTimeDerivativeSquare

end SchwarzschildEinstein.PureOdd.Master
