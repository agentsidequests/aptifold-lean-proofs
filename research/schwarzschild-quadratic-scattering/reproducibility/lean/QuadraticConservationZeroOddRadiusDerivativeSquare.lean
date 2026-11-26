import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddRadiusDerivativeSquare : Vacuum.zeroCertificate (conservationProgram false).2.1.2.2 := by
  have syntax_eq : (conservationProgram false).2.1.2.2 = f2849 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2849, h2849, by decide +kernel⟩
#print axioms zeroOddRadiusDerivativeSquare

end SchwarzschildEinstein.PureOdd.Master
