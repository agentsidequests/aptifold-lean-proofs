import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddAngularSquare : Vacuum.zeroCertificate (conservationProgram false).2.2.1 := by
  have syntax_eq : (conservationProgram false).2.2.1 = f2892 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2892, h2892, by decide +kernel⟩
#print axioms zeroOddAngularSquare

end SchwarzschildEinstein.PureOdd.Master
