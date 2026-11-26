import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddTimeSquare : Vacuum.zeroCertificate (conservationProgram false).1.1 := by
  have syntax_eq : (conservationProgram false).1.1 = f2374 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2374, h2374, by decide +kernel⟩
#print axioms zeroOddTimeSquare

end SchwarzschildEinstein.PureOdd.Master
