import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenTimeCross : Vacuum.zeroCertificate (conservationProgram true).1.2.1 := by
  have syntax_eq : (conservationProgram true).1.2.1 = f1611 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p1611, h1611, by decide +kernel⟩
#print axioms zeroEvenTimeCross

end SchwarzschildEinstein.PureOdd.Master
