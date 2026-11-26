import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenTimeSquare : Vacuum.zeroCertificate (conservationProgram true).1.1 := by
  have syntax_eq : (conservationProgram true).1.1 = f1264 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p1264, h1264, by decide +kernel⟩
#print axioms zeroEvenTimeSquare

end SchwarzschildEinstein.PureOdd.Master
