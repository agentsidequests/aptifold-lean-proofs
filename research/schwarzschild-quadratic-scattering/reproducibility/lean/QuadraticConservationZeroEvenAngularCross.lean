import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenAngularCross : Vacuum.zeroCertificate (conservationProgram true).2.2.2.1 := by
  have syntax_eq : (conservationProgram true).2.2.2.1 = f2120 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2120, h2120, by decide +kernel⟩
#print axioms zeroEvenAngularCross

end SchwarzschildEinstein.PureOdd.Master
