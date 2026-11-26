import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenAngularSquare : Vacuum.zeroCertificate (conservationProgram true).2.2.1 := by
  have syntax_eq : (conservationProgram true).2.2.1 = f2100 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2100, h2100, by decide +kernel⟩
#print axioms zeroEvenAngularSquare

end SchwarzschildEinstein.PureOdd.Master
