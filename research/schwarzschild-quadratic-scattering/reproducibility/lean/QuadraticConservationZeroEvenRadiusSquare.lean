import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenRadiusSquare : Vacuum.zeroCertificate (conservationProgram true).2.1.1 := by
  have syntax_eq : (conservationProgram true).2.1.1 = f1968 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p1968, h1968, by decide +kernel⟩
#print axioms zeroEvenRadiusSquare

end SchwarzschildEinstein.PureOdd.Master
