import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenRadiusDerivativeSquare : Vacuum.zeroCertificate (conservationProgram true).2.1.2.2 := by
  have syntax_eq : (conservationProgram true).2.1.2.2 = f2077 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2077, h2077, by decide +kernel⟩
#print axioms zeroEvenRadiusDerivativeSquare

end SchwarzschildEinstein.PureOdd.Master
