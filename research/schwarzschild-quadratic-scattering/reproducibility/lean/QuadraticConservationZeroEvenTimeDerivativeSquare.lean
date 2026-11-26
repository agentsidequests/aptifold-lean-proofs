import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroEvenTimeDerivativeSquare : Vacuum.zeroCertificate (conservationProgram true).1.2.2 := by
  have syntax_eq : (conservationProgram true).1.2.2 = f1860 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p1860, h1860, by decide +kernel⟩
#print axioms zeroEvenTimeDerivativeSquare

end SchwarzschildEinstein.PureOdd.Master
