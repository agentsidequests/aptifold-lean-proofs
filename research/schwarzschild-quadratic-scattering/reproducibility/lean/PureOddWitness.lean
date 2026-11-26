import PureOddWitness15

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000

def coefficients : Fraction × Fraction × Fraction := (p674,p706,p716)

theorem a_reduced : Reduced PureOddProgram.coefficients.1 coefficients.1 := h674
theorem b_reduced : Reduced PureOddProgram.coefficients.2.1 coefficients.2.1 := h706
theorem c_reduced : Reduced PureOddProgram.coefficients.2.2 coefficients.2.2 := h716

#print axioms a_reduced
#print axioms b_reduced
#print axioms c_reduced

end SchwarzschildMixtures.PureOddWitness
