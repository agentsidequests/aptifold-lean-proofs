import QuadraticConservationRows
import EvenProgram

namespace SchwarzschildEinstein.PureOdd.Master

open SchwarzschildMixtures.ExactRational

def conservationProgram (even : Bool) : Quadratic Formula × Quadratic Formula × Quadratic Formula :=
  let q := Mixed.rationalConstant
  let r := Formula.radius
  let w := Formula.frequency
  let ell := Formula.angular
  let s := if even then evenParentSourceRows q Formula.dr r w ell else oddParentSourceRows q Formula.dr r w ell
  polarConservationRows q Formula.dr r w ell s

private def flatten (v : Quadratic Formula × Quadratic Formula × Quadratic Formula) : List Formula :=
  [v.1,v.2.1,v.2.2].flatMap fun p => [p.1,p.2.1,p.2.2]

set_option maxHeartbeats 0 in
#eval do
  let (roots, operations) := Polar.exportFormulaList (flatten (conservationProgram true) ++
    flatten (conservationProgram false))
  for operation in operations do
    IO.println operation
  IO.println ("outputs " ++ String.intercalate " " (roots.map toString))

end SchwarzschildEinstein.PureOdd.Master
