import AdmittedMixtureCase1
import OutgoingEndpointData

namespace SchwarzschildMixtures.OutgoingData

open NumeratorData

set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem first_cap_a : withinRadialCap 18 Case1.field.1 = true := by decide +kernel
theorem first_cap_b : withinRadialCap 16 Case1.field.2.1 = true := by decide +kernel
theorem first_cap_c : withinRadialCap 14 Case1.field.2.2 = true := by decide +kernel

theorem first_mixed_lead : Expr.Check (mixedLead Case1.field) (c 0) := by decide +kernel
theorem first_mixed_next : Expr.Check (mixedNext Case1.field) (c 0) := by decide +kernel
theorem first_outgoing_lead : Expr.Check (outgoingLead Case1.field) (c 0) := by decide +kernel
theorem first_incoming_lead :
    Expr.Check (factorTimes (incomingLead Case1.field)) (firstIncoming Case1.multiplier) := by decide +kernel

#print axioms first_cap_a
#print axioms first_cap_b
#print axioms first_cap_c
#print axioms first_mixed_lead
#print axioms first_mixed_next
#print axioms first_outgoing_lead
#print axioms first_incoming_lead

end SchwarzschildMixtures.OutgoingData
