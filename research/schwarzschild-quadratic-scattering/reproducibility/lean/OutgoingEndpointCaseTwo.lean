import AdmittedMixtureCase2
import OutgoingEndpointData

namespace SchwarzschildMixtures.OutgoingData

open NumeratorData

set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem second_cap_a : withinRadialCap 18 Case2.field.1 = true := by decide +kernel
theorem second_cap_b : withinRadialCap 16 Case2.field.2.1 = true := by decide +kernel
theorem second_cap_c : withinRadialCap 14 Case2.field.2.2 = true := by decide +kernel

theorem second_mixed_lead : Expr.Check (mixedLead Case2.field) (c 0) := by decide +kernel
theorem second_mixed_next : Expr.Check (mixedNext Case2.field) (c 0) := by decide +kernel
theorem second_outgoing_lead :
    Expr.Check (factorGapTimes (outgoingLead Case2.field)) (secondOutgoing Case2.multiplier) := by decide +kernel
theorem second_incoming_lead :
    Expr.Check (factorGapTimes (incomingLead Case2.field)) (secondIncoming Case2.multiplier) := by decide +kernel

#print axioms second_cap_a
#print axioms second_cap_b
#print axioms second_cap_c
#print axioms second_mixed_lead
#print axioms second_mixed_next
#print axioms second_outgoing_lead
#print axioms second_incoming_lead

end SchwarzschildMixtures.OutgoingData
