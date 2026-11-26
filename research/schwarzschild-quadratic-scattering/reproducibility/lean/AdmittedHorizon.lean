import AdmittedMixtures
import HorizonRadialEnvelope

/-! Apply the analytic cancellation to both exact regularized daughter fields. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent MeromorphicRadial Horizon

noncomputable section

/-- The two admitted regularized scalar fields have holomorphic radial
envelopes at the future horizon on an analytic ingoing parent. -/
theorem admitted_horizon_extension (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (H : ℂ → ℂ) (hH : AnalyticAt ℂ H 2) :
    ∃ (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 2),
      evaluateEnvelope (admittedField second k n) (ofFunction H hH.meromorphicAt)
        (ofFunction (envelopeJet k H) (envelope_jet_analytic k hH).meromorphicAt) =
          ofFunction G hG.meromorphicAt := by
  obtain ⟨a,b,c,ha,hb,hc,eq⟩ := admitted_horizon_residue second n hn k hk ki
  exact analytic_of_simple_pole_cancellation _ k H hH ha hb hc eq

#print axioms admitted_horizon_extension

end
end SchwarzschildMixtures
