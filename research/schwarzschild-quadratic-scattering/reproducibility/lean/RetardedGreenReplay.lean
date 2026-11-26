import RetardedGreenFunction
import RetardedScattering

/-! Match the full retarded Green integral to each actual quadratic
source and its previously checked unique exterior field. -/
namespace SchwarzschildMixtures.Strain

open Filter Set SchwarzschildLaurent.Outgoing SchwarzschildLaurent.LinearWave
open SchwarzschildMixtures.OutgoingData
open scoped Topology

noncomputable section

theorem admitted_retarded_green_field (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
        Nonempty (EvenParentData n k a j) ∧ j.incoming = parentAlpha k n ∧ u.incoming ≠ 0 ∧
        ∀ (second : Bool) (r : ℝ), 2 < r →
          let c := (parentAlpha k n)^2*endpointIncoming second k n/u.incoming
          let p := radialParticular second n k j.value j.jet r-c*u.value r
          let dp := exteriorParticularJet second n k j.value j.jet r-c*u.jet r
          let S := exteriorSource second n k j.value j.jet
          Tendsto (greenCutoff u.value u.jet (u.outgoingCombination ∘ u.value)
            (u.outgoingCombination ∘ u.jet) S (2*(2*k)) r)
            ((𝓝[>] (2 : ℝ)) ×ˢ atTop) (𝓝 (p,dp)) := by
  obtain ⟨a,j,u,even,incident,uin,solves⟩ := admitted_retarded_scattering n hn k hk ki
  refine ⟨a,j,u,even,incident,uin,?_⟩
  intro second r hr
  have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  obtain ⟨eq,_,boundary,_,_⟩ := solves second
  have ⟨outEq,_,_⟩ := outgoing_partner (2*k) (2*n) wk wi u
  have inside : ContinuousOn u.value (Ioi (2 : ℝ)) := fun x hx =>
    (u.equation.value x hx).continuousAt.continuousWithinAt
  have outside : ContinuousOn (u.outgoingCombination ∘ u.value) (Ioi (2 : ℝ)) := fun x hx =>
    (outEq.value x hx).continuousAt.continuousWithinAt
  have integrable (b : ℝ → ℂ) (continuous : ContinuousOn b (Ioi (2 : ℝ)))
      (l r : ℝ) (hl : 2 < l) (hr' : 2 < r) :=
    exterior_source_interval_integrable second n hn k hk ki j.value j.jet b j.equation continuous hl hr'
  exact retarded_green_field_limit (2*k) (2*n) wk wi u eq boundary
    (integrable u.value inside) (integrable (u.outgoingCombination ∘ u.value) outside) hr

#print axioms admitted_retarded_green_field

end
end SchwarzschildMixtures.Strain
