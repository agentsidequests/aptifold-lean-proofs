import ExteriorForcedEquation
import LinearStrainScatteringReplay

/-! The normalized outgoing strain for the actual checked source.
Both the global linear waves and the forced solution are supplied. -/
namespace SchwarzschildMixtures.Strain

open Filter Set MeasureTheory
open scoped Topology Interval
open SchwarzschildLaurent.Outgoing SchwarzschildLaurent.LinearWave

noncomputable section

/-- Both printed complex responses are the two-cutoff limits of the
normalized integrals for their actual regularized sources. -/
theorem complete_outgoing_strain (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
        Nonempty (EvenParentData n k a j) ∧ u.incoming ≠ 0 ∧
        ∀ second : Bool,
          RadialEquation radiusLapse (rwPotential (2*k) (angularEigenvalue (2*n)))
            (exteriorSource second n k j.value j.jet)
            (radialParticular second n k j.value j.jet)
            (exteriorParticularJet second n k j.value j.jet) ∧
          (∀ l r : ℝ, 2 < l → 2 < r →
            IntervalIntegrable (fun x => u.value x*exteriorSource second n k j.value j.jet x/radiusLapse x)
              volume l r) ∧
          Tendsto (fun lr : ℝ × ℝ =>
            strainScale second k n *
              ((∫ r in lr.1..lr.2, u.value r*exteriorSource second n k j.value j.jet r/radiusLapse r)/
                (4*k*u.incoming)))
            ((𝓝[>] (2 : ℝ)) ×ˢ atTop)
            (𝓝 (printedResponse second k n j.outgoing (u.outgoing/u.incoming))) := by
  obtain ⟨a,j,u,even,u0,response⟩ := outgoing_strain_with_global_waves n hn k hk ki
  have daughter : ContinuousOn u.value (Ioi (2:ℝ)) := fun r hr =>
    (u.equation.value r hr).continuousAt.continuousWithinAt
  refine ⟨a,j,u,even,u0,?_⟩
  intro second
  have forced := admitted_exterior_forced_equation second n hn k hk ki j.value j.jet j.equation
  have pot := congrArg (rwPotential (2*k)) (angular_eigenvalue_double n)
  rw [← pot] at forced
  have finite : ∀ l r : ℝ, 2 < l → 2 < r →
      IntervalIntegrable (fun x => u.value x*exteriorSource second n k j.value j.jet x/radiusLapse x) volume l r :=
    fun _ _ hl hr => exterior_source_interval_integrable second n hn k hk ki
      j.value j.jet u.value j.equation daughter hl hr
  exact ⟨forced,finite,response second _ _ forced finite⟩

#print axioms complete_outgoing_strain

end
end SchwarzschildMixtures.Strain
