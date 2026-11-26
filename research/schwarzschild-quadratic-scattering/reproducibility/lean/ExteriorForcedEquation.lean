import ExteriorRowEquation

/-! Bind the realized operator to the two admitted fields and the
exact regularized source, and justify integration at finite cutoffs. -/
namespace SchwarzschildMixtures.Strain

open Set MeasureTheory Filter
open scoped Topology
open SchwarzschildLaurent SchwarzschildLaurent.Exterior SchwarzschildLaurent.Outgoing

noncomputable section

def exteriorParticularJet (second : Bool) (n : ℕ) (k : ℂ) (u du : ℝ → ℂ) : ℝ → ℂ :=
  waveRowValue (unscaledStep ((n:ℂ)*(n+1)) k (unscaledRow (admittedField second k n))) u du

/-- The actual particular field solves the actual checked source
equation throughout the real exterior. -/
theorem admitted_exterior_forced_equation (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (u du : ℝ → ℂ)
    (parent : RadialEquation radiusLapse (rwPotential k ((n:ℂ)*(n+1))) 0 u du) :
    RadialEquation radiusLapse (rwPotential (2*k) (2*(n:ℂ)*(2*n+1))) (exteriorSource second n k u du)
      (radialParticular second n k u du) (exteriorParticularJet second n k u du) := by
  let L := (n:ℂ)*(n+1)
  let M := 2*(n:ℂ)*(2*n+1)
  let p := unscaledRow (admittedField second k n)
  let s := unscaledRow (admittedSource second k n)
  have good (r : ℝ) (hr : 2 < r) := admitted_rows_regular_exterior second n hn k hk ki r hr
  have law : unscaledOperator L M k p = s := by
    change unscaledOperator L M k (unscaledRow (admittedField second k n)) = _
    rw [← unscaled_operator_correct,admitted_field_solves second n hn k hk ki]
  have eq := unscaled_forced_radial_equation L M k p s u du parent
    (fun r hr => (good r hr).1.unscaled.regular) law
  constructor
  · intro r hr
    have near : radialParticular second n k u du =ᶠ[𝓝 r] waveRowValue p u du := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact (particular_from_unscaled_row second n k u du x (good x hx).1).symm
    exact (eq.value r hr).congr_of_eventuallyEq near
  · intro r hr
    obtain ⟨hp,hs⟩ := good r hr
    have jet := eq.jet r hr
    change HasDerivAt (exteriorParticularJet second n k u du)
      ((rwPotential (2*k) M r*waveRowValue (unscaledRow (admittedField second k n)) u du r+
          waveRowValue (unscaledRow (admittedSource second k n)) u du r)/radiusLapse r) r at jet
    rw [particular_from_unscaled_row second n k u du r hp,source_from_unscaled_row second n k u du r hs] at jet
    exact jet

theorem exterior_source_continuous (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (u du : ℝ → ℂ)
    (parent : RadialEquation radiusLapse (rwPotential k ((n:ℂ)*(n+1))) 0 u du) :
    ContinuousOn (exteriorSource second n k u du) (Ioi (2:ℝ)) := by
  let p := admittedSource second k n
  have good (r : ℝ) (hr : 2 < r) := (admitted_rows_regular_exterior second n hn k hk ki r hr).2
  have a : ContinuousOn (radialEval p.1) (Ioi (2:ℝ)) := fun r hr =>
    (radial_eval_derivative (good r hr).1).continuousAt.continuousWithinAt
  have b : ContinuousOn (radialEval p.2.1) (Ioi (2:ℝ)) := fun r hr =>
    (radial_eval_derivative (good r hr).2.1).continuousAt.continuousWithinAt
  have c : ContinuousOn (radialEval p.2.2) (Ioi (2:ℝ)) := fun r hr =>
    (radial_eval_derivative (good r hr).2.2).continuousAt.continuousWithinAt
  have h : ContinuousOn u (Ioi (2:ℝ)) := fun r hr => (parent.value r hr).continuousAt.continuousWithinAt
  have dh : ContinuousOn du (Ioi (2:ℝ)) := fun r hr => (parent.jet r hr).continuousAt.continuousWithinAt
  have coe : ContinuousOn (fun r : ℝ => (r : ℂ)) (Ioi (2:ℝ)) := Complex.continuous_ofReal.continuousOn
  have z := (coe.pow 2).mul dh
  exact ((a.mul (h.pow 2)).add ((b.mul h).mul z)).add (c.mul (z.pow 2))

theorem exterior_source_interval_integrable (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (j dj u : ℝ → ℂ)
    (parent : RadialEquation radiusLapse (rwPotential k ((n:ℂ)*(n+1))) 0 j dj)
    (daughter : ContinuousOn u (Ioi (2:ℝ))) {l r : ℝ} (hl : 2 < l) (hr : 2 < r) :
    IntervalIntegrable (fun x => u x*exteriorSource second n k j dj x/radiusLapse x) volume l r := by
  have coe : ContinuousOn (fun x : ℝ => (x : ℂ)) (Ioi (2:ℝ)) :=
    Complex.continuous_ofReal.continuousOn
  have radius0 (x : ℝ) (hx : x ∈ Ioi (2:ℝ)) : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 by linarith [show 2 < x from hx])
  have lapse : ContinuousOn radiusLapse (Ioi (2:ℝ)) :=
    (coe.sub continuousOn_const).div coe radius0
  have source := exterior_source_continuous second n hn k hk ki j dj parent
  have integrand := (daughter.mul source).div lapse (fun _ h => exterior_lapse_nonzero h)
  have subset : uIcc l r ⊆ Ioi (2:ℝ) := fun _ hx => (lt_min hl hr).trans_le hx.1
  exact (integrand.mono subset).intervalIntegrable

#print axioms admitted_exterior_forced_equation
#print axioms exterior_source_continuous
#print axioms exterior_source_interval_integrable

end
end SchwarzschildMixtures.Strain
