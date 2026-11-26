import OddSourceEndpoint
import QuadraticSourceBounds

/-! The pure-odd source has a unique retarded Green solution even though
the rational operator exclusion applies to its local coefficient row. -/
namespace SchwarzschildMixtures.Strain

open Polynomial Filter Set MeasureTheory
open SchwarzschildLaurent SchwarzschildLaurent.Exterior SchwarzschildLaurent.Outgoing
open SchwarzschildLaurent.LinearWave
open scoped Topology

noncomputable section

def oddExteriorSource (n : ℕ) (k : ℂ) (j dj : ℝ → ℂ) : ℝ → ℂ :=
  waveRowValue (unscaledRow (publishedOdd k n)) j dj

theorem odd_exterior_source_regular (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0)
    (ki : k.re = 0) (r : ℝ) (hr : 2 < r) :
    RegularRow r (unscaledRow (publishedOdd k n)) := by
  obtain ⟨p,q,form,live,_,_,_,_,_⟩ := pure_odd_source_endpoint_data n hn k hk ki
  rw [form]
  exact RowValues.fraction p q r (live r hr.le)

theorem odd_source_radial_bounds (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (a : ℂ) (j : IngoingWaveData k (angularEigenvalue n) a) :
    let S := oddExteriorSource n k j.value j.jet
    ContinuousOn S (Ioi (2 : ℝ)) ∧
      (∃ C : ℝ, ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖S r/radiusLapse r‖ ≤ C) ∧
      (∃ C : ℝ, ∀ᶠ r in atTop, ‖S r/radiusLapse r‖ ≤ C*r^(-2 : ℝ)) := by
  dsimp only
  obtain ⟨p,q,row,live,deg,dA,dB,dC,compatibility⟩ := pure_odd_source_endpoint_data n hn k hk ki
  have qh : q.eval (2 : ℂ) ≠ 0 := by simpa only [Complex.ofReal_ofNat] using live 2 le_rfl
  have q0 : q ≠ 0 := fun h => qh (by simp [h])
  have agrees (r : ℝ) (hr : 2 < r) :
      oddExteriorSource n k j.value j.jet r = polynomialQuadraticSource p q j.value j.jet r := by
    rw [oddExteriorSource,row,polynomial_source_from_fraction _ _ _ _ _ (live r hr.le)]
  have jc : ContinuousOn j.value (Ioi (2 : ℝ)) := fun r hr =>
    (j.equation.value r hr).continuousAt.continuousWithinAt
  have djc : ContinuousOn j.jet (Ioi (2 : ℝ)) := fun r hr =>
    (j.equation.jet r hr).continuousAt.continuousWithinAt
  have c := polynomial_source_continuous p q j.value j.jet (fun r hr => live r hr.le) jc djc
  refine ⟨c.congr agrees, ?_, ?_⟩
  · obtain ⟨B,bound⟩ := polynomial_source_horizon_bound p q k _ a ki qh compatibility j
    refine ⟨B,?_⟩
    filter_upwards [bound,self_mem_nhdsWithin (s := Ioi (2 : ℝ))] with r hb hr
    rw [agrees r hr]
    exact hb
  · obtain ⟨B,bound⟩ := polynomial_source_infinity_bound p q 23 k _ a hk ki deg q0 dA dB dC j
    refine ⟨B,?_⟩
    filter_upwards [bound,eventually_gt_atTop (2 : ℝ)] with r hb hr
    rw [agrees r hr]
    exact hb

theorem pure_odd_retarded_scattering (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (a : ℂ) (j : IngoingWaveData k (angularEigenvalue n) a)
    (u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1) :
    let S := oddExteriorSource n k j.value j.jet
    let V := rwPotential (2*k) (angularEigenvalue (2*n))
    let q := (∫ x in Ioi (2 : ℝ), u.value x*S x/radiusLapse x)/((2*(2*k))*u.incoming)
    ∃ p dp : ℝ → ℂ, RadialEquation radiusLapse V S p dp ∧ RetardedBoundary (2*k) p dp q ∧
      ∀ (other dother : ℝ → ℂ) (out : ℂ), RadialEquation radiusLapse V S other dother →
        RetardedBoundary (2*k) other dother out →
        (∀ r : ℝ, 2 < r → p r = other r ∧ dp r = dother r) ∧ q = out := by
  dsimp only
  let S := oddExteriorSource n k j.value j.jet
  have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  obtain ⟨sc,sH,sI⟩ := odd_source_radial_bounds n hn k hk ki a j
  have decayed : ContinuousOn (fun r => S r/radiusLapse r) (Ioi (2 : ℝ)) := by
    simp only [div_eq_mul_inv]
    exact sc.mul inverse_lapse_continuous
  have ⟨vEq,_,_⟩ := outgoing_partner (2*k) (2*n) wk wi u
  have uc : ContinuousOn u.value (Ioi (2 : ℝ)) := fun r hr =>
    (u.equation.value r hr).continuousAt.continuousWithinAt
  have vc : ContinuousOn (u.outgoingCombination ∘ u.value) (Ioi (2 : ℝ)) := fun r hr =>
    (vEq.value r hr).continuousAt.continuousWithinAt
  obtain ⟨⟨h,hp,hb⟩,⟨i,ip,ib⟩⟩ := ingoing_wave_endpoint_bounds wk wi u
  have uH : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖u.value r‖ ≤ C :=
    ⟨h,hp,hb.mono fun _ b => b.1⟩
  have uI : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in atTop, ‖u.value r‖ ≤ C :=
    ⟨i,ip,ib.mono fun _ b => b.1⟩
  have ⟨vH,vI⟩ := outgoing_partner_endpoint_bounds wk wi u
  have inner : IntegrableOn (fun r => u.value r*S r/radiusLapse r) (Ioi (2 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_assoc] using source_weight_integrable
      u.value (fun r => S r/radiusLapse r) uc decayed uH uI sH sI
  have outer : IntegrableOn (fun r => u.outgoingCombination (u.value r)*S r/radiusLapse r) (Ioi (2 : ℝ)) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_assoc] using source_weight_integrable
      (u.outgoingCombination ∘ u.value) (fun r => S r/radiusLapse r) vc decayed vH vI sH sI
  exact retarded_green_exists (2*k) (2*n) wk wi u S sc inner outer

#print axioms odd_exterior_source_regular
#print axioms odd_source_radial_bounds
#print axioms pure_odd_retarded_scattering

end
end SchwarzschildMixtures.Strain
