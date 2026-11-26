import AngularRetardedTransport
import OddRetardedScattering

/-! Arbitrary parity profiles in the top daughter have unique retarded
solutions by combining the two closed-form responses and one Green response. -/
namespace SchwarzschildMixtures.Strain

open Polynomial Set MeasureTheory Filter
open SchwarzschildLaurent SchwarzschildLaurent.Exterior SchwarzschildLaurent.LinearWave
open SchwarzschildLaurent.Outgoing
open scoped Topology

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def angularExteriorForcing (n m : ℕ) (k : ℂ) (even odd : ℂ[X]) (j dj : ℝ → ℂ) : ℝ → ℂ :=
  waveRowValue (unscaledRow (angularSource n m k even odd)) j dj

theorem angular_exterior_three_sources (n m : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (even odd : ℂ[X]) (j dj : ℝ → ℂ) (r : ℝ) (hr : 2 < r) :
    let w := angularSourceWeights n m k even odd
    angularExteriorForcing n m k even odd j dj r =
      w.1*exteriorSource false n k j dj r+w.2.1*exteriorSource true n k j dj r+
        w.2.2*oddExteriorSource n k j dj r := by
  dsimp only
  let w := angularSourceWeights n m k even odd
  let A := unscaledRow (admittedSource false k n)
  let B := unscaledRow (admittedSource true k n)
  let C := unscaledRow (publishedOdd k n)
  have form : unscaledRow (angularSource n m k even odd) =
      plus (scale (Cᵣ w.1) A) (plus (scale (Cᵣ w.2.1) B) (scale (Cᵣ w.2.2) C)) := by
    rw [angular_source_from_three_rows]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [A,B,C,w,unscaledRow,plus,scale] <;> ring
  have ra := (admitted_rows_regular_exterior false n hn k hk ki r hr).2
  have rb := (admitted_rows_regular_exterior true n hn k hk ki r hr).2
  have rc := odd_exterior_source_regular n hn k hk ki r hr
  have a : RegularRow r A := ra.unscaled.regular
  have b : RegularRow r B := rb.unscaled.regular
  have values := (RowValues.scale (RadiusValue.const (r : ℂ) w.1) a).plus
    ((RowValues.scale (RadiusValue.const (r : ℂ) w.2.1) b).plus
      (RowValues.scale (RadiusValue.const (r : ℂ) w.2.2) rc))
  rw [angularExteriorForcing,form,← source_from_unscaled_row false n k j dj r ra,
    ← source_from_unscaled_row true n k j dj r rb]
  unfold waveRowValue
  rw [values.read_eq]
  simp only [oddExteriorSource,waveRowValue,quadraticValue,plus,scale,w,A,B]
  ring

private theorem retarded_add_scaled {w : ℂ} {u du v dv : ℝ → ℂ} {a b : ℂ} (c : ℂ)
    (uBC : RetardedBoundary w u du a) (vBC : RetardedBoundary w v dv b) :
    RetardedBoundary w (fun r => u r+c*v r) (fun r => du r+c*dv r) (a+c*b) := by
  obtain ⟨x,xH⟩ := uBC.horizon
  obtain ⟨y,yH⟩ := vBC.horizon
  constructor
  · refine ⟨x+c*y,?_⟩
    simpa only [neg_mul,sub_neg_eq_add,mul_zero,sub_zero] using radial_mode_limits_sub_scaled (-c) xH yH
  · simpa only [neg_mul,sub_neg_eq_add,mul_zero,sub_zero] using
      radial_mode_limits_sub_scaled (-c) uBC.infinity vBC.infinity

/-- A single convergent pure-odd integral supplies the missing radial
response for every polarization and azimuthal profile of the top daughter. -/
theorem general_angular_retarded_scattering (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
        j.incoming = parentAlpha k n ∧ u.incoming ≠ 0 ∧
        ∀ (even odd : ℂ[X]) (m : ℕ),
          let weights := angularSourceWeights n m k even odd
          let V := rwPotential (2*k) (angularEigenvalue (2*n))
          let S := angularExteriorForcing n m k even odd j.value j.jet
          let q₁ := boundaryResponse false k n j.outgoing (u.outgoing/u.incoming)
          let q₂ := boundaryResponse true k n j.outgoing (u.outgoing/u.incoming)
          let q₃ := (∫ r in Ioi (2 : ℝ), u.value r*oddExteriorSource n k j.value j.jet r/radiusLapse r)/
            ((2*(2*k))*u.incoming)
          let q := weights.1*q₁+weights.2.1*q₂+weights.2.2*q₃
          ∃ p dp : ℝ → ℂ, RadialEquation radiusLapse V S p dp ∧ RetardedBoundary (2*k) p dp q ∧
            ∀ (other dother : ℝ → ℂ) (out : ℂ), RadialEquation radiusLapse V S other dother →
              RetardedBoundary (2*k) other dother out →
              (∀ r : ℝ, 2 < r → p r = other r ∧ dp r = dother r) ∧ q = out := by
  obtain ⟨a,j,u,_,jin,uin,admitted⟩ := admitted_retarded_scattering n hn k hk ki
  let V := rwPotential (2*k) (angularEigenvalue (2*n))
  let S₁ := exteriorSource false n k j.value j.jet
  let S₂ := exteriorSource true n k j.value j.jet
  let S₃ := oddExteriorSource n k j.value j.jet
  have each (second : Bool) : ∃ p dp : ℝ → ℂ, RadialEquation radiusLapse V
      (exteriorSource second n k j.value j.jet) p dp ∧
      RetardedBoundary (2*k) p dp (boundaryResponse second k n j.outgoing (u.outgoing/u.incoming)) := by
    obtain ⟨eq,_,bc,_,_⟩ := admitted second
    exact ⟨_,_,eq,bc⟩
  obtain ⟨p₁,dp₁,e₁,b₁⟩ := each false
  obtain ⟨p₂,dp₂,e₂,b₂⟩ := each true
  obtain ⟨p₃,dp₃,e₃,b₃,_⟩ := pure_odd_retarded_scattering n hn k hk ki a j u
  refine ⟨a,j,u,jin,uin,?_⟩
  intro even odd m
  dsimp only
  let w := angularSourceWeights n m k even odd
  let p := fun r => w.1*p₁ r+w.2.1*p₂ r+w.2.2*p₃ r
  let dp := fun r => w.1*dp₁ r+w.2.1*dp₂ r+w.2.2*dp₃ r
  let S := angularExteriorForcing n m k even odd j.value j.jet
  have start := equation_scale w.1 e₁ (fun r => w.1*S₁ r) (fun _ _ => rfl)
  have ready := radial_equation_sub_scaled (-w.2.2) (radial_equation_sub_scaled (-w.2.1) start e₂) e₃
  simp only [neg_mul,sub_neg_eq_add] at ready
  have equation : RadialEquation radiusLapse V S p dp := by
    refine ⟨ready.value,?_⟩
    intro r hr
    have form : S r = w.1*S₁ r+w.2.1*S₂ r+w.2.2*S₃ r :=
      angular_exterior_three_sources n m hn k hk ki even odd j.value j.jet r hr
    rw [form]
    exact ready.jet r hr
  have boundary := retarded_add_scaled w.2.2
    (retarded_add_scaled w.2.1 (retarded_scale w.1 b₁) b₂) b₃
  refine ⟨p,dp,equation,boundary,?_⟩
  have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  exact fun _ _ _ otherEq otherBC =>
    retarded_solution_unique (2*k) (angularEigenvalue (2*n)) wk wi u uin equation otherEq boundary otherBC

#print axioms angular_exterior_three_sources
#print axioms general_angular_retarded_scattering

end
end SchwarzschildMixtures.Strain
