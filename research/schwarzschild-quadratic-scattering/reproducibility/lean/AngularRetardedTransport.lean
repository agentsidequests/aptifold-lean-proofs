import AngularMixtureClassification
import RetardedScattering

/-! Retarded fields and strains for the aligned angular mixtures. -/
namespace SchwarzschildMixtures.Strain

open Filter Polynomial SchwarzschildLaurent SchwarzschildLaurent.Exterior
  SchwarzschildLaurent.LinearWave SchwarzschildLaurent.Outgoing
  SchwarzschildMixtures.OutgoingData
open scoped Topology

noncomputable section

theorem equation_scale (c : ℂ) {f V S v dv : ℝ → ℂ}
    (h : RadialEquation f V S v dv) (T : ℝ → ℂ) (source : ∀ r > 2, T r = c*S r) :
    RadialEquation f V T (fun r => c*v r) (fun r => c*dv r) := by
  constructor <;> intro r hr
  · apply ((h.value r hr).const_mul c).congr_deriv
    simp only [div_eq_mul_inv]
    ring
  · apply ((h.jet r hr).const_mul c).congr_deriv
    rw [source r hr]
    simp only [div_eq_mul_inv]
    ring

private theorem modes_scale {l : Filter ℝ} {w : ℂ} {v dv : ℝ → ℂ}
    {a b : ℂ} (c : ℂ) (h : RadialModeLimits l w v dv a b) :
    RadialModeLimits l w (fun r => c*v r) (fun r => c*dv r) (c*a) (c*b) := by
  constructor
  · apply (h.incoming.const_mul c).congr
    intro r
    simp only [incomingMode, div_eq_mul_inv]
    ring
  · apply (h.outgoing.const_mul c).congr
    intro r
    simp only [outgoingMode, div_eq_mul_inv]
    ring

theorem retarded_scale {w : ℂ} {v dv : ℝ → ℂ} {q : ℂ}
    (c : ℂ) (h : RetardedBoundary w v dv q) :
    RetardedBoundary w (fun r => c*v r) (fun r => c*dv r) (c*q) := by
  obtain ⟨a, ha⟩ := h.horizon
  constructor
  · exact ⟨c*a, by simpa only [mul_zero] using modes_scale c ha⟩
  · simpa only [mul_zero] using modes_scale c h.infinity

/-- The azimuthal source with its nonzero binomial normalization cleared. -/
def angularExteriorSource (second : Bool) (n m : ℕ) (k : ℂ)
    (a : ℂ[X]) (u du : ℝ → ℂ) : ℝ → ℂ :=
  fun r => quadraticValue
    (readRow (angularSource n m k a (C (SchwarzschildMixtures.mixtureRatio second k n)*a)) r)
    (u r) ((r : ℂ)^2*du r)

theorem angular_exterior_source_scale (second : Bool) (n m : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (a : ℂ[X]) (u du : ℝ → ℂ) (r : ℝ) (hr : 2 < r) :
    angularExteriorSource second n m k a u du r =
      (a^2).coeff m*exteriorSource second n k u du r := by
  let c := (a^2).coeff m
  have good := (admitted_rows_regular_exterior second n hn k hk ki r hr).2
  have scaled := good.scale (h := RadiusValue.const (r : ℂ) c)
  unfold angularExteriorSource
  rw [angular_source_on_admitted_branch n m hn k ki second a, scaled.read_eq]
  simp only [exteriorSource, quadraticValue, scale, c]
  ring

/-- Every angular coefficient inherits the same retarded field and
frequency response up to the angular scale, including zero coefficients. -/
theorem admitted_angular_retarded_scattering (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
      j.incoming = parentAlpha k n ∧ u.incoming ≠ 0 ∧
      ∀ (second : Bool) (profile : ℂ[X]) (m : ℕ),
        let c := (profile^2).coeff m
        let q := c*boundaryResponse second k n j.outgoing (u.outgoing/u.incoming)
        let V := rwPotential (2*k) (angularEigenvalue (2*n))
        let S := angularExteriorSource second n m k profile j.value j.jet
        ∃ v dv : ℝ → ℂ,
          RadialEquation radiusLapse V S v dv ∧
          RetardedBoundary (2*k) v dv q ∧
          (∀ (other dother : ℝ → ℂ) (out : ℂ),
            RadialEquation radiusLapse V S other dother →
            RetardedBoundary (2*k) other dother out →
            (∀ r : ℝ, 2 < r → v r = other r ∧ dv r = dother r) ∧ q = out) ∧
          strainScale second k n*q = c*printedResponse second k n j.outgoing (u.outgoing/u.incoming) := by
  obtain ⟨a,j,u,_,jin,uin,fields⟩ := admitted_retarded_scattering n hn k hk ki
  refine ⟨a,j,u,jin,uin,?_⟩
  intro second profile m
  dsimp only
  obtain ⟨eq,_,boundary,_,strain⟩ := fields second
  let c := (profile^2).coeff m
  have e := equation_scale c eq _ (fun r hr =>
    angular_exterior_source_scale second n m hn k hk ki profile j.value j.jet r hr)
  have b := retarded_scale c boundary
  refine ⟨_,_,e,b,?_,?_⟩
  · have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
    have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
    exact fun _ _ _ otherEq otherBC =>
      retarded_solution_unique (2*k) (angularEigenvalue (2*n)) wk wi u uin e otherEq b otherBC
  · show strainScale second k n*(c*boundaryResponse second k n j.outgoing (u.outgoing/u.incoming)) = _
    rw [mul_left_comm, strain]

#print axioms angular_exterior_source_scale
#print axioms admitted_angular_retarded_scattering

end
end SchwarzschildMixtures.Strain
