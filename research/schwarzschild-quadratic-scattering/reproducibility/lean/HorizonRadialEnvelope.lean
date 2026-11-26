import MeromorphicRadialField
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Remove the ingoing phase before taking a radial germ at the horizon.
The envelope and its scaled jet can be analytic even when the carrier is
not a meromorphic germ at \(r=2\). -/
namespace SchwarzschildLaurent.Horizon

open Filter Polynomial MeromorphicRadial
open scoped Topology

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

/-- The radial envelope of \(Z=r^2 D J\) when \(J=e^{-kx}H\). -/
def envelopeJet (k : ℂ) (H : ℂ → ℂ) (r : ℂ) : ℂ :=
  r*(r-2)*deriv H r - k*r^2*H r

theorem envelope_jet_analytic (k : ℂ) {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 2) :
    AnalyticAt ℂ (envelopeJet k H) 2 := by
  have hd := hH.deriv
  unfold envelopeJet
  fun_prop

@[simp] theorem envelope_jet_at_horizon (k : ℂ) (H : ℂ → ℂ) :
    envelopeJet k H 2 = -(4*k)*H 2 := by
  unfold envelopeJet
  ring

private theorem analytic_polynomial (a : ℂ) (p : ℂ[X]) : AnalyticAt ℂ p.eval a := by
  induction p using Polynomial.induction_on' with
  | add b c hb hc =>
    simpa only [eval_add] using hb.fun_add hc
  | monomial n c =>
    have power : AnalyticAt ℂ (fun z : ℂ => z^n) a := by fun_prop
    simpa only [eval_monomial] using (analyticAt_const (v := c)).fun_mul power

/-- A finite rational value is represented by a holomorphic function with
that value, using exactly the rational-function embedding of the replay. -/
theorem rational_value_analytic {a value : ℂ} {u : ℂᵣ}
    (h : RadiusValue a u value) :
    ∃ (q : ℂ → ℂ) (hq : AnalyticAt ℂ q a),
      q a = value ∧ rationalGerm a u = ofFunction q hq.meromorphicAt := by
  obtain ⟨p,d,hd,rfl,rfl⟩ := h
  have hf := (analytic_polynomial a p).fun_div (analytic_polynomial a d) hd
  refine ⟨fun z => p.eval z/d.eval z,hf,rfl,?_⟩
  rw [map_div₀, rationalGerm_polynomial, rationalGerm_polynomial]
  have hdmap : polynomialGerm a d ≠ 0 := by
    rw [ne_eq, ← map_zero (polynomialGerm a), (polynomialGerm_injective a).eq_iff]
    intro e
    exact hd (by simp [e])
  symm
  apply (eq_div_iff hdmap).2
  apply Subtype.ext
  change ((fun z => (p.eval z/d.eval z)*d.eval z) : GermAt a) = (p.eval : GermAt a)
  apply Filter.Germ.coe_eq.mpr
  have hdnear := (analytic_polynomial a d).continuousAt.eventually_ne hd
  filter_upwards [hdnear.filter_mono nhdsWithin_le_nhds] with z hz
  exact div_mul_cancel₀ _ hz

private theorem coordinate_germ (a : ℂ) :
    rationalGerm a (coordinate a) =
      ofFunction (fun r => r-a) ((analyticAt_id.sub analyticAt_const).meromorphicAt) := by
  rw [coordinate, rationalGerm_polynomial]
  apply Subtype.ext
  change ((localCoordinate a).eval : GermAt a) = ((fun r => r-a) : GermAt a)
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall (fun r => by simp [localCoordinate])

/-- Degree-two evaluation on the two envelopes. The second input has
already been differentiated with the carrier included. -/
def evaluateEnvelope (row : Row ℂᵣ) (H Z : At 2) : At 2 :=
  let e := rationalGerm 2
  e row.1*H^2 + e row.2.1*H*Z + e row.2.2*Z^2

def evaluateEnvelopeAt (row : Row ℂᵣ) (H Z : ℂ → ℂ) (r : ℂ) : ℂ :=
  let v := fun u => RatFunc.eval (RingHom.id ℂ) r u
  v row.1*H r^2 + v row.2.1*H r*Z r + v row.2.2*Z r^2

private theorem rational_eval_meromorphic (a : ℂ) (u : ℂᵣ) :
    MeromorphicAt (fun r => RatFunc.eval (RingHom.id ℂ) r u) a := by
  simpa only [RatFunc.eval, Polynomial.eval₂_id] using
    (analytic_polynomial a u.num).meromorphicAt.fun_div (analytic_polynomial a u.denom).meromorphicAt

private theorem rational_germ_eval (a : ℂ) (u : ℂᵣ) :
    rationalGerm a u = ofFunction (fun r => RatFunc.eval (RingHom.id ℂ) r u) (rational_eval_meromorphic a u) := by
  have nonzero : polynomialGerm a u.denom ≠ 0 := by
    rw [ne_eq, ← map_zero (polynomialGerm a), (polynomialGerm_injective a).eq_iff]
    exact u.denom_ne_zero
  have eventually_nonzero : ∀ᶠ r in 𝓝[≠] a, u.denom.eval r ≠ 0 := by
    apply (analytic_polynomial a u.denom).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    intro zero
    apply nonzero
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr (zero.filter_mono nhdsWithin_le_nhds)
  calc
    _ = polynomialGerm a u.num / polynomialGerm a u.denom := by
      rw [← rationalGerm_polynomial, ← rationalGerm_polynomial, ← map_div₀, RatFunc.num_div_denom]
    _ = _ := by
      symm
      apply (eq_div_iff nonzero).2
      apply Subtype.ext
      change ((fun r => RatFunc.eval (RingHom.id ℂ) r u * u.denom.eval r) : GermAt a) =
        (u.num.eval : GermAt a)
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [eventually_nonzero] with r hr
      simp only [RatFunc.eval, Polynomial.eval₂_id]
      exact div_mul_cancel₀ _ hr

theorem extension_agrees_with_evaluation (row : Row ℂᵣ) {H Z G : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 2) (hZ : AnalyticAt ℂ Z 2) (hG : AnalyticAt ℂ G 2)
    (eq : evaluateEnvelope row (ofFunction H hH.meromorphicAt) (ofFunction Z hZ.meromorphicAt) =
      ofFunction G hG.meromorphicAt) :
    evaluateEnvelopeAt row H Z =ᶠ[𝓝[≠] (2 : ℂ)] G := by
  dsimp only [evaluateEnvelope] at eq
  rw [rational_germ_eval 2 row.1, rational_germ_eval 2 row.2.1, rational_germ_eval 2 row.2.2] at eq
  exact Filter.Germ.coe_eq.mp (congrArg Subtype.val eq)

theorem analytic_of_simple_pole_cancellation (row : Row ℂᵣ) (k : ℂ)
    (H : ℂ → ℂ) (hH : AnalyticAt ℂ H 2)
    {a b c : ℂ}
    (ha : RadiusValue 2 (coordinate 2*row.1) a)
    (hb : RadiusValue 2 (coordinate 2*row.2.1) b)
    (hc : RadiusValue 2 (coordinate 2*row.2.2) c)
    (residue : a-4*k*b+16*k^2*c = 0) :
    ∃ (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 2),
      evaluateEnvelope row (ofFunction H hH.meromorphicAt)
        (ofFunction (envelopeJet k H) (envelope_jet_analytic k hH).meromorphicAt) =
          ofFunction G hG.meromorphicAt := by
  obtain ⟨A,hA,a₂,hAg⟩ := rational_value_analytic ha
  obtain ⟨B,hB,b₂,hBg⟩ := rational_value_analytic hb
  obtain ⟨C,hC,c₂,hCg⟩ := rational_value_analytic hc
  let Z := envelopeJet k H
  have hZ : AnalyticAt ℂ Z 2 := envelope_jet_analytic k hH
  let N := fun r => A r*H r^2+B r*H r*Z r+C r*Z r^2
  have hN : AnalyticAt ℂ N 2 := by fun_prop
  have zero : N 2 = 0 := by
    dsimp only [N, Z]
    rw [a₂,b₂,c₂,envelope_jet_at_horizon]
    linear_combination H 2 ^ 2 * residue
  have hSeries := hN
  obtain ⟨p,hp⟩ := hSeries
  let G := dslope N 2
  have hG : AnalyticAt ℂ G 2 := hp.has_fpower_series_dslope_fslope.analyticAt
  refine ⟨G,hG,?_⟩
  apply (mul_left_cancel₀ ((map_ne_zero (rationalGerm 2)).2 (coordinate_ne_zero 2)))
  calc
    _ = evaluateEnvelope (scale (coordinate 2) row)
        (ofFunction H hH.meromorphicAt) (ofFunction Z hZ.meromorphicAt) := by
      simp only [evaluateEnvelope, scale, map_mul]
      ring
    _ = ofFunction N hN.meromorphicAt := by
      simp only [evaluateEnvelope, scale, hAg,hBg,hCg]
      rfl
    _ = rationalGerm 2 (coordinate 2)*ofFunction G hG.meromorphicAt := by
      rw [coordinate_germ]
      apply Subtype.ext
      change (N : GermAt 2) = ((fun r => (r-2)*G r) : GermAt 2)
      apply Filter.Germ.coe_eq.mpr
      exact Eventually.of_forall fun r => by
        simpa only [smul_eq_mul, G] using (sub_smul_dslope_of_zero zero r).symm

#print axioms rational_value_analytic
#print axioms envelope_jet_analytic
#print axioms envelope_jet_at_horizon
#print axioms analytic_of_simple_pole_cancellation
#print axioms extension_agrees_with_evaluation

end
end SchwarzschildLaurent.Horizon
