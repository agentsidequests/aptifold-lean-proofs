import OutgoingWaveLimits

/-! Leading scattering limits for a quadratic field of a parent wave
and its first tortoise derivative. -/
namespace SchwarzschildLaurent.Outgoing

open Filter
open scoped Topology

noncomputable section

abbrev Coefficients := ℂ × ℂ × ℂ

def quadraticValue (c : Coefficients) (v dv : ℂ) : ℂ :=
  c.1*v^2+c.2.1*v*dv+c.2.2*dv^2

def quadraticJetCoefficients (c dc : Coefficients) (V : ℂ) : Coefficients :=
  (dc.1+c.2.1*V, 2*c.1+dc.2.1+2*c.2.2*V, c.2.1+dc.2.2)

/-- Input is a row and its tortoise derivative, with limits taken
after converting from the scaled parent jet to the ordinary jet. -/
structure CoefficientLimits (f : ℝ → ℂ) (c dc : ℝ → Coefficients)
    (c₀ : Coefficients) : Prop where
  value : Tendsto c atTop (𝓝 c₀)
  jet : Tendsto dc atTop (𝓝 (0,0,0))
  derivatives : ∀ᶠ r in atTop,
    HasDerivAt (fun s => (c s).1) ((dc r).1/f r) r ∧
    HasDerivAt (fun s => (c s).2.1) ((dc r).2.1/f r) r ∧
    HasDerivAt (fun s => (c s).2.2) ((dc r).2.2/f r) r

theorem quadratic_has_derivative (f V v dv : ℝ → ℂ) (c dc : ℝ → Coefficients)
    (eq : RadialEquation f V 0 v dv) {r : ℝ} (hr : 2 < r) (hf : f r ≠ 0)
    (h₁ : HasDerivAt (fun s => (c s).1) ((dc r).1/f r) r)
    (h₂ : HasDerivAt (fun s => (c s).2.1) ((dc r).2.1/f r) r)
    (h₃ : HasDerivAt (fun s => (c s).2.2) ((dc r).2.2/f r) r) :
    HasDerivAt (fun s => quadraticValue (c s) (v s) (dv s))
      (quadraticValue (quadraticJetCoefficients (c r) (dc r) (V r)) (v r) (dv r)/f r) r := by
  have hv := eq.value r hr
  have hD := eq.jet r hr
  simp only [quadraticValue,pow_two]
  apply (((h₁.mul (hv.mul hv)).add ((h₂.mul hv).mul hD)).add (h₃.mul (hD.mul hD))).congr_deriv
  simp only [quadraticJetCoefficients,Pi.mul_apply,Pi.zero_apply,add_zero]
  field_simp [hf] <;> ring

private def parts (c : Coefficients) (k ain aout : ℂ) : Coefficients :=
  (ain^2*quadraticValue c 1 (-k), aout^2*quadraticValue c 1 k,
    2*ain*aout*(c.1-k^2*c.2.2))

private def threeWaves (q : Coefficients) (m p : ℂ) : ℂ :=
  q.1*m^2+q.2.1*p^2+q.2.2

private theorem quadratic_three_waves (c : Coefficients) (k ain aout m p : ℂ) (hmp : m*p = 1) :
    quadraticValue c (wave ain aout m p) (waveJet k ain aout m p) =
      threeWaves (parts c k ain aout) m p := by
  unfold threeWaves parts wave waveJet quadraticValue
  dsimp only
  linear_combination (2*ain*aout*(c.1-k^2*c.2.2))*hmp

private theorem derivative_parts (c : Coefficients) (k ain aout : ℂ) :
    let q := parts c k ain aout
    parts (quadraticJetCoefficients c (0,0,0) (k^2)) k ain aout =
      (-(2*k)*q.1, (2*k)*q.2.1, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [parts,quadraticValue,quadraticJetCoefficients] <;> ring

private theorem project_three_waves (w m p : ℂ) (hp : m^2*p^2 = 1) (q d : Coefficients) :
    incomingMode w (p^2) (threeWaves q m p) (threeWaves d m p) =
      (q.1-d.1/w)/2 + p^4*((q.2.1-d.2.1/w)/2) + p^2*((q.2.2-d.2.2/w)/2) ∧
    outgoingMode w (m^2) (threeWaves q m p) (threeWaves d m p) =
      (q.2.1+d.2.1/w)/2 + m^4*((q.1+d.1/w)/2) + m^2*((q.2.2+d.2.2/w)/2) := by
  unfold incomingMode outgoingMode threeWaves
  constructor
  · linear_combination ((q.1-d.1/w)/2)*hp
  · linear_combination ((q.2.1+d.2.1/w)/2)*hp

private theorem signed_limit_from_three {l : Filter ℝ} (w : ℂ) (hw : w ≠ 0)
    (m p : ℝ → ℂ) (hmp : ∀ r, m r*p r = 1) (hm : ∀ r, ‖m r‖ = 1) (hp : ∀ r, ‖p r‖ = 1)
    (q d : ℝ → Coefficients) (ai ao : ℂ)
    (hq : Tendsto q l (𝓝 (ai,ao,0))) (hd : Tendsto d l (𝓝 (-w*ai,w*ao,0))) :
    ModeLimits l w (fun r => m r^2) (fun r => p r^2)
      (fun r => threeWaves (q r) (m r) (p r)) (fun r => threeWaves (d r) (m r) (p r)) ai ao := by
  simp only [nhds_prod_eq] at hq hd
  have hi := (hq.fst.sub (hd.fst.div_const w)).div_const 2
  have ho := (hq.snd.fst.add (hd.snd.fst.div_const w)).div_const 2
  have xi := (hq.snd.fst.sub (hd.snd.fst.div_const w)).div_const 2
  have xo := (hq.fst.add (hd.fst.div_const w)).div_const 2
  have mi := (hq.snd.snd.sub (hd.snd.snd.div_const w)).div_const 2
  have mo := (hq.snd.snd.add (hd.snd.snd.div_const w)).div_const 2
  simp only [neg_mul,neg_div,mul_div_cancel_left₀ _ hw,sub_neg_eq_add,
    add_neg_cancel,sub_self,zero_div, ← two_mul,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℂ) ≠ 0)] at hi ho xi xo mi mo
  have pow_p (n : ℕ) (r : ℝ) : ‖p r^n‖ = 1 := by rw [norm_pow,hp,one_pow]
  have pow_m (n : ℕ) (r : ℝ) : ‖m r^n‖ = 1 := by rw [norm_pow,hm,one_pow]
  have i := (hi.add (unit_mul_zero (pow_p 4) xi)).add (unit_mul_zero (pow_p 2) mi)
  have o := (ho.add (unit_mul_zero (pow_m 4) xo)).add (unit_mul_zero (pow_m 2) mo)
  rw [add_zero,add_zero] at i o
  refine ⟨i.congr fun r => ?_,o.congr fun r => ?_⟩
  · exact (project_three_waves w (m r) (p r) (squared_phase_inverse _ _ (hmp r)) (q r) (d r)).1.symm
  · exact (project_three_waves w (m r) (p r) (squared_phase_inverse _ _ (hmp r)) (q r) (d r)).2.symm

theorem quadratic_mode_limits (k : ℂ) (hk : k ≠ 0) (m p : ℝ → ℂ)
    (phases : ∀ r, m r*p r = 1) (hm : ∀ r, ‖m r‖ = 1) (hp : ∀ r, ‖p r‖ = 1)
    (f V j dj P dP : ℝ → ℂ) (c dc : ℝ → Coefficients) (c₀ : Coefficients)
    (ain aout : ℂ) (hparent : ModeLimits atTop k m p j dj ain aout)
    (parentEq : RadialEquation f V 0 j dj) (hV : Tendsto V atTop (𝓝 (k^2)))
    (hf : ∀ᶠ r in atTop, f r ≠ 0)
    (coefs : CoefficientLimits f c dc c₀) (mixed : c₀.1-k^2*c₀.2.2 = 0)
    (valueEq : ∀ᶠ r in atTop, P r = quadraticValue (c r) (j r) (dj r))
    (jetEq : ∀ r, 2 < r → HasDerivAt P (dP r/f r) r) :
    ModeLimits atTop (2*k) (fun r => m r^2) (fun r => p r^2) P dP
      (ain^2*quadraticValue c₀ 1 (-k)) (aout^2*quadraticValue c₀ 1 k) := by
  let i := fun r => incomingMode k (p r) (j r) (dj r)
  let o := fun r => outgoingMode k (m r) (j r) (dj r)
  let q := fun r => parts (c r) k (i r) (o r)
  let cd := fun r => quadraticJetCoefficients (c r) (dc r) (V r)
  let d := fun r => parts (cd r) k (i r) (o r)
  have cdl : Tendsto cd atTop (𝓝 (quadraticJetCoefficients c₀ (0,0,0) (k^2))) := by
    have cont : Continuous (fun x : Coefficients × Coefficients × ℂ =>
        quadraticJetCoefficients x.1 x.2.1 x.2.2) := by
      unfold quadraticJetCoefficients
      fun_prop
    exact cont.continuousAt.tendsto.comp (coefs.value.prodMk_nhds (coefs.jet.prodMk_nhds hV))
  have pp : Continuous (fun x : Coefficients × ℂ × ℂ => parts x.1 k x.2.1 x.2.2) := by
    unfold parts quadraticValue
    fun_prop
  have qLim := pp.continuousAt.tendsto.comp
    (coefs.value.prodMk_nhds (hparent.incoming.prodMk_nhds hparent.outgoing))
  have dLim := pp.continuousAt.tendsto.comp
    (cdl.prodMk_nhds (hparent.incoming.prodMk_nhds hparent.outgoing))
  change Tendsto q atTop (𝓝 (parts c₀ k ain aout)) at qLim
  change Tendsto d atTop (𝓝 (parts (quadraticJetCoefficients c₀ (0,0,0) (k^2)) k ain aout)) at dLim
  rw [derivative_parts] at dLim
  have q0 : parts c₀ k ain aout =
      (ain^2*quadraticValue c₀ 1 (-k),aout^2*quadraticValue c₀ 1 k,0) := by simp [parts,mixed]
  have limits := signed_limit_from_three (2*k) (mul_ne_zero (by norm_num) hk) m p phases hm hp q d
    (ain^2*quadraticValue c₀ 1 (-k)) (aout^2*quadraticValue c₀ 1 k) (q0 ▸ qLim) dLim
  obtain ⟨N,hN⟩ := eventually_atTop.1 valueEq
  have point : ∀ᶠ r in atTop,
      threeWaves (q r) (m r) (p r) = P r ∧ threeWaves (d r) (m r) (p r) = dP r := by
    filter_upwards [eventually_gt_atTop (max N 2),hf,coefs.derivatives] with r hr hfr hcd
    have ext : 2 < r := (le_max_right N 2).trans_lt hr
    have large : N < r := (le_max_left N 2).trans_lt hr
    have e : (fun s => quadraticValue (c s) (j s) (dj s)) =ᶠ[𝓝 r] P := by
      filter_upwards [Ioi_mem_nhds large] with s hs
      exact (hN s hs.le).symm
    have deriv := quadratic_has_derivative f V j dj c dc parentEq ext hfr hcd.1 hcd.2.1 hcd.2.2
    have jets := (deriv.congr_of_eventuallyEq e.symm).unique (jetEq r ext)
    have exactJet := (div_left_inj' hfr).mp jets
    obtain ⟨v,v'⟩ := reconstruct_modes k (m r) (p r) (j r) (dj r) hk (phases r)
    refine ⟨?_,?_⟩
    · exact (quadratic_three_waves (c r) k (i r) (o r) (m r) (p r) (phases r)).symm.trans
        ((congrArg₂ (quadraticValue (c r)) v v').trans (hN r large.le).symm)
    · exact (quadratic_three_waves (cd r) k (i r) (o r) (m r) (p r) (phases r)).symm.trans
        ((congrArg₂ (quadraticValue (cd r)) v v').trans exactJet)
  refine ⟨limits.incoming.congr' ?_,limits.outgoing.congr' ?_⟩ <;>
    filter_upwards [point] with r hr <;> rw [hr.1,hr.2]

#print axioms quadratic_has_derivative
#print axioms quadratic_mode_limits

end
end SchwarzschildLaurent.Outgoing
