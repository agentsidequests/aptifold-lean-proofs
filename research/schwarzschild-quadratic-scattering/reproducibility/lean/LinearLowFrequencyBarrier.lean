import ScatteringSoftNonzero
import ScatteringPhysicalBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A positive Regge–Wheeler barrier forces at least quadratic growth
of the real part on a low-frequency radial interval. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set SchwarzschildLaurent.Outgoing SchwarzschildMixtures.Strain
open scoped Topology

noncomputable section

theorem monotone_from_nonnegative_derivative {a b : ℝ} {f df : ℝ → ℝ}
    (derivative : ∀ r ∈ Icc a b, HasDerivAt f (df r) r)
    (nonnegative : ∀ r ∈ Icc a b, 0 ≤ df r) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun r h => (derivative r h).continuousAt.continuousWithinAt
  · exact fun r h => (derivative r (interior_subset h)).differentiableAt.differentiableWithinAt
  · intro r h
    rw [(derivative r (interior_subset h)).deriv]
    exact nonnegative r (interior_subset h)

/-- A cooperative two-component system stays positive. A first loss of
positivity would be approached while both derivatives are nonnegative. -/
theorem forward_positive_pair (a b : ℝ) (y z A B C : ℝ → ℝ)
    (dy : ∀ r ∈ Icc a b, HasDerivAt y (A r*z r) r)
    (dz : ∀ r ∈ Icc a b, HasDerivAt z (B r*y r+C r) r)
    (coeffs : ∀ r ∈ Icc a b, 0 ≤ A r ∧ 0 ≤ B r ∧ 0 ≤ C r)
    (ya : 0 < y a) (za : 0 < z a) :
    ∀ r ∈ Icc a b, 0 < y r ∧ 0 < z r := by
  let bad := {r : ℝ | r ∈ Icc a b ∧ (y r ≤ 0 ∨ z r ≤ 0)}
  have empty : ¬bad.Nonempty := by
    intro exists_bad
    let t := sInf bad
    have lower : BddBelow bad := ⟨a,fun _ h => h.1.1⟩
    have lo : a ≤ t := le_csInf exists_bad (fun _ h => h.1.1)
    have hi : t ≤ b := by
      obtain ⟨q,hq⟩ := exists_bad
      exact (csInf_le lower hq).trans hq.1.2
    have range : Icc a t ⊆ Icc a b := fun _ h => ⟨h.1,h.2.trans hi⟩
    have before : ∀ r ∈ interior (Icc a t), 0 < y r ∧ 0 < z r := by
      intro r hr
      rw [interior_Icc] at hr
      have admitted : r ∈ Icc a b := ⟨hr.1.le,hr.2.le.trans hi⟩
      by_contra! nonpositive
      have disjunction : y r ≤ 0 ∨ z r ≤ 0 :=
        if h : 0 < y r then Or.inr (nonpositive h) else Or.inl (le_of_not_gt h)
      have tr : t ≤ r := csInf_le lower ⟨admitted,disjunction⟩
      exact (not_le_of_gt hr.2) tr
    have ymono : MonotoneOn y (Icc a t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun r hr => (dy r (range hr)).continuousAt.continuousWithinAt
      · exact fun r hr => (dy r (range (interior_subset hr))).differentiableAt.differentiableWithinAt
      · intro r hr
        have h := range (interior_subset hr)
        rw [(dy r h).deriv]
        exact mul_nonneg (coeffs r h).1 (before r hr).2.le
    have zmono : MonotoneOn z (Icc a t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun r hr => (dz r (range hr)).continuousAt.continuousWithinAt
      · exact fun r hr => (dz r (range (interior_subset hr))).differentiableAt.differentiableWithinAt
      · intro r hr
        have h := range (interior_subset hr)
        rw [(dz r h).deriv]
        exact add_nonneg (mul_nonneg (coeffs r h).2.1 (before r hr).1.le) (coeffs r h).2.2
    have yT := ya.trans_le (ymono ⟨le_rfl,lo⟩ ⟨lo,le_rfl⟩ lo)
    have zT := za.trans_le (zmono ⟨le_rfl,lo⟩ ⟨lo,le_rfl⟩ lo)
    have noBad : ∀ᶠ r in 𝓝 t, r ∉ bad := by
      filter_upwards [
        (dy t ⟨lo,hi⟩).continuousAt.tendsto.eventually (Ioi_mem_nhds yT),
        (dz t ⟨lo,hi⟩).continuousAt.tendsto.eventually (Ioi_mem_nhds zT)] with r h1 h2
      intro h
      exact h.2.elim (not_le_of_gt h1) (not_le_of_gt h2)
    exact (mem_closure_iff_frequently.mp (csInf_mem_closure exists_bad lower)) noBad
  intro r hr
  by_contra! fails
  have disjunction : y r ≤ 0 ∨ z r ≤ 0 :=
    if h : 0 < y r then Or.inr (fails h) else Or.inl (le_of_not_gt h)
  exact empty ⟨r,hr,disjunction⟩

def realLapse (r : ℝ) : ℝ := (r-2)/r

def realBarrier (n : ℕ) (omega r : ℝ) : ℝ :=
  realLapse r*((n:ℝ)*(n+1)/r^2-6/r^3)-omega^2

theorem real_lapse_cast (r : ℝ) : (realLapse r : ℂ) = radiusLapse r := by
  simp [realLapse,radiusLapse]

theorem real_barrier_cast (n : ℕ) (omega r : ℝ) :
    (realBarrier n omega r : ℂ) = rwPotential (frequencyParameter omega) (angularEigenvalue n) r := by
  unfold realBarrier rwPotential frequencyParameter angularEigenvalue
  push_cast
  rw [real_lapse_cast,mul_pow,Complex.I_sq]
  ring

theorem real_lapse_positive {r : ℝ} (hr : 2 < r) : 0 < realLapse r :=
  div_pos (sub_pos.mpr hr) (by linarith)

theorem real_exterior_derivatives (n : ℕ) (omega : ℝ) {u du : ℝ → ℂ}
    (equation : RadialEquation radiusLapse (rwPotential (frequencyParameter omega) (angularEigenvalue n)) 0 u du)
    {r : ℝ} (hr : 2 < r) :
    HasDerivAt (fun s => (u s).re) ((realLapse r)⁻¹*(du r).re) r ∧
    HasDerivAt (fun s => (du s).re) ((realBarrier n omega r/realLapse r)*(u r).re) r := by
  have dv := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (equation.value r hr)
  have dd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (equation.jet r hr)
  rw [← real_lapse_cast] at dv
  rw [← real_lapse_cast,← real_barrier_cast] at dd
  constructor
  · simp only [Function.comp_def,Complex.reCLM_apply,Complex.div_ofReal_re] at dv
    exact dv.congr_deriv (by ring)
  · simp only [Function.comp_def,Complex.reCLM_apply,Pi.zero_apply,add_zero,Complex.div_ofReal_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at dd
    exact dd.congr_deriv (by ring)

/-- In the long barrier interval the tortoise second derivative of
`r^2` is at most the potential term acting on `r^2`. -/
theorem square_barrier_subsolution (n : ℕ) (hn : 2 ≤ n) {omega r : ℝ} (wo : 0 < omega)
    (hr : 4 ≤ r) (outer : omega*r ≤ 1/2) : 2*realLapse r ≤ realBarrier n omega r*r^2 := by
  have r0 : 0 < r := by linarith
  have ell : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have L : 6 ≤ (n:ℝ)*(n+1) := by nlinarith [mul_nonneg (sub_nonneg.mpr ell) (show (0:ℝ) ≤ n+3 by linarith)]
  have lap : 1/2 ≤ realLapse r := (le_div_iff₀ r0).2 (by linarith)
  have rloss : 6/r ≤ 3/2 := (div_le_iff₀ r0).2 (by linarith)
  have gap : 5/2 ≤ (n:ℝ)*(n+1)-2-6/r := by linarith
  have static := mul_le_mul lap gap (by norm_num : (0:ℝ) ≤ 5/2) (real_lapse_positive (by linarith)).le
  have freq := (sq_le_sq₀ (by positivity : 0 ≤ omega*r) (by norm_num : (0:ℝ) ≤ 1/2)).2 outer
  have identity : realBarrier n omega r*r^2 =
      realLapse r*((n:ℝ)*(n+1)-2-6/r)+2*realLapse r-(omega*r)^2 := by
    unfold realBarrier
    field_simp [r0.ne']
    ring
  rw [identity]
  norm_num at static freq
  linarith

/-- A fixed positive seed at four mass units grows at least as a
positive multiple of `r^2` up to the chosen low-frequency radius. -/
theorem square_growth_in_barrier (n : ℕ) (hn : 2 ≤ n) {omega R c : ℝ} {scale : ℂ} (wo : 0 < omega)
    (outer : omega*R ≤ 1/2) (cp : 0 < c)
    (u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) scale)
    (seed_value : c*4^2 < (u.value 4).re) (seed_jet : 4*c < (u.jet 4).re) :
    ∀ r ∈ Icc 4 R, c*r^2 < (u.value r).re := by
  let y := fun r : ℝ => (u.value r).re-c*r^2
  let z := fun r : ℝ => (u.jet r).re-2*c*(r-2)
  let A := fun r : ℝ => (realLapse r)⁻¹
  let B := fun r : ℝ => realBarrier n omega r/realLapse r
  let C := fun r : ℝ => c*(B r*r^2-2)
  have dy : ∀ r ∈ Icc 4 R, HasDerivAt y (A r*z r) r := by
    intro r hr
    have ext : 2 < r := lt_of_lt_of_le (by norm_num) hr.1
    have value := (real_exterior_derivatives n omega u.equation ext).1
    have poly := ((hasDerivAt_id r).pow 2).const_mul c
    apply (value.sub poly).congr_deriv
    dsimp only [A,z,id_eq]
    have r0 : r ≠ 0 := by linarith [hr.1]
    unfold realLapse
    field_simp [r0,sub_ne_zero.mpr ext.ne']
    ring
  have dz : ∀ r ∈ Icc 4 R, HasDerivAt z (B r*y r+C r) r := by
    intro r hr
    have ext : 2 < r := lt_of_lt_of_le (by norm_num) hr.1
    have jet := (real_exterior_derivatives n omega u.equation ext).2
    have line := ((hasDerivAt_id r).sub_const 2).const_mul (2*c)
    apply (jet.sub line).congr_deriv
    dsimp only [y,C]
    ring
  have nonnegative : ∀ r ∈ Icc 4 R, 0 ≤ A r ∧ 0 ≤ B r ∧ 0 ≤ C r := by
    intro r hr
    have f := real_lapse_positive (lt_of_lt_of_le (by norm_num) hr.1)
    have endBound := (mul_le_mul_of_nonneg_left hr.2 wo.le).trans outer
    have sub := square_barrier_subsolution n hn wo hr.1 endBound
    have p : 0 ≤ realBarrier n omega r := by
      by_contra! neg
      have product := mul_nonpos_of_nonpos_of_nonneg neg.le (sq_nonneg r)
      linarith
    refine ⟨inv_nonneg.mpr f.le,div_nonneg p f.le,?_⟩
    apply mul_nonneg cp.le
    apply sub_nonneg.mpr
    dsimp only [B]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ f).2 sub
  have ya : 0 < y 4 := sub_pos.mpr seed_value
  have za : 0 < z 4 := by
    dsimp only [z]
    linarith
  intro r hr
  exact sub_pos.mp (forward_positive_pair 4 R y z A B C dy dz nonnegative ya za r hr).1

theorem soft_incidence_at_matching_radius (n : ℕ) {omega : ℝ} (wo : 0 < omega) (small : omega ≤ 1/8)
    (u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1) :
    (‖u.value (1/(2*omega))‖/2)*Real.exp (-2*((n:ℝ)*(n+1)+3)) ≤ ‖u.incoming‖ := by
  let R : ℝ := 1/(2*omega)
  have Rlarge : 4 ≤ R := (le_div_iff₀ (by positivity : 0 < 2*omega)).2 (by linarith)
  have normW : ‖frequencyParameter omega‖ = omega := by simp [frequencyParameter,Complex.norm_real,abs_of_pos wo]
  have nonzero : frequencyParameter omega ≠ 0 := norm_ne_zero_iff.mp (by rw [normW]; exact wo.ne')
  have imaginary : (frequencyParameter omega).re = 0 := by simp [frequencyParameter,Complex.mul_re]
  have normL : ‖angularEigenvalue n‖ = (n:ℝ)*(n+1) := by
    simp only [angularEigenvalue,← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,
      ← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have transport := incident_lower_from_value (frequencyParameter omega) n nonzero imaginary u
    (R := R) (lt_of_lt_of_le (by norm_num) Rlarge)
  rw [normW,normL] at transport
  have exponent : -(((n:ℝ)*(n+1)+3)/omega)/R = -2*((n:ℝ)*(n+1)+3) := by
    dsimp only [R]
    field_simp [wo.ne']
  rwa [exponent] at transport

/-- Uniform positive data in a unit phase give an explicit lower
bound on incidence as the frequency tends to zero. -/
theorem soft_incidence_from_square_seed (n : ℕ) (hn : 2 ≤ n) {omega c : ℝ} (wo : 0 < omega)
    (small : omega ≤ 1/8) (cp : 0 < c)
    (u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1)
    (phase : ℂ) (unit : ‖phase‖ = 1)
    (seed_value : c*4^2 < (phase*u.value 4).re) (seed_jet : 4*c < (phase*u.jet 4).re) :
    ((c/8)*Real.exp (-2*((n:ℝ)*(n+1)+3)))/omega^2 ≤ ‖u.incoming‖ := by
  let R : ℝ := 1/(2*omega)
  have large : 4 ≤ R := (le_div_iff₀ (by positivity : 0 < 2*omega)).2 (by linarith)
  have cutoff : omega*R ≤ 1/2 := by
    dsimp only [R]
    field_simp [wo.ne']
    norm_num
  let rotated := u.scale phase
  have grow := square_growth_in_barrier n hn wo cutoff cp rotated seed_value seed_jet R ⟨large,le_rfl⟩
  have upper := Complex.re_le_norm (rotated.value R)
  change (phase*u.value R).re ≤ ‖phase*u.value R‖ at upper
  rw [norm_mul,unit,one_mul] at upper
  have lower : c*R^2 ≤ ‖u.value R‖ := grow.le.trans upper
  have tail := soft_incidence_at_matching_radius n wo small u
  calc
    _ = (c*R^2/2)*Real.exp (-2*((n:ℝ)*(n+1)+3)) := by
      dsimp only [R]
      field_simp [wo.ne']
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right lower (by norm_num))
      (Real.exp_pos _).le).trans tail

#print axioms forward_positive_pair
#print axioms real_exterior_derivatives
#print axioms square_barrier_subsolution
#print axioms square_growth_in_barrier
#print axioms soft_incidence_at_matching_radius
#print axioms soft_incidence_from_square_seed

end
end SchwarzschildLaurent.LinearWave
