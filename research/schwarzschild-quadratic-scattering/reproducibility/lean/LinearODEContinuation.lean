import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Continuation of an initial-value solution with a uniform Lipschitz
bound. The Picard steps have a common length even though the radius of
the state-space ball changes at each step. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Metric Set
open scoped NNReal Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def joinAt (a : ℝ) (left right : ℝ → E) (r : ℝ) : E :=
  if r ≤ a then left r else right r

omit [CompleteSpace E] in
/-- The derivative across the join is fixed by the same vector field
and the same state on both sides. -/
theorem joined_derivative (F : ℝ → E → E) (s : Set ℝ) (a : ℝ)
    (left right : ℝ → E) (matchAt : left a = right a)
    (hl : ∀ r ∈ s ∩ Iic a, HasDerivWithinAt left (F r (left r)) (s ∩ Iic a) r)
    (hr : ∀ r ∈ s ∩ Ici a, HasDerivWithinAt right (F r (right r)) (s ∩ Ici a) r) :
    ∀ r ∈ s, HasDerivWithinAt (joinAt a left right) (F r (joinAt a left right r)) s r := by
  intro r h
  have agreeL : EqOn (joinAt a left right) left (s ∩ Iic a) := fun _ ht => if_pos ht.2
  have agreeR : EqOn (joinAt a left right) right (s ∩ Ici a) := by
    intro t ht
    rcases eq_or_lt_of_le (show a ≤ t from ht.2) with ht' | ht'
    · subst t
      simpa only [joinAt, if_pos le_rfl] using matchAt
    · simp only [joinAt,if_neg ht'.not_ge]
  have u : HasDerivWithinAt (joinAt a left right) (F r (joinAt a left right r)) (s ∩ Iic a) r := by
    by_cases ha : r ≤ a
    · rw [agreeL ⟨h,ha⟩]
      exact (hl r ⟨h,ha⟩).congr_of_mem agreeL ⟨h,ha⟩
    · exact HasFDerivWithinAt.of_notMem_closure fun hc =>
        ha ((closure_minimal inter_subset_right isClosed_Iic) hc)
  have v : HasDerivWithinAt (joinAt a left right) (F r (joinAt a left right r)) (s ∩ Ici a) r := by
    by_cases ha : a ≤ r
    · rw [agreeR ⟨h,ha⟩]
      exact (hr r ⟨h,ha⟩).congr_of_mem agreeR ⟨h,ha⟩
    · exact HasFDerivWithinAt.of_notMem_closure fun hc =>
        ha ((closure_minimal inter_subset_right isClosed_Ici) hc)
  have sets : (s ∩ Iic a) ∪ (s ∩ Ici a) = s := by
    ext t
    exact ⟨fun ht => ht.elim And.left And.left,
      fun ht => (le_total t a).elim (fun hle => Or.inl ⟨ht,hle⟩) (fun hle => Or.inr ⟨ht,hle⟩)⟩
  rw [← sets]
  exact u.union v

private theorem uniform_picard_step (F : ℝ → E → E) (K : ℝ≥0)
    (lip : ∀ r, LipschitzWith K (F r)) (zero : ∀ r, F r 0 = 0)
    (cont : ∀ x, Continuous (fun r => F r x))
    (a τ : ℝ) (step : 0 ≤ τ) (short : (K:ℝ)*τ ≤ 1/2) (x : E) :
    ∃ u : ℝ → E, u a = x ∧ ∀ r ∈ Icc a (a+τ),
      HasDerivWithinAt u (F r (u r)) (Icc a (a+τ)) r := by
  let R : ℝ≥0 := ‖x‖₊+1
  let B : ℝ≥0 := K*(2*R)
  let start : Icc a (a+τ) := ⟨a,le_rfl,by linarith⟩
  apply IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (t₀ := start) (a := R) (L := B) (K := K)
  constructor
  · intro r _
    exact (lip r).lipschitzOnWith
  · intro z _
    exact (cont z).continuousOn
  · intro r _ z hz
    have close : ‖z-x‖ ≤ (R:ℝ) := mem_closedBall_iff_norm.1 hz
    have hx : ‖x‖ ≤ (R:ℝ) := by
      change ‖x‖ ≤ ‖x‖+1
      linarith
    have size : ‖z‖ ≤ 2*(R:ℝ) := calc
      ‖z‖ = ‖(z-x)+x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z-x‖+‖x‖ := norm_add_le _ _
      _ ≤ _ := by linarith
    have onorm : ‖F r z‖ ≤ (K:ℝ)*‖z‖ := by
      simpa only [zero r,dist_zero_right] using (lip r).dist_le_mul z 0
    exact onorm.trans (mul_le_mul_of_nonneg_left size K.coe_nonneg)
  · change (B:ℝ)*max (a+τ-a) (a-a) ≤ (R:ℝ)-0
    rw [show a+τ-a = τ by ring,sub_self,max_eq_left step,sub_zero]
    calc
      _ = (2*((K:ℝ)*τ))*(R:ℝ) := by dsimp only [B]; push_cast; ring
      _ ≤ 1*(R:ℝ) := mul_le_mul_of_nonneg_right (by linarith) R.coe_nonneg
      _ = _ := one_mul _

private theorem interval_nhds_right {a b t : ℝ} (h : a ≤ t) (ht : t < b) :
    Icc a b ∈ 𝓝[Ici t] t := by
  refine mem_of_superset (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht))) ?_
  exact fun y hy => ⟨h.trans hy.1,hy.2.le⟩

omit [CompleteSpace E] in
theorem closed_interval_agreement (F : ℝ → E → E) (K : ℝ≥0)
    (lip : ∀ r, LipschitzWith K (F r)) {a b c t : ℝ}
    (u v : ℝ → E) (h : u a = v a) (ht : a ≤ t) (hb : t ≤ b) (hc : t ≤ c)
    (hu : ∀ r ∈ Icc a b, HasDerivWithinAt u (F r (u r)) (Icc a b) r)
    (hv : ∀ r ∈ Icc a c, HasDerivWithinAt v (F r (v r)) (Icc a c) r) :
    u t = v t := by
  have ub : ContinuousOn u (Icc a t) := fun r hr =>
    (hu r ⟨hr.1,hr.2.trans hb⟩).continuousWithinAt.mono (Icc_subset_Icc_right hb)
  have vb : ContinuousOn v (Icc a t) := fun r hr =>
    (hv r ⟨hr.1,hr.2.trans hc⟩).continuousWithinAt.mono (Icc_subset_Icc_right hc)
  have f' : ∀ r ∈ Ico a t, HasDerivWithinAt u (F r (u r)) (Ici r) r := fun r hr =>
    (hu r ⟨hr.1,hr.2.le.trans hb⟩).mono_of_mem_nhdsWithin (interval_nhds_right hr.1 (hr.2.trans_le hb))
  have g' : ∀ r ∈ Ico a t, HasDerivWithinAt v (F r (v r)) (Ici r) r := fun r hr =>
    (hv r ⟨hr.1,hr.2.le.trans hc⟩).mono_of_mem_nhdsWithin (interval_nhds_right hr.1 (hr.2.trans_le hc))
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun r _ => (lip r).lipschitzOnWith) ub f' (fun _ _ => mem_univ _)
    vb g' (fun _ _ => mem_univ _) h ⟨ht,le_rfl⟩

/-- Solve on the whole right half-line by finite continuation. Uniqueness
on overlaps identifies the chosen finite solutions. -/
theorem global_right_trajectory (F : ℝ → E → E) (K : ℝ≥0)
    (lip : ∀ r, LipschitzWith K (F r)) (zero : ∀ r, F r 0 = 0)
    (cont : ∀ x, Continuous (fun r => F r x)) (a : ℝ) (x : E) :
    ∃ u : ℝ → E, u a = x ∧
      ∀ r ∈ Ici a, HasDerivWithinAt u (F r (u r)) (Ici a) r := by
  let τ : ℝ := 1/(2*((K:ℝ)+1))
  have τpos : 0 < τ := by dsimp only [τ]; positivity
  have short : (K:ℝ)*τ ≤ 1/2 := by
    dsimp only [τ]
    have pos : (0:ℝ) < 2*((K:ℝ)+1) := by positivity
    rw [mul_one_div,div_le_iff₀ pos]
    linarith
  let endAt (n : ℕ) : ℝ := a+((n:ℝ)+1)*τ
  have succ (n : ℕ) : endAt (n+1) = endAt n+τ := by
    dsimp only [endAt]
    push_cast
    ring
  have all : ∀ n : ℕ, ∃ u : ℝ → E, u a = x ∧
      ∀ r ∈ Icc a (endAt n), HasDerivWithinAt u (F r (u r)) (Icc a (endAt n)) r := by
    intro n
    induction n with
    | zero =>
        simpa [endAt] using uniform_picard_step F K lip zero cont a τ τpos.le short x
    | succ n ih =>
        obtain ⟨u,at_a,du⟩ := ih
        obtain ⟨v,at_end,dv⟩ := uniform_picard_step F K lip zero cont (endAt n) τ τpos.le short (u (endAt n))
        have bound : a ≤ endAt n := by
          dsimp only [endAt]
          have pos : 0 ≤ ((n:ℝ)+1)*τ := by positivity
          linarith
        refine ⟨joinAt (endAt n) u v,by rw [joinAt,if_pos bound,at_a],?_⟩
        apply joined_derivative _ _ _ _ _ at_end.symm
        · intro r hr
          exact (du r ⟨hr.1.1,hr.2⟩).mono fun y hy => ⟨hy.1.1,hy.2⟩
        · intro r hr
          have included : Icc a (endAt (n+1)) ∩ Ici (endAt n) ⊆ Icc (endAt n) (endAt n+τ) :=
            fun y hy => ⟨hy.2,succ n ▸ hy.1.2⟩
          exact (dv r (included hr)).mono included
  choose candidates law using all
  have reach (r : ℝ) : ∃ n, r < endAt n := by
    obtain ⟨n,hn⟩ := exists_nat_gt ((r-a)/τ)
    have wide := (div_lt_iff₀ τpos).1 hn
    exact ⟨n,by dsimp only [endAt]; nlinarith⟩
  let select (r : ℝ) : ℕ := (reach r).choose
  let u := fun r => candidates (select r) r
  have coincides (n : ℕ) : EqOn u (candidates n) (Icc a (endAt n)) := by
    intro r hr
    change candidates (select r) r = candidates n r
    exact closed_interval_agreement F K lip _ _ ((law _).1.trans (law n).1.symm) hr.1
      (reach r).choose_spec.le hr.2 (law _).2 (law n).2
  refine ⟨u,(law (select a)).1,?_⟩
  intro r hr
  let n := select r
  have rt : r < endAt n := (reach r).choose_spec
  have side : Icc a (endAt n) ∈ 𝓝[Ici a] r := by
    refine mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds rt))) ?_
    exact fun y hy => ⟨hy.1,hy.2.le⟩
  have equal : u =ᶠ[𝓝[Ici a] r] candidates n := mem_of_superset side (coincides n)
  rw [coincides n ⟨hr,rt.le⟩]
  exact (((law n).2 r ⟨hr,rt.le⟩).mono_of_mem_nhdsWithin side).congr_of_eventuallyEq_of_mem equal hr

#print axioms joined_derivative
#print axioms global_right_trajectory

end
end SchwarzschildLaurent.LinearWave
