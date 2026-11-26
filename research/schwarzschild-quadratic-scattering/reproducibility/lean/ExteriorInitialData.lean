import LinearExteriorWave

/-! A homogeneous solution with assigned value and tortoise jet at an
interior radius. The one-sided continuation has the full derivative
at the starting radius by an affine continuation on the unused side. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set SchwarzschildLaurent.Outgoing
open scoped Topology

noncomputable section

theorem exterior_wave_from_initial_data (w L : ℂ) {a : ℝ} (ha : 2 < a) (b c : ℂ) :
    ∃ u du : ℝ → ℂ, u a = b ∧ du a = c ∧
      ∀ r : ℝ, a ≤ r →
        HasDerivAt u (du r/radiusLapse r) r ∧
        HasDerivAt du (rwPotential w L r*u r/radiusLapse r) r := by
  let initial : ℂ × ℂ := (b,c)
  let F := fun (r : ℝ) => exteriorSystem w L (max r a)
  have lip := exterior_clamped_system_lipschitz w L ha
  have zero (r : ℝ) : F r 0 = 0 := by simp [F,exteriorSystem]
  have cont (y : ℂ × ℂ) : Continuous (fun r => F r y) := by
    let t := fun r : ℝ => ((max r a:ℝ):ℂ)
    have T : Continuous t := Complex.continuous_ofReal.comp (continuous_id.max continuous_const)
    have nz (r : ℝ) : t r ≠ 0 := by
      have positive : 0 < max r a := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      exact Complex.ofReal_ne_zero.mpr positive.ne'
    have pole (r : ℝ) : t r-2 ≠ 0 := by
      have outside : 2 < max r a := ha.trans_le (le_max_right _ _)
      change ((max r a:ℝ):ℂ)-2 ≠ 0
      exact sub_ne_zero.mpr (by exact_mod_cast outside.ne')
    have W : Continuous (fun r => exteriorWeight (max r a)) := by
      unfold exteriorWeight
      exact continuous_const.add (continuous_const.div (T.sub continuous_const) pole)
    have V : Continuous (fun r => tailPotential L (max r a)) := by
      unfold tailPotential
      exact (continuous_const.div (T.pow 2) (fun r => pow_ne_zero _ (nz r))).sub
        (continuous_const.div (T.pow 3) (fun r => pow_ne_zero _ (nz r)))
    exact (continuous_const.mul W).prodMk
      (((continuous_const.mul W).add V).mul continuous_const)
  obtain ⟨right,atA,rightDeriv⟩ := global_right_trajectory F _ lip zero cont a initial
  let slope := F a initial
  let left := fun r : ℝ => initial+(r-a) • slope
  let system := fun (r : ℝ) y => if a ≤ r then F r y else slope
  let Y := joinAt a left right
  have leftA : left a = initial := by simp [left]
  have dl (r : ℝ) (hr : r ∈ univ ∩ Iic a) :
      HasDerivWithinAt left (system r (left r)) (univ ∩ Iic a) r := by
    have raw : HasDerivAt left slope r := by
      dsimp only [left]
      simpa only [one_smul,id_eq] using
        ((((hasDerivAt_id r).sub_const a).smul_const slope).const_add initial)
    by_cases ar : a ≤ r
    · have eq := le_antisymm (show r ≤ a from hr.2) ar
      subst r
      simpa only [system,if_pos le_rfl,leftA] using raw.hasDerivWithinAt
    · simpa only [system,if_neg ar] using raw.hasDerivWithinAt
  have dr (r : ℝ) (hr : r ∈ univ ∩ Ici a) :
      HasDerivWithinAt right (system r (right r)) (univ ∩ Ici a) r := by
    simpa only [system,if_pos (show a ≤ r from hr.2),univ_inter] using rightDeriv r hr.2
  have Dy (r : ℝ) (ar : a ≤ r) :
      HasDerivAt Y (exteriorSystem w L r (Y r)) r := by
    have raw := joined_derivative system univ a left right (leftA.trans atA.symm) dl dr r (mem_univ r)
    simpa only [Y,system,F,if_pos ar,max_eq_left ar,hasDerivWithinAt_univ] using raw
  have Yinit : Y a = initial := by simpa only [Y,joinAt,if_pos le_rfl] using leftA
  refine ⟨fun r => (Y r).1,fun r => (Y r).2,congrArg Prod.fst Yinit,congrArg Prod.snd Yinit,?_⟩
  intro r ar
  have proof := Dy r ar
  rw [exterior_system_eq w L r (ha.trans_le ar)] at proof
  exact ⟨(ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r proof,
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r proof⟩

#print axioms exterior_wave_from_initial_data

end
end SchwarzschildLaurent.LinearWave
