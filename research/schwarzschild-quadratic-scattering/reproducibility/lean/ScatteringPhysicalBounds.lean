import RetardedStrainError
import ScatteringPrefactorCircle

/-! Transfer bounds on the actual linear waves into the second
strain formula, with the even-parent incidence convention. -/
namespace SchwarzschildMixtures.Strain

open SchwarzschildLaurent.Outgoing SchwarzschildLaurent.LinearWave

noncomputable section

theorem parent_incidence_unit (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    ‖parentAlpha k n‖ = 1 := by
  let g := parentRate n
  have unit := prefactor_circle_parameter_unit g (parent_rate_positive n hn) k ki
  have plus : k+(g:ℂ) ≠ 0 := by
    rw [parent_rate_cast,add_comm]
    exact gamma_add_frequency n hn k ki
  have minus : (g:ℂ)-k ≠ 0 := by
    rw [parent_rate_cast,sub_eq_add_neg]
    exact gamma_add_frequency n hn (-k) (by simp [ki])
  have product : parentAlpha k n*((k-(g:ℂ))/(k+(g:ℂ))) = -1 := by
    simp only [parentAlpha,← parent_rate_cast n]
    change ((g:ℂ)+k)/((g:ℂ)-k)*((k-(g:ℂ))/(k+(g:ℂ))) = -1
    field_simp [plus,minus]
    ring
  have norm := congrArg (fun z : ℂ => ‖z‖) product
  rwa [norm_mul,unit,mul_one,norm_neg,norm_one] at norm

theorem unit_even_incidence_reflection_loss (n : ℕ) (hn : 2 ≤ n) (k a : ℂ)
    (hk : k ≠ 0) (ki : k.re = 0)
    (parent : IngoingWaveData k (angularEigenvalue n) a)
    (incident : parent.incoming = parentAlpha k n) :
    1-‖parent.outgoing‖^2 = ‖a‖^2 := by
  have flux := ingoing_scattering_flux k hk ki n a parent
  simp only [incident,← Complex.sq_norm,parent_incidence_unit n hn k ki,one_pow] at flux
  linarith

/-- A lower bound on unit-horizon incident amplitude gives a bound on
the physically normalized strain for every daughter reflection phase. -/
theorem second_strain_floor_from_incident (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (parent : IngoingWaveData k (angularEigenvalue n) 1)
    (daughter : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1)
    {B : ℝ} (Bpos : 0 < B) (Bgain : B ≤ ‖parent.incoming‖) :
    ‖secondResponsePrefactor n k‖*
      (‖prefactorRatio (parentRate n) (daughterRate n) k‖*(1-1/B^2)-1) ≤
      ‖printedResponse true k n (parentAlpha k n*(parent.outgoing/parent.incoming))
        (daughter.outgoing/daughter.incoming)‖ := by
  let rp := parentAlpha k n*(parent.outgoing/parent.incoming)
  let rd := daughter.outgoing/daughter.incoming
  let C := ‖prefactorRatio (parentRate n) (daughterRate n) k‖
  have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  have dr : ‖rd‖ ≤ 1 := (ingoing_amplitude_gains _ _ wk wi daughter).2.le
  have fraction : ‖rp‖^2 = 1-1/‖parent.incoming‖^2 := by
    simp only [rp,norm_mul,parent_incidence_unit n hn k ki,one_mul]
    exact unit_horizon_reflected_fraction k n hk ki parent
  have reciprocal : 1/‖parent.incoming‖^2 ≤ 1/B^2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos Bpos) ((sq_le_sq₀ Bpos.le (norm_nonneg _)).2 Bgain)
  have reflect : 1-1/B^2 ≤ ‖rp‖^2 := by
    rw [fraction]
    exact sub_le_sub_left reciprocal 1
  calc
    _ ≤ ‖secondResponsePrefactor n k‖*(C*‖rp‖^2-‖rd‖) :=
      mul_le_mul_of_nonneg_left (sub_le_sub (mul_le_mul_of_nonneg_left reflect (norm_nonneg _)) dr) (norm_nonneg _)
    _ ≤ _ := printed_second_magnitude_floor n hn k rp rd ki

#print axioms parent_incidence_unit
#print axioms unit_even_incidence_reflection_loss
#print axioms second_strain_floor_from_incident

end
end SchwarzschildMixtures.Strain
