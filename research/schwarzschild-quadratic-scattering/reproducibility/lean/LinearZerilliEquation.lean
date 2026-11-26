import LinearDarboux
import LinearScatteringData
import EinsteinProjection

/-! Bind the inverse Darboux map to the manuscript's Schwarzschild
superpotential and the actual Zerilli wave equation. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set
open scoped Topology
open SchwarzschildLaurent.Outgoing SchwarzschildLaurent.Horizon
open SchwarzschildMixtures SchwarzschildMixtures.Strain

noncomputable section

def polarLambda (n : ℕ) : ℂ := ((n : ℂ)-1)*(n+2)/2

def schwarzschildW (n : ℕ) (r : ℂ) : ℂ :=
  SchwarzschildEinstein.superpotential r (polarLambda n)

def zerilliPotential (w : ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  w^2+SchwarzschildEinstein.zerilli (r : ℂ) (polarLambda n)

private def superpotentialJet (lam r : ℂ) : ℂ :=
  let f := SchwarzschildEinstein.lapse r
  let den := r*(lam*r+3)
  f*(3*((2/r^2)*den-f*(2*lam*r+3))/den^2)

private theorem gamma_lambda (n : ℕ) :
    SchwarzschildEinstein.algebraicFrequency (polarLambda n) = gamma n := by
  unfold SchwarzschildEinstein.algebraicFrequency polarLambda gamma
  ring

private theorem angular_lambda (n : ℕ) : 2*polarLambda n+2 = angularEigenvalue n := by
  unfold polarLambda angularEigenvalue
  ring

private theorem lambda_cast (n : ℕ) :
    polarLambda n = (↑(((n:ℝ)-1)*(n+2)/2 : ℝ) : ℂ) := by
  unfold polarLambda
  push_cast
  rfl

private theorem lambda_positive (n : ℕ) (hn : 2 ≤ n) : 0 < ((n:ℝ)-1)*(n+2)/2 := by
  have p : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have m : (0:ℝ) < (n:ℝ)-1 := by linarith
  positivity

private theorem lambda_ne_zero (n : ℕ) (hn : 2 ≤ n) : polarLambda n ≠ 0 := by
  rw [lambda_cast]
  exact_mod_cast (lambda_positive n hn).ne'

private theorem polar_denominator (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (pos : 0 < r) :
    polarLambda n*(r : ℂ)+3 ≠ 0 := by
  have real : 0 < ((n:ℝ)-1)*(n+2)/2*r+3 :=
    add_pos (mul_pos (lambda_positive n hn) pos) (by norm_num)
  have cast : polarLambda n*(r : ℂ)+3 = (↑(((n:ℝ)-1)*(n+2)/2*r+3 : ℝ) : ℂ) := by
    rw [lambda_cast]
    push_cast
    rfl
  rw [cast]
  exact_mod_cast real.ne'

private theorem lapse_matches (r : ℝ) (hr : 2 < r) :
    SchwarzschildEinstein.lapse (r : ℂ) = radiusLapse r := by
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  unfold SchwarzschildEinstein.lapse radiusLapse
  field_simp [nz]

private theorem scalar_superpotential_derivative (lam r : ℂ) (r0 : r ≠ 0) (d0 : lam*r+3 ≠ 0) :
    HasDerivAt (fun s : ℂ => SchwarzschildEinstein.superpotential s lam)
      (3*((2/r^2)*(r*(lam*r+3))-SchwarzschildEinstein.lapse r*(2*lam*r+3))/(r*(lam*r+3))^2) r := by
  have lapseDer : HasDerivAt (fun s : ℂ => SchwarzschildEinstein.lapse s) (2/r^2) r := by
    have d := (hasDerivAt_const r (1:ℂ)).sub ((hasDerivAt_const r (2:ℂ)).div (hasDerivAt_id r) r0)
    apply d.congr_deriv
    simp [neg_div]
  have denDer : HasDerivAt (fun s : ℂ => s*(lam*s+3)) (2*lam*r+3) r := by
    have d := (hasDerivAt_id r).mul (((hasDerivAt_id r).const_mul lam).add_const 3)
    apply d.congr_deriv
    simp
    ring
  have d := ((lapseDer.const_mul 3).div denDer (mul_ne_zero r0 d0)).const_add
    (SchwarzschildEinstein.algebraicFrequency lam)
  apply d.congr_deriv
  ring

private theorem exterior_superpotential_jet (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 2 < r) :
    HasDerivAt (fun s : ℝ => schwarzschildW n (s : ℂ))
      (superpotentialJet (polarLambda n) (r : ℂ)/radiusLapse r) r := by
  have pos : 0 < r := by linarith
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  have law := (scalar_superpotential_derivative (polarLambda n) (r : ℂ) nz (polar_denominator n hn r pos)).comp_ofReal
  apply law.congr_deriv
  simp only [superpotentialJet,lapse_matches r hr,mul_div_cancel_left₀ _ (exterior_lapse_nonzero hr)]

private theorem scalar_factorization (lam r : ℂ) (r0 : r ≠ 0) (d0 : lam*r+3 ≠ 0) :
    let W := SchwarzschildEinstein.superpotential r lam
    let g := SchwarzschildEinstein.algebraicFrequency lam
    let d := superpotentialJet lam r
    SchwarzschildEinstein.reggeWheeler r lam = W^2-d-g^2 ∧
      SchwarzschildEinstein.zerilli r lam = W^2+d-g^2 := by
  dsimp only [SchwarzschildEinstein.superpotential,SchwarzschildEinstein.algebraicFrequency,
    SchwarzschildEinstein.reggeWheeler,SchwarzschildEinstein.zerilli,SchwarzschildEinstein.lapse,
    superpotentialJet]
  generalize same : lam*r+3 = p at d0 ⊢
  constructor <;> field_simp [r0,d0] <;> rw [← same] <;> ring

private theorem exterior_partner_potentials (w : ℂ) (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 2 < r) :
    darbouxCenter w (gamma n) (schwarzschildW n (r : ℂ))-superpotentialJet (polarLambda n) (r : ℂ) =
      rwPotential w (angularEigenvalue n) r ∧
    darbouxCenter w (gamma n) (schwarzschildW n (r : ℂ))+superpotentialJet (polarLambda n) (r : ℂ) =
      zerilliPotential w n r := by
  have pos : 0 < r := by linarith
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  obtain ⟨odd,even⟩ := scalar_factorization (polarLambda n) (r : ℂ) nz (polar_denominator n hn r pos)
  simp only [gamma_lambda] at odd even
  have rwval : SchwarzschildEinstein.reggeWheeler (r : ℂ) (polarLambda n) =
      radiusLapse r*tailPotential (angularEigenvalue n) r := by
    rw [SchwarzschildEinstein.reggeWheeler,lapse_matches r hr,angular_lambda]
    rfl
  rw [rwval] at odd
  constructor
  · change _ = w^2+radiusLapse r*tailPotential (angularEigenvalue n) r
    unfold darbouxCenter schwarzschildW
    linear_combination -odd
  · unfold darbouxCenter zerilliPotential schwarzschildW
    linear_combination -even

theorem schwarzschild_superpotential_limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun r : ℝ => schwarzschildW n (r : ℂ)) atTop (𝓝 (gamma n)) := by
  have t := inverse_radius_tends_to_zero
  have den : Tendsto (fun r => polarLambda n+3*inverseRadius r) atTop (𝓝 (polarLambda n)) := by
    simpa only [mul_zero,add_zero] using (t.const_mul 3).const_add (polarLambda n)
  have tail := ((lapse_tends_to_one.const_mul 3).mul (t.pow 2)).div den (lambda_ne_zero n hn)
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_div] at tail
  have total := (tendsto_const_nhds (x := gamma n)).add tail
  rw [add_zero] at total
  apply total.congr'
  filter_upwards [eventually_gt_atTop (2:ℝ)] with r hr
  have pos : 0 < r := by linarith
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  have pole := polar_denominator n hn r pos
  change gamma n+3*radiusLapse r*((r:ℂ)⁻¹)^2/(polarLambda n+3*(r:ℂ)⁻¹) = schwarzschildW n (r:ℂ)
  have rewrite : polarLambda n+3*(r:ℂ)⁻¹ = (polarLambda n*(r:ℂ)+3)/(r:ℂ) := by
    field_simp [nz]
  rw [rewrite,schwarzschildW,SchwarzschildEinstein.superpotential,gamma_lambda,lapse_matches r hr]
  field_simp [nz,pole]

theorem schwarzschild_superpotential_horizon (n : ℕ) (hn : 2 ≤ n) :
    AnalyticAt ℂ (schwarzschildW n) 2 ∧ schwarzschildW n 2 = gamma n := by
  have two : (2:ℂ) ≠ 0 := by norm_num
  have pole : polarLambda n*2+3 ≠ 0 := by simpa using polar_denominator n hn 2 (by norm_num)
  have f : AnalyticAt ℂ (fun r : ℂ => 1-2/r) 2 :=
    (analyticAt_const (v := (1:ℂ))).fun_sub ((analyticAt_const (v := (2:ℂ))).fun_div analyticAt_id two)
  have d : AnalyticAt ℂ (fun r : ℂ => r*(polarLambda n*r+3)) 2 := by fun_prop
  have q := ((analyticAt_const (v := (3:ℂ))).fun_mul f).fun_div d (mul_ne_zero two pole)
  refine ⟨(analyticAt_const (v := SchwarzschildEinstein.algebraicFrequency (polarLambda n))).fun_add q,?_⟩
  simp only [schwarzschildW,SchwarzschildEinstein.superpotential,SchwarzschildEinstein.lapse,gamma_lambda]
  norm_num

theorem zerilli_partner_equation (n : ℕ) (hn : 2 ≤ n) (w a : ℂ)
    (j : IngoingWaveData w (angularEigenvalue n) a) :
    RadialEquation radiusLapse (zerilliPotential w n) 0
      (fun r => inverseDarbouxValue w (gamma n) (schwarzschildW n (r : ℂ)) (j.value r) (j.jet r))
      (fun r => inverseDarbouxJet w (gamma n) (schwarzschildW n (r : ℂ)) (j.value r) (j.jet r)) := by
  let W := fun r : ℝ => schwarzschildW n (r : ℂ)
  let Wd := fun r : ℝ => superpotentialJet (polarLambda n) (r : ℂ)
  have odd : RadialEquation radiusLapse (fun r => darbouxCenter w (gamma n) (W r)-Wd r) 0 j.value j.jet :=
    ⟨j.equation.value,fun r hr => by
      simpa only [W,Wd,(exterior_partner_potentials w n hn r hr).1] using j.equation.jet r hr⟩
  have even := inverse_darboux_equation w (gamma n) radiusLapse W Wd j.value j.jet
    (fun _ hr => exterior_lapse_nonzero hr) (exterior_superpotential_jet n hn) odd
  exact ⟨even.value,fun r hr => by
    simpa only [W,Wd,(exterior_partner_potentials w n hn r hr).2] using even.jet r hr⟩

#print axioms schwarzschild_superpotential_limit
#print axioms schwarzschild_superpotential_horizon
#print axioms zerilli_partner_equation

end
end SchwarzschildLaurent.LinearWave
