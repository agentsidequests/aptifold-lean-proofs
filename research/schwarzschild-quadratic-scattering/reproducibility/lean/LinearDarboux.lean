import LinearScatteringModes
import Mathlib.Topology.Order.LiminfLimsup

/-! Invert the normalized Darboux map on a real-frequency homogeneous
wave. The same amplitude readout is used before and after the map. -/
namespace SchwarzschildLaurent.LinearWave

open Filter
open scoped Topology
open SchwarzschildLaurent.Outgoing SchwarzschildMixtures

noncomputable section

def darbouxCenter (w g W : ℂ) : ℂ := w^2+W^2-g^2

def inverseDarbouxValue (w g W u du : ℂ) : ℂ := (W*u+du)/(g+w)

def inverseDarbouxJet (w g W u du : ℂ) : ℂ :=
  (W*du+darbouxCenter w g W*u)/(g+w)

theorem inverse_darboux_equation (w g : ℂ) (f W dW u du : ℝ → ℂ)
    (nonzero : ∀ r, 2 < r → f r ≠ 0)
    (Wjet : ∀ r, 2 < r → HasDerivAt W (dW r/f r) r)
    (odd : RadialEquation f (fun r => darbouxCenter w g (W r)-dW r) 0 u du) :
    RadialEquation f (fun r => darbouxCenter w g (W r)+dW r) 0
      (fun r => inverseDarbouxValue w g (W r) (u r) (du r))
      (fun r => inverseDarbouxJet w g (W r) (u r) (du r)) := by
  constructor <;> intro r hr
  · have d := (((Wjet r hr).mul (odd.value r hr)).add (odd.jet r hr)).div_const (g+w)
    apply d.congr_deriv
    simp only [Pi.zero_apply,add_zero,inverseDarbouxJet]
    field_simp [nonzero r hr]
    ring
  · have dbase : HasDerivAt (fun r => darbouxCenter w g (W r)) (2*W r*dW r/f r) r := by
      have raw := (((Wjet r hr).mul (Wjet r hr)).const_add (w^2)).sub_const (g^2)
      have deriv : dW r/f r*W r+W r*(dW r/f r) = 2*W r*dW r/f r := by ring
      simpa only [darbouxCenter,pow_two,Pi.mul_apply] using raw.congr_deriv deriv
    have d := (((Wjet r hr).mul (odd.jet r hr)).add (dbase.mul (odd.value r hr))).div_const (g+w)
    apply d.congr_deriv
    simp only [Pi.zero_apply,add_zero,inverseDarbouxValue]
    field_simp [nonzero r hr]
    ring

theorem darboux_recovers_odd (w g W u du : ℂ) (plus : g+w ≠ 0) (minus : g-w ≠ 0) :
    (W*inverseDarbouxValue w g W u du - inverseDarbouxJet w g W u du)/(g-w) = u := by
  unfold inverseDarbouxValue inverseDarbouxJet darbouxCenter
  field_simp [plus,minus]
  ring

private theorem inverse_modes_exact (w g W m p u du : ℂ) (hw : w ≠ 0) (hg : g+w ≠ 0) :
    incomingMode w p (inverseDarbouxValue w g W u du) (inverseDarbouxJet w g W u du) =
      (W-w)/(g+w)*incomingMode w p u du-p*((W^2-g^2)*u/(2*w*(g+w))) ∧
    outgoingMode w m (inverseDarbouxValue w g W u du) (inverseDarbouxJet w g W u du) =
      (W+w)/(g+w)*outgoingMode w m u du+m*((W^2-g^2)*u/(2*w*(g+w))) := by
  unfold incomingMode outgoingMode inverseDarbouxValue inverseDarbouxJet darbouxCenter
  constructor <;> field_simp [hw,hg] <;> ring

private theorem wave_norm_bounded (w : ℂ) (hw : w ≠ 0) (wi : w.re = 0) (u du : ℝ → ℂ)
    (ai ao : ℂ) (lim : ModeLimits atTop w (incomingCarrier w) (outgoingCarrier w) u du ai ao) :
    IsBoundedUnder (· ≤ ·) atTop (norm ∘ u) := by
  obtain ⟨cap,hcap⟩ := (lim.incoming.norm.add lim.outgoing.norm).isBoundedUnder_le
  refine ⟨cap,Filter.eventually_map.2 ?_⟩
  have ev := Filter.eventually_map.1 hcap
  filter_upwards [ev] with r hr
  let m := incomingCarrier w r
  let p := outgoingCarrier w r
  let ai' := incomingMode w p (u r) (du r)
  let ao' := outgoingMode w m (u r) (du r)
  have nm : ‖m‖ = 1 := phase_norm (-w) (by simp [wi]) (realTortoise r)
  have np : ‖p‖ = 1 := phase_norm w wi (realTortoise r)
  have wave_eq : wave ai' ao' m p = u r :=
    (reconstruct_modes w m p (u r) (du r) hw (opposite_phases w (realTortoise r))).1
  change ‖u r‖ ≤ cap
  calc
    _ = ‖ai'*m+ao'*p‖ := by rw [← wave_eq]; rfl
    _ ≤ ‖ai'*m‖+‖ao'*p‖ := norm_add_le _ _
    _ = ‖ai'‖+‖ao'‖ := by simp [nm,np]
    _ ≤ _ := hr

theorem inverse_darboux_limits (w g : ℂ) (hw : w ≠ 0) (wi : w.re = 0) (hg : g+w ≠ 0)
    (W u du : ℝ → ℂ) (Wlim : Tendsto W atTop (𝓝 g)) (ai ao : ℂ)
    (odd : ModeLimits atTop w (incomingCarrier w) (outgoingCarrier w) u du ai ao) :
    ModeLimits atTop w (incomingCarrier w) (outgoingCarrier w)
      (fun r => inverseDarbouxValue w g (W r) (u r) (du r))
      (fun r => inverseDarbouxJet w g (W r) (u r) (du r)) ((g-w)/(g+w)*ai) ao := by
  have delta : Tendsto (fun r => (W r)^2-g^2) atTop (𝓝 0) := by
    have d := (Wlim.pow 2).sub_const (g^2)
    rw [sub_self] at d
    exact d
  have z := delta.zero_mul_isBoundedUnder_le (wave_norm_bounded w hw wi u du ai ao odd)
  have zero : Tendsto (fun r => ((W r)^2-g^2)*u r/(2*w*(g+w))) atTop (𝓝 0) := by
    simpa only [zero_div] using z.div_const (2*w*(g+w))
  have small₁ := unit_mul_zero (c := outgoingCarrier w) (fun r => phase_norm w wi (realTortoise r)) zero
  have small₂ := unit_mul_zero (c := incomingCarrier w)
    (fun r => phase_norm (-w) (by simp [wi]) (realTortoise r)) zero
  have leading₁ := (((Wlim.sub_const w).div_const (g+w)).mul odd.incoming).sub small₁
  have leading₂ := (((Wlim.add_const w).div_const (g+w)).mul odd.outgoing).add small₂
  simp only [sub_zero] at leading₁
  simp only [div_self hg,one_mul,add_zero] at leading₂
  refine ⟨leading₁.congr fun r => ?_,leading₂.congr fun r => ?_⟩
  · exact (inverse_modes_exact w g (W r) (incomingCarrier w r) (outgoingCarrier w r) (u r) (du r) hw hg).1.symm
  · exact (inverse_modes_exact w g (W r) (incomingCarrier w r) (outgoingCarrier w r) (u r) (du r) hw hg).2.symm

#print axioms inverse_darboux_equation
#print axioms darboux_recovers_odd
#print axioms inverse_darboux_limits

end
end SchwarzschildLaurent.LinearWave
