import OutgoingGreenIdentity
import Mathlib.Analysis.Normed.Ring.Lemmas

/-! Exact incoming and outgoing amplitudes of a wave and its radial jet.
Only the amplitudes have limits. The unit phases need not converge. -/
namespace SchwarzschildLaurent.Outgoing

open Filter
open scoped Topology

noncomputable section

def phase (w : ℂ) (x : ℝ) : ℂ := Complex.exp (w*(x : ℂ))

theorem opposite_phases (w : ℂ) (x : ℝ) : phase (-w) x*phase w x = 1 := by
  unfold phase
  rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]

theorem phase_norm (w : ℂ) (hw : w.re = 0) (x : ℝ) : ‖phase w x‖ = 1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,hw]

theorem phase_double (w : ℂ) (x : ℝ) : phase (2*w) x = phase w x ^ 2 := by
  unfold phase
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem unit_mul_zero {ι : Type*} {l : Filter ι} {c z : ι → ℂ}
    (hc : ∀ r, ‖c r‖ = 1) (hz : Tendsto z l (𝓝 0)) :
    Tendsto (fun r => c r*z r) l (𝓝 0) := by
  apply isBoundedUnder_le_mul_tendsto_zero _ hz
  have bound : ∀ᶠ r in l, ‖c r‖ ≤ 1 :=
    Eventually.of_forall fun r => by rw [hc r]
  exact ⟨1, Filter.eventually_map.2 bound⟩

def wave (ain aout m p : ℂ) : ℂ := ain*m+aout*p

def waveJet (w ain aout m p : ℂ) : ℂ := w*(aout*p-ain*m)

def incomingMode (w p v dv : ℂ) : ℂ := (v-dv/w)*p/2

def outgoingMode (w m v dv : ℂ) : ℂ := (v+dv/w)*m/2

structure ModeLimits {ι : Type*} (l : Filter ι) (w : ℂ) (m p v dv : ι → ℂ)
    (ain aout : ℂ) : Prop where
  incoming : Tendsto (fun r => incomingMode w (p r) (v r) (dv r)) l (𝓝 ain)
  outgoing : Tendsto (fun r => outgoingMode w (m r) (v r) (dv r)) l (𝓝 aout)

theorem reconstruct_modes (w m p v dv : ℂ) (hw : w ≠ 0) (hmp : m*p = 1) :
    wave (incomingMode w p v dv) (outgoingMode w m v dv) m p = v ∧
      waveJet w (incomingMode w p v dv) (outgoingMode w m v dv) m p = dv := by
  have left : incomingMode w p v dv*m = (v-dv/w)/2 := by
    unfold incomingMode
    linear_combination (v-dv/w)/2*hmp
  have right : outgoingMode w m v dv*p = (v+dv/w)/2 := by
    unfold outgoingMode
    linear_combination (v+dv/w)/2*hmp
  unfold wave waveJet
  rw [left,right]
  constructor <;> field_simp [hw] <;> ring

theorem modes_of_wave (w m p ain aout : ℂ) (hw : w ≠ 0) (hmp : m*p = 1) :
    incomingMode w p (wave ain aout m p) (waveJet w ain aout m p) = ain ∧
    outgoingMode w m (wave ain aout m p) (waveJet w ain aout m p) = aout := by
  unfold incomingMode outgoingMode wave waveJet
  simp only [mul_div_cancel_left₀ _ hw]
  constructor
  · linear_combination ain*hmp
  · linear_combination aout*hmp

theorem squared_phase_inverse (m p : ℂ) (hp : m*p = 1) : m^2*p^2 = 1 := by
  have square := congrArg (fun c : ℂ => c^2) hp
  change (m*p)^2 = (1:ℂ)^2 at square
  simpa only [mul_pow,one_pow] using square

/-- Opposite phases cancel in the bilinear current at every radius. -/
theorem current_of_mode_limits {ι : Type*} (l : Filter ι) (w : ℂ) (hw : w ≠ 0)
    (m p u du v dv : ι → ℂ) (phases : ∀ r, m r*p r = 1)
    (uin uout vin vout : ℂ) (hu : ModeLimits l w m p u du uin uout)
    (hv : ModeLimits l w m p v dv vin vout) :
    Tendsto (fun r => current (u r) (du r) (v r) (dv r)) l
      (𝓝 (2*w*(uin*vout-uout*vin))) := by
  have lim := ((hu.incoming.mul hv.outgoing).sub (hu.outgoing.mul hv.incoming)).const_mul (2*w)
  apply lim.congr
  intro r
  obtain ⟨uv,uj⟩ := reconstruct_modes w (m r) (p r) (u r) (du r) hw (phases r)
  obtain ⟨vv,vj⟩ := reconstruct_modes w (m r) (p r) (v r) (dv r) hw (phases r)
  let ai := incomingMode w (p r) (u r) (du r)
  let ao := outgoingMode w (m r) (u r) (du r)
  let bi := incomingMode w (p r) (v r) (dv r)
  let bo := outgoingMode w (m r) (v r) (dv r)
  calc
    _ = current (wave ai ao (m r) (p r)) (waveJet w ai ao (m r) (p r))
        (wave bi bo (m r) (p r)) (waveJet w bi bo (m r) (p r)) :=
      (signed_current w (m r) (p r) (phases r) ai ao bi bo).symm
    _ = _ := by dsimp only [ai,ao,bi,bo]; rw [uv,uj,vv,vj]

/-- A common ingoing carrier leaves only derivatives of the smooth
envelopes in the horizon current. -/
theorem ingoing_current_limit {ι : Type*} (l : Filter ι) (w : ℂ)
    (c U dU P dP : ι → ℂ) (hc : ∀ r, ‖c r‖ = 1) (u₀ p₀ : ℂ)
    (hU : Tendsto U l (𝓝 u₀)) (hP : Tendsto P l (𝓝 p₀))
    (hdU : Tendsto dU l (𝓝 0)) (hdP : Tendsto dP l (𝓝 0)) :
    Tendsto (fun r => current (c r*U r) (c r*(dU r-w*U r))
      (c r*P r) (c r*(dP r-w*P r))) l (𝓝 0) := by
  have vanishing : Tendsto (fun r => U r*dP r-P r*dU r) l (𝓝 0) := by
    simpa using (hU.mul hdP).sub (hP.mul hdU)
  apply (unit_mul_zero (c := fun r => c r^2) (fun r => by simp [norm_pow,hc r]) vanishing).congr
  intro r
  unfold current
  ring

#print axioms reconstruct_modes
#print axioms current_of_mode_limits
#print axioms ingoing_current_limit

end
end SchwarzschildLaurent.Outgoing
