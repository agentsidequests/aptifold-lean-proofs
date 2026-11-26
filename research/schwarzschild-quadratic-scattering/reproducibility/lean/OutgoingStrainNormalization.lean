import OutgoingAngularScale
import OutgoingMixtureLimits

/-! Physical strain normalization and signs of the parity projection. -/
namespace SchwarzschildMixtures.Strain

open SchwarzschildLaurent.Outgoing SchwarzschildMixtures.OutgoingData

noncomputable section

def parentAlpha (k ell : ℂ) : ℂ := (gamma ell+k)/(gamma ell-k)

def mixtureRatio (second : Bool) (k ell : ℂ) : ℂ :=
  if second then alternativeRatio k ell else 1

def incidentFactor (second : Bool) (k ell : ℂ) : ℂ :=
  1+mixtureRatio second k ell*parentAlpha k ell

def strainScale (second : Bool) (k : ℂ) (n : ℕ) : ℂ :=
  (angularScale n : ℂ)/(incidentFactor second k n)^2

def boundaryResponse (second : Bool) (k ell rp rd : ℂ) : ℂ :=
  endpointOutgoing second k ell*rp^2-(parentAlpha k ell)^2*endpointIncoming second k ell*rd

def printedResponse (second : Bool) (k : ℂ) (n : ℕ) (rp rd : ℂ) : ℂ :=
  let g := gamma (n : ℂ)
  let G := daughterGamma (n : ℂ)
  let K : ℂ := (printedScale n : ℂ)
  if second then K/(4*G)*(k*(k-g^2/G)/(k+g)^2*rp^2+k/(k-G)*rd)
  else K*k^2/(4*g^2*(k-G))*rd

private theorem gamma_minus (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    gamma (n : ℂ)-k ≠ 0 := by
  simpa only [sub_eq_add_neg] using gamma_add_frequency n hn (-k) (by simp [ki])

private theorem gap_nonzero (n : ℕ) (hn : 2 ≤ n) : daughterGamma (n : ℂ)-gamma (n : ℂ) ≠ 0 := by
  intro e
  exact (gap_positive n hn).ne' (by rw [e,Complex.zero_re])

private theorem daughter_nonzero (n : ℕ) (hn : 2 ≤ n) : daughterGamma (n : ℂ) ≠ 0 := by
  intro e
  have g := gamma_positive n hn
  have h := gap_positive n hn
  rw [e, Complex.sub_re, Complex.zero_re] at h
  linarith

theorem incident_factor_first (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    incidentFactor false k n = 2*gamma (n : ℂ)/(gamma (n : ℂ)-k) := by
  simp only [incidentFactor,mixtureRatio,Bool.false_eq_true,if_false,one_mul,parentAlpha]
  field_simp [gamma_minus n hn k ki]
  ring

theorem incident_factor_second (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    incidentFactor true k n = 2*daughterGamma (n : ℂ)/(daughterGamma (n : ℂ)-gamma (n : ℂ)) := by
  simp [incidentFactor,mixtureRatio,parentAlpha,alternativeRatio]
  field_simp [gamma_minus n hn k ki,gamma_add_frequency n hn k ki,gap_nonzero n hn]
  ring

theorem incident_factor_nonzero (second : Bool) (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    incidentFactor second k n ≠ 0 := by
  cases second
  · rw [incident_factor_first n hn k ki]
    apply div_ne_zero (mul_ne_zero (by norm_num) ?_) (gamma_minus n hn k ki)
    intro e
    exact (gamma_positive n hn).ne' (by rw [e,Complex.zero_re])
  · rw [incident_factor_second n hn k ki]
    exact div_ne_zero (mul_ne_zero (by norm_num) (daughter_nonzero n hn)) (gap_nonzero n hn)

/-- Unit even incidence and the reference-parent odd amplitude.
The incoming strain uses the plus sign between the parity contributions. -/
theorem incident_strain (second : Bool) (n : ℕ) (k : ℂ) :
    (masterFactor n : ℂ)*(1+Complex.I*(-Complex.I*mixtureRatio second k n*parentAlpha k n)) =
      (masterFactor n : ℂ)*incidentFactor second k n := by
  unfold incidentFactor
  have i : Complex.I*Complex.I = -1 := Complex.I_mul_I
  linear_combination -(masterFactor n : ℂ)*mixtureRatio second k n*parentAlpha k n*i

/-- The two plane-wave coefficients of the Darboux map. -/
theorem parent_darboux_readout (g k E_in E_out : ℂ) (h : g-k ≠ 0) :
    (g*E_in-(-k)*E_in)/(g-k) = (g+k)/(g-k)*E_in ∧
      (g*E_out-k*E_out)/(g-k) = E_out := by
  constructor <;> field_simp [h] <;> ring

theorem daughter_darboux_readout (G k E O : ℂ) (h : G-k ≠ 0) :
    (2*G*E-(-2*k)*E)/(2*(G-k))-Complex.I*O = (G+k)/(G-k)*E-Complex.I*O ∧
      (2*G*E-(2*k)*E)/(2*(G-k))-Complex.I*O = E-Complex.I*O := by
  constructor <;> field_simp [h] <;> ring

/-- Cancelling the incoming strain alone would allow a nonzero incoming
projected master. Independent parity boundary conditions are needed. -/
theorem incoming_strain_cancellation_control (G k : ℂ) (hG : G ≠ 0) (h : G-k ≠ 0) :
    (1 : ℂ)+Complex.I*Complex.I = 0 ∧ (G+k)/(G-k)-Complex.I*Complex.I ≠ 0 := by
  rw [Complex.I_mul_I]
  refine ⟨by ring,?_⟩
  have e : (G+k)/(G-k)-(-1) = 2*G/(G-k) := by field_simp [h]; ring
  rw [e]
  exact div_ne_zero (mul_ne_zero (by norm_num) hG) h

theorem angular_scale_factor (n : ℕ) (hn : 2 ≤ n) :
    (angularScale n : ℂ)*rationalAngularFactor (n : ℂ) = (printedScale n : ℂ) := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (angular_scale_matches_printed_factor n hn)
  change (↑(angularScale n*angularQuotient n) : ℂ) = (printedScale n : ℂ) at h
  simpa only [angularQuotient,angularCubic,rationalAngularFactor,rationalAngularNumerator,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_pow,
    Complex.ofReal_natCast,Complex.ofReal_ofNat,Complex.ofReal_one] using h

theorem normalized_closed_response (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k rp rd : ℂ) (ki : k.re = 0) :
    strainScale second k n * boundaryResponse second k n rp rd =
      printedResponse second k n rp rd := by
  have minus := gamma_minus n hn k ki
  have plus : k+gamma (n : ℂ) ≠ 0 := by simpa [add_comm] using gamma_add_frequency n hn k ki
  have daughter := frequency_sub_daughter n hn k ki
  have gap := gap_nonzero n hn
  have G := daughter_nonzero n hn
  have g : gamma (n : ℂ) ≠ 0 := by
    intro e
    exact (gamma_positive n hn).ne' (by rw [e,Complex.zero_re])
  unfold strainScale boundaryResponse printedResponse
  rw [← angular_scale_factor n hn]
  cases second
  · rw [incident_factor_first n hn k ki]
    simp only [endpointOutgoing,endpointIncoming,parentAlpha,Bool.false_eq_true,if_false,zero_mul]
    field_simp [g,minus,plus,daughter] <;> ring
  · rw [incident_factor_second n hn k ki]
    simp [endpointOutgoing,endpointIncoming,parentAlpha]
    field_simp [G,minus,plus,daughter,gap] <;> ring

#print axioms incident_factor_nonzero
#print axioms incident_strain
#print axioms daughter_darboux_readout
#print axioms incoming_strain_cancellation_control
#print axioms normalized_closed_response

end
end SchwarzschildMixtures.Strain
