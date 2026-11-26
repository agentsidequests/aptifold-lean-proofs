import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The highest-weight angular carrier and the radial projection used to
put the quadratic source into the common odd daughter equation. -/
namespace SchwarzschildEinstein

variable {K : Type*} [Field K]

/-- The coefficient formulas used by both vector and trace-free tensor
projection invert the two harmonic columns whenever the determinant is nonzero. -/
theorem harmonic_projection (A₁ A₂ B₁ B₂ x y : K) (nondegenerate : A₁*B₂-A₂*B₁ ≠ 0) :
    let U := A₁*x+B₁*y
    let V := A₂*x+B₂*y
    (U*B₂-V*B₁)/(A₁*B₂-A₂*B₁) = x ∧
      (A₁*V-A₂*U)/(A₁*B₂-A₂*B₁) = y := by
  dsimp only
  constructor <;> apply (div_eq_iff nondegenerate).2 <;> ring

variable [Algebra ℚ K] (D : Derivation ℚ K K)

/-- A derivative of the factored mode must still differentiate its carrier.
The same rule applies to radial, stereographic, time and azimuthal derivatives. -/
theorem carrier_derivative (p log u : K) (n : ℕ) (hp : D p = log*p) :
    D (p^n*u) = p^n*(D u+(n : K)*log*u) := by
  have power : D (p^n) = (n : K)*log*p^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, D.leibniz, ih, hp, Nat.cast_succ]
      simp only [smul_eq_mul]
      ring
  rw [D.leibniz, power]
  simp only [smul_eq_mul]
  ring

private theorem two_constant : D (2 : K) = 0 := D.map_natCast 2
private theorem three_constant : D (3 : K) = 0 := D.map_natCast 3

theorem stereographic_carrier (v : K) (dv : D v = 1) (hv : v ≠ 0) (hcoord : 1+v^2 ≠ 0) :
    D (2*v/(1+v^2)) = ((1-v^2)/(v*(1+v^2))) * (2*v/(1+v^2)) := by
  have nonzero : 1+v*v ≠ 0 := by simpa only [pow_two] using hcoord
  simp only [D.leibniz_div, D.leibniz, pow_two, map_add, D.map_one_eq_zero,
    two_constant, dv, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  field_simp [hv, nonzero]
  ring

def lapse (r : K) : K := 1-2/r
def algebraicFrequency (lam : K) : K := lam*(lam+1)/3
def superpotential (r lam : K) : K := algebraicFrequency lam+3*lapse r/(r*(lam*r+3))
def reggeWheeler (r lam : K) : K := lapse r*((2*lam+2)/r^2-6/r^3)
def zerilli (r lam : K) : K :=
  2*lapse r*(lam^2*(lam+1)*r^3+3*lam^2*r^2+9*lam*r+9)/(r^3*(lam*r+3)^2)

/-- Both Schwarzschild potentials share the same superpotential, with
opposite signs on its tortoise derivative. -/
theorem schwarzschild_potential_factorization [CharZero K] (r lam : K) (hr : r ≠ 0)
    (hpolar : lam*r+3 ≠ 0) (dr : D r = lapse r) (dl : D lam = 0) :
    let W := superpotential r lam
    let gamma := algebraicFrequency lam
    reggeWheeler r lam = W^2-D W-gamma^2 ∧
      zerilli r lam = W^2+D W-gamma^2 := by
  dsimp only [superpotential, algebraicFrequency, reggeWheeler, zerilli]
  generalize hp : lam*r+3 = p at hpolar ⊢
  have dp : D p = lam*(1-2/r) := by
    rw [← hp]
    simp only [map_add, D.leibniz, smul_eq_mul, three_constant, dl, dr, lapse, mul_zero, add_zero]
  simp only [lapse, map_add, map_sub, D.leibniz_div, D.leibniz, D.map_one_eq_zero,
    two_constant, three_constant, dl, dr, dp, smul_eq_mul, mul_zero, add_zero,
    zero_add, sub_zero]
  constructor <;> field_simp [hr, hpolar] <;> rw [← hp] <;> ring

def wave (c u : K) : K := D (D u)-c*u
def toOdd (W u : K) : K := W*u-D u

private theorem wave_add (c u v : K) : wave D c (u+v) = wave D c u+wave D c v := by
  simp only [wave, map_add, mul_add]
  ring

private theorem wave_sub (c u v : K) : wave D c (u-v) = wave D c u-wave D c v := by
  simp only [wave, map_sub, mul_sub]
  ring

private theorem wave_div_const (c u scale : K) (const : D scale = 0) :
    wave D c (u/scale) = wave D c u/scale := by
  simp only [wave, D.leibniz_div_const _ _ const, smul_eq_mul]
  rw [D.leibniz, D.leibniz_inv, const]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

private theorem wave_mul_const (c scale u : K) (const : D scale = 0) :
    wave D c (scale*u) = scale*wave D c u := by
  simp only [wave, D.leibniz, smul_eq_mul, const, mul_zero, add_zero]
  ring

theorem darbouX_source (c W u : K) (constant : D c = 0) :
    wave D (W^2-D W+c) (toOdd D W u) =
      toOdd D W (wave D (W^2+D W+c) u) := by
  simp only [wave, toOdd, pow_two, map_add, map_sub, D.leibniz, smul_eq_mul, constant, add_zero]
  ring

/-- The field and forcing use the same normalized daughter projection.
For the scattering convention, freq = 2k and phase = i. -/
theorem schwarzschild_projected_source [CharZero K] (r lam freq phase e o se so : K) (hr : r ≠ 0)
    (hpolar : lam*r+3 ≠ 0) (dr : D r = lapse r) (dl : D lam = 0)
    (df : D freq = 0) (dp : D phase = 0)
    (even : wave D (freq^2+zerilli r lam) e = se)
    (odd : wave D (freq^2+reggeWheeler r lam) o = so) :
    let W := superpotential r lam
    let scale := algebraicFrequency lam-freq
    wave D (freq^2+reggeWheeler r lam) (toOdd D W e/scale-phase*o) =
      toOdd D W se/scale-phase*so := by
  dsimp only
  have dg : D (algebraicFrequency lam) = 0 := by
    simp only [algebraicFrequency, D.leibniz_div_const _ _ (three_constant D),
      D.leibniz, map_add, D.map_one_eq_zero, dl, smul_eq_mul, add_zero, mul_zero]
  have scale_const : D (algebraicFrequency lam-freq) = 0 := by rw [map_sub, dg, df, sub_zero]
  rw [wave_sub, wave_div_const _ _ _ _ scale_const, wave_mul_const _ _ _ _ dp, odd]
  obtain ⟨hodd, heven⟩ := schwarzschild_potential_factorization D r lam hr hpolar dr dl
  have common : D (freq^2-(algebraicFrequency lam)^2) = 0 := by
    simp [pow_two, D.leibniz, df, dg]
  have left : freq^2+reggeWheeler r lam =
      (superpotential r lam)^2-D (superpotential r lam)+(freq^2-(algebraicFrequency lam)^2) := by
    rw [hodd]
    ring
  have right : freq^2+zerilli r lam =
      (superpotential r lam)^2+D (superpotential r lam)+(freq^2-(algebraicFrequency lam)^2) := by
    rw [heven]
    ring
  rw [left, darbouX_source _ _ _ _ common, ← right, even]

/-- A local shift of the projected field adds the same operator applied
to that shift to the forcing. The two equations have equivalent local
solvability whenever the admissible space is closed under this translation. -/
theorem local_source_shift (c x source shift : K) :
    wave D c x = source ↔ wave D c (x+shift) = source+wave D c shift := by
  rw [wave_add]
  exact ⟨fun h => congrArg (fun t => t+wave D c shift) h, add_right_cancel⟩

#print axioms harmonic_projection
#print axioms carrier_derivative
#print axioms stereographic_carrier
#print axioms schwarzschild_potential_factorization
#print axioms schwarzschild_projected_source
#print axioms local_source_shift

end SchwarzschildEinstein
