import ArchivedOddFraction
import AdmittedMixtureField

/-! Restore the published pure-odd source by adding the two local operator
images to the pole-subtracted matrix input. -/
namespace SchwarzschildMixtures

open Polynomial SchwarzschildLaurent ArchivedOddData NumeratorData

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ

def oddMultiplier (m : ℕ) : ℕ := m * SchwarzschildMatrix.sourceScale.toNat

def oddShift (m : ℕ) (p : Row Expr) (k ell : ℂ) : Row ℂᵣ :=
  localField p (oddMultiplier m) false k ell

def oddForcing (m : ℕ) (s : Row Expr) (k ell : ℂ) : Row ℂᵣ :=
  projectedSource s (oddMultiplier m) false k ell

private theorem value_power (k ell : ℂ) (p : Expr) (n : ℕ) :
    Expr.value k ell (ArchivedOddData.power p n) = (Expr.value k ell p)^n := by
  induction n with
  | zero => simp [ArchivedOddData.power, c, Expr.value_constant]
  | succ n ih => simp [ArchivedOddData.power, ih, pow_succ]

private def paddingScalar (m : ℕ) (k ell : ℂ) : ℂ :=
  (m:ℂ)*ell*(ell-1)^2*(ell+2)^2*(ell+1)^4*(2*ell-1)^4*k^2*(12*(k+gamma ell))^2

private theorem padding_value (m : ℕ) (k ell : ℂ) :
    Expr.value k ell (padding m) =
      C (paddingScalar m k ell) *
        X^9 * shiftedRadius * (parentPole ell)^7 * (daughterPole ell)^3 := by
  have freq : 12*(k+gamma ell) = 12*k+(ell-1)*ell*(ell+1)*(ell+2) := by
    unfold gamma
    ring
  simp [padding, paddingScalar, value_power, parentFrequency, c, x, xh, w, l, u, Expr.value_single,
    Expr.value_constant, sparseParentPole, sparseDaughterPole, parentPole, daughterPole,
    shiftedRadius, freq, map_mul, map_pow, map_add, map_sub, map_ofNat]

theorem matrix_clearance_value (k ell : ℂ) :
    SchwarzschildMatrix.sourceClearance k ell =
      (SchwarzschildMatrix.sourceScale : ℂ)*6*((2*ell+1)*(2*ell-1)*(ell+1))*(k-daughterGamma ell) := by
  have hg : SchwarzschildMatrix.gamma ell = daughterGamma ell := by
    unfold SchwarzschildMatrix.gamma daughterGamma gamma
    ring
  rw [← hg]
  rfl

private theorem padding_clearance (m : ℕ) (k ell : ℂ) :
    paddingScalar m k ell * SchwarzschildMatrix.sourceClearance k ell =
      fieldScalar (oddMultiplier m) false k ell := by
  have hcast : (SchwarzschildMatrix.sourceScale.toNat : ℂ) = (SchwarzschildMatrix.sourceScale : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg (show (0:ℤ) ≤ SchwarzschildMatrix.sourceScale by decide +kernel)
  rw [matrix_clearance_value]
  simp only [paddingScalar, fieldScalar, oddMultiplier, Nat.cast_mul, hcast,
    Bool.false_eq_true, if_false, mul_one]
  rw [pow_succ (ell+1) 4, pow_succ (2*ell-1) 4]
  ac_rfl

theorem padded_denominator (m : ℕ) (k ell : ℂ) :
    Expr.value k ell (padding m) * matrixDenominator k ell =
      denominatorStep (poles ell) *
        (denominatorStep (poles ell) * fieldDenominator (fieldScalar (oddMultiplier m) false k ell) ell) := by
  -- Compare the powers of the radius and poles without expanding the poles.
  have collect_powers (a b x h p q : ℂ[X]) :
      a*x^9*h*p^7*q^3*(b*x^6) =
        (x^2*(p*q))*(x^2*(p*q)*((a*b)*x^11*h*p^5*q)) := by ring
  rw [padding_value, matrixDenominator, collect_powers, ← map_mul, padding_clearance]
  rfl

private theorem restored_value (m : ℕ) (k ell : ℂ) (p : Row Expr) :
    rowValue k ell (restoredNumerators m p) =
      plus (rowValue k ell (sourceData p))
        (scale (Expr.value k ell (padding m)) (rowValue k ell tableNumerators)) := by
  simp [restoredNumerators, rowValue, scaleData, mapRow, exprRowMap, plus, scale]

private theorem compare_rows (k ell : ℂ) (p s : Row Expr)
    (ha : Expr.Check p.1 s.1) (hb : Expr.Check p.2.1 s.2.1) (hc : Expr.Check p.2.2 s.2.2) :
    rowValue k ell p = rowValue k ell s :=
  Prod.ext (Expr.value_eq_of_check _ _ ha k ell) (Prod.ext
    (Expr.value_eq_of_check _ _ hb k ell) (Expr.value_eq_of_check _ _ hc k ell))

set_option maxRecDepth 2400 in
/-- This relates two independently sourced inputs to the exclusion proof.
The forcing comes from the published kernel, and the local shift uses the
published regulator plus the referee packet's removed poles. -/
theorem odd_forcing_restored (m n : ℕ) (hm : 0 < m) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (p s : Row Expr)
    (ca : Expr.Check (restoredNumerators m p).1 s.1)
    (cb : Expr.Check (restoredNumerators m p).2.1 s.2.1)
    (cc : Expr.Check (restoredNumerators m p).2.2 s.2.2) :
    oddForcing m s k n =
      plus (rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (oddShift m p k n))
        (archivedSource k n) := by
  let ell : ℂ := n
  let scalar := fieldScalar (oddMultiplier m) false k ell
  let q := fieldDenominator scalar ell
  let b := poles ell
  let d := denominatorStep b * (denominatorStep b * q)
  let pad := Expr.value k ell (padding m)
  have hc : 0 < SchwarzschildMatrix.sourceScale.toNat := by decide +kernel
  have hq : q ≠ 0 :=
    fieldDenominator_ne_zero _ (fieldScalar_ne_zero _ n (Nat.mul_pos hm hc) hn false k hk ki) n hn
  have hb : b ≠ 0 := poles_ne_zero n hn
  have hs : denominatorStep b ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hb
  have hd : d ≠ 0 := mul_ne_zero hs (mul_ne_zero hs hq)
  have padded : pad * matrixDenominator k ell = d := padded_denominator m k ell
  have hproduct : pad * matrixDenominator k ell ≠ 0 := by rw [padded]; exact hd
  have hpad := (mul_ne_zero_iff.mp hproduct).1
  have compared := compare_rows k ell (restoredNumerators m p) s ca cb cc
  have restored := restored_value m k ell p
  have applied :
      rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k (oddShift m p k ell) =
        fractionRow (rowValue k ell (sourceData p)) d :=
    source_of_checked_numerators k ell scalar p (sourceData p) hq hb rfl
  change fractionRow (rowValue k ell s) d = _
  rw [← compared, restored, fractionRow_plus, ← applied]
  have paddedFraction :
      fractionRow (scale pad (rowValue k ell tableNumerators)) d = archivedSource k ell := by
    rw [← padded, fractionRow_cancel _ hpad, archived_source_as_fraction k ell]
  rw [paddedFraction]

#print axioms odd_forcing_restored

end
end SchwarzschildMixtures
