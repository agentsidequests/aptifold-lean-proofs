import Arithmetic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Nagura

open Nat

def runningLcm : Nat → Nat
  | 0 => 1
  | n + 1 => (runningLcm n).lcm (n + 1)

theorem runningLcmNe (n : Nat) : runningLcm n ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.lcm_ne_zero ih (Nat.succ_ne_zero n)

theorem runningLcmPos (n : Nat) : 0 < runningLcm n := Nat.pos_of_ne_zero (runningLcmNe n)

private theorem dividesLcm (n d : Nat) (pos : 1 ≤ d) (bound : d ≤ n) :
    d ∣ runningLcm n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : d = n + 1
    · rw [h, runningLcm]
      exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)

theorem runningLcmDvd (a b : Nat) (h : a ≤ b) : runningLcm a ∣ runningLcm b := by
  induction a with
  | zero => exact Nat.one_dvd _
  | succ a ih =>
    change (runningLcm a).lcm (a + 1) ∣ runningLcm b
    exact Nat.lcm_dvd (ih (by omega)) (dividesLcm b _ (by omega) h)

theorem runningLcmMono (a b : Nat) (h : a ≤ b) : runningLcm a ≤ runningLcm b :=
  Nat.le_of_dvd (runningLcmPos b) (runningLcmDvd a b h)

theorem lcmExponent (p n : Nat) (prime : p.Prime) :
    (runningLcm n).factorization p = p.log n := by
  apply Nat.le_antisymm
  · induction n with
    | zero => simp [runningLcm]
    | succ n ih =>
      rw [runningLcm, Nat.factorization_lcm (runningLcmNe n) (Nat.succ_ne_zero n), Finsupp.sup_apply]
      change max ((runningLcm n).factorization p) ((n + 1).factorization p) ≤ p.log (n + 1)
      refine max_le (ih.trans (Nat.log_mono_right (by omega))) ?_
      apply Nat.le_log_of_pow_le prime.one_lt
      exact Nat.le_of_dvd (Nat.succ_pos n) (Nat.ordProj_dvd _ _)
  · by_cases h : n = 0
    · simp [h, runningLcm]
    · apply (prime.pow_dvd_iff_le_factorization (runningLcmNe n)).1
      exact dividesLcm n _ (Nat.pow_pos prime.pos) (Nat.pow_log_le_self p h)

private theorem exponentMul (a b p : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  rw [Nat.factorization_mul ha hb, Finsupp.coe_add, Pi.add_apply]

-- This formulation of Legendre's factorial valuation adapts the induction in
-- Mathlib's Data.Nat.Choose.Factorization (Bolton Bailey, Patrick Stevens,
-- and Thomas Browning, Apache 2.0) to its elementary prerequisites.
private theorem factorialExponent (p : Nat) (prime : p.Prime) :
    ∀ (n b : Nat), p.log n < b → (n !).factorization p = ∑ i ∈ Finset.Ico 1 b, n / p ^ i
  | 0, b, _ => by simp
  | n + 1, b, hb => by
    rw [Nat.factorial_succ, exponentMul _ _ _ (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n),
      factorialExponent p prime n b ((Nat.log_mono_right (by omega)).trans_lt hb)]
    rw [Nat.factorization_eq_card_pow_dvd_of_lt prime (Nat.succ_pos n)
      (Nat.lt_pow_of_log_lt prime.one_lt hb)]
    calc
      ((Finset.Ico 1 b).filter fun i => p ^ i ∣ n + 1).card + ∑ i ∈ Finset.Ico 1 b, n / p ^ i =
          ∑ i ∈ Finset.Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) := by
        simp [Nat.add_comm, Finset.sum_add_distrib, Finset.sum_boole]
      _ = ∑ i ∈ Finset.Ico 1 b, (n + 1) / p ^ i :=
        Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

private theorem logSum (p n b : Nat) (prime : p.Prime) (hb : p.log n < b) :
    p.log n = ∑ i ∈ Finset.Ico 1 b, oneAbove n (p ^ i) := by
  let low := Finset.Ico 1 (p.log n + 1)
  have sub : low ⊆ Finset.Ico 1 b := by
    intro i hi
    simp [low] at hi
    exact Finset.mem_Ico.2 ⟨hi.1, by omega⟩
  have powers (i : Nat) (hi : 1 ≤ i) : p ^ i ≤ n ↔ i ≤ p.log n := by
    constructor
    · exact Nat.le_log_of_pow_le prime.one_lt
    · intro h
      by_cases hz : n = 0
      · simp [hz] at h
        omega
      · exact Nat.pow_le_of_le_log hz h
  have trim : (∑ i ∈ low, oneAbove n (p ^ i)) = ∑ i ∈ Finset.Ico 1 b, oneAbove n (p ^ i) := by
    apply Finset.sum_subset sub
    intro i hi miss
    have ih := (Finset.mem_Ico.1 hi).1
    have upper : ¬ i ≤ p.log n := by
      intro h
      exact miss (Finset.mem_Ico.2 ⟨ih, by omega⟩)
    simp [oneAbove, powers i ih, upper]
  rw [← trim]
  have terms : (∑ i ∈ low, oneAbove n (p ^ i)) = ∑ i ∈ low, (1 : Nat) := by
    apply Finset.sum_congr rfl
    intro i hi
    have h := Finset.mem_Ico.1 hi
    simp [oneAbove, powers i h.1, show i ≤ p.log n by omega]
  rw [terms]
  simp [low]

def factorialGroup (n : Nat) (ds : List Nat) : Nat :=
  (ds.map fun d => (n / d)!).prod

private def lcmGroup (n : Nat) (ds : List Nat) : Nat :=
  (ds.map fun d => runningLcm (n / d)).prod

private theorem factorialGroupNe (n : Nat) (ds : List Nat) : factorialGroup n ds ≠ 0 := by
  induction ds with
  | nil => simp [factorialGroup]
  | cons d ds ih => exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) ih

private theorem lcmGroupNe (n : Nat) (ds : List Nat) : lcmGroup n ds ≠ 0 := by
  induction ds with
  | nil => simp [lcmGroup]
  | cons d ds ih => exact Nat.mul_ne_zero (runningLcmNe _) ih

private theorem logDivLt (p n d : Nat) : p.log (n / d) < n + 1 :=
  (Nat.log_mono_right (Nat.div_le_self n d)).trans_lt (Nat.lt_add_one_of_le (Nat.log_le_self p n))

private theorem factorialGroupExponent (n p : Nat) (prime : p.Prime) (ds : List Nat) :
    (factorialGroup n ds).factorization p =
      ∑ i ∈ Finset.Ico 1 (n + 1), (ds.map fun d => (n / p ^ i) / d).sum := by
  induction ds with
  | nil => simp [factorialGroup]
  | cons d ds ih =>
    change (((n / d)! * factorialGroup n ds).factorization p) = _
    rw [exponentMul _ _ _ (Nat.factorial_ne_zero _) (factorialGroupNe n ds), ih,
      factorialExponent p prime (n / d) (n + 1) (logDivLt p n d),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [List.map_cons, List.sum_cons, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm d (p ^ i)]

private theorem lcmGroupExponent (n p : Nat) (prime : p.Prime) (ds : List Nat)
    (positive : ∀ d ∈ ds, 0 < d) :
    (lcmGroup n ds).factorization p =
      ∑ i ∈ Finset.Ico 1 (n + 1), (ds.map fun d => oneAbove (n / p ^ i) d).sum := by
  induction ds with
  | nil => simp [lcmGroup]
  | cons d ds ih =>
    change (runningLcm (n / d) * lcmGroup n ds).factorization p = _
    rw [exponentMul _ _ _ (runningLcmNe _) (lcmGroupNe n ds), lcmExponent p _ prime,
      ih (fun e he => positive e (List.mem_cons_of_mem d he)),
      logSum p (n / d) (n + 1) prime (logDivLt p n d), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hd := positive d (List.mem_cons_self)
    have hp := Nat.pow_pos (n := i) prime.pos
    have equal : p ^ i ≤ n / d ↔ d ≤ n / p ^ i := by
      rw [Nat.le_div_iff_mul_le hd, Nat.le_div_iff_mul_le hp, Nat.mul_comm d]
    simp only [List.map_cons, List.sum_cons, oneAbove, equal]

private def profile (n : Nat) (fs ls : List Nat) : Nat :=
  (fs.map fun d => n / d).sum + (ls.map fun d => oneAbove n d).sum

private theorem dividesOfProfile (fs ls gs rs : List Nat)
    (lpos : ∀ d ∈ ls, 0 < d) (rpos : ∀ d ∈ rs, 0 < d)
    (compare : ∀ t, profile t fs ls ≤ profile t gs rs) (n : Nat) :
    factorialGroup n fs * lcmGroup n ls ∣ factorialGroup n gs * lcmGroup n rs := by
  have posL := Nat.mul_ne_zero (factorialGroupNe n fs) (lcmGroupNe n ls)
  have posR := Nat.mul_ne_zero (factorialGroupNe n gs) (lcmGroupNe n rs)
  apply (Nat.factorization_prime_le_iff_dvd posL posR).1
  intro p prime
  rw [exponentMul _ _ _ (factorialGroupNe n fs) (lcmGroupNe n ls),
      exponentMul _ _ _ (factorialGroupNe n gs) (lcmGroupNe n rs),
      factorialGroupExponent n p prime fs, factorialGroupExponent n p prime gs,
      lcmGroupExponent n p prime ls lpos, lcmGroupExponent n p prime rs rpos,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => compare (n / p ^ i))

theorem lowerDivision (n : Nat) :
    factorialGroup n [2, 3, 5] ∣ factorialGroup n [1, 30] :=
  by
    simpa [lcmGroup] using
      dividesOfProfile [2, 3, 5] [] [1, 30] [] (by simp) (by simp)
        (fun t => by simpa [profile, Nat.add_assoc] using (lowerFloor t).1) n

theorem lowerLcmDivision (n : Nat) :
    factorialGroup n [1, 30] ∣ factorialGroup n [2, 3, 5] * runningLcm n :=
  by
    simpa [lcmGroup] using
      dividesOfProfile [1, 30] [] [2, 3, 5] [1] (by simp) (by simp)
        (fun t => by simpa [profile, Nat.add_assoc] using (lowerFloor t).2) n

theorem upperLcmDivision (n : Nat) :
    factorialGroup n [2, 3, 7, 43, 1806] * runningLcm n ∣
      (n !) * runningLcm (n / 1806) :=
  by
    simpa [lcmGroup, factorialGroup] using
      dividesOfProfile [2, 3, 7, 43, 1806] [1] [1] [1806] (by simp) (by simp)
        (fun t => by
          simpa [profile, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (upperFloor t)) n

theorem evenLcmDivision (n : Nat) :
    ((n / 2)! * (n / 2)!) * runningLcm n ∣ (n !) * runningLcm (n / 2) :=
  by
    simpa [lcmGroup, factorialGroup] using
      dividesOfProfile [2, 2] [1] [1] [2] (by simp) (by simp)
        (fun t => by
          simpa [profile, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (evenFloor t)) n

theorem primePowerCorrection (x y m : Nat) (h : y < (m + 1) * (m + 1))
    (none : ∀ p, p.Prime → x < p → p ≤ y → False) :
    runningLcm y ≤ runningLcm x * runningLcm m ^ 2 := by
  have pos := Nat.mul_pos (runningLcmPos x) (Nat.pow_pos (n := 2) (runningLcmPos m))
  apply Nat.le_of_dvd pos
  apply (Nat.factorization_prime_le_iff_dvd (runningLcmNe y) (Nat.ne_of_gt pos)).1
  intro p prime
  rw [exponentMul _ _ _ (runningLcmNe x) (Nat.ne_of_gt (Nat.pow_pos (runningLcmPos m))),
      lcmExponent p y prime, lcmExponent p x prime, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.nsmul_eq_mul, lcmExponent p m prime]
  let e := p.log y
  change e ≤ p.log x + 2 * p.log m
  by_cases hz : e = 0
  · omega
  · have hy : y ≠ 0 := by
      intro hy
      exact hz (by simp [e, hy])
    have pe : p ^ e ≤ y := Nat.pow_log_le_self p hy
    have py : p ≤ y := calc
      p = p ^ 1 := (Nat.pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right prime.pos (by omega)
      _ ≤ y := pe
    have px : p ≤ x := by
      by_contra hpx
      exact none p prime (by omega) py
    have ex : 1 ≤ p.log x := Nat.le_log_of_pow_le prime.one_lt (by simpa using px)
    have pm : p ^ (e / 2) ≤ m := by
      by_contra hl
      have q : m + 1 ≤ p ^ (e / 2) := by omega
      have hy' : (m + 1) * (m + 1) ≤ y := calc
        (m + 1) * (m + 1) ≤ p ^ (e / 2) * p ^ (e / 2) := Nat.mul_le_mul q q
        _ = p ^ (e / 2 + e / 2) := (Nat.pow_add _ _ _).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right prime.pos (by omega)
        _ ≤ y := pe
      omega
    have em : e / 2 ≤ p.log m := Nat.le_log_of_pow_le prime.one_lt pm
    omega

end Nagura
