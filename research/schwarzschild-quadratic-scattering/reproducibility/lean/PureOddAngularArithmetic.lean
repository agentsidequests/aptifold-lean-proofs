import PureOddAngularData
import PureOddFullAngleCoordinates

/-! Sparse exact arithmetic for the angular calculation. Denominators
are products of powers of r, r - 2, and 1 - c². Checking a zero
numerator is sufficient, with no assumption of a unique normal form. -/
namespace SchwarzschildEinstein.PureOdd.AngularArithmetic

private def powersValue {K : Type*} [CommMonoid K] (x : ℕ → K) (i : ℕ) : Powers → K
  | [] => 1
  | a::p => x i ^ a * powersValue x (i+1) p

private theorem powersValue_add {K : Type*} [CommMonoid K] (x : ℕ → K)
    (i : ℕ) (p q : Powers) :
    powersValue x i (addPowers p q) = powersValue x i p * powersValue x i q := by
  induction p generalizing i q with
  | nil => simp [addPowers, powersValue]
  | cons a p ih =>
    cases q with
    | nil => simp [addPowers, powersValue]
    | cons b q =>
      simp only [addPowers, powersValue, pow_add, ih]
      ac_rfl

variable {K : Type*} [Field K] [CharZero K]

def Polynomial.eval (x : ℕ → K) : Polynomial → K
  | [] => 0
  | (w,a)::ps => (a : K)*powersValue x 0 w + eval x ps

private theorem Polynomial.eval_insert (x : ℕ → K) (w : Powers) (a : ℚ) (p : Polynomial) :
    eval x (insert w a p) = (a : K)*powersValue x 0 w + eval x p := by
  induction p with
  | nil =>
    by_cases h : a = 0 <;> simp [insert, h, eval]
  | cons t ps ih =>
    obtain ⟨v,b⟩ := t
    by_cases same : w = v
    · subst w
      by_cases cancel : a+b = 0
      · have eq : (a : K) + (b : K) = 0 := by exact_mod_cast cancel
        rw [insert, if_pos rfl, if_pos cancel, eval, ← add_assoc, ← add_mul, eq, zero_mul, zero_add]
      · rw [insert, if_pos rfl, if_neg cancel]
        simp only [eval, Rat.cast_add, add_mul, add_assoc]
    · rw [insert, if_neg same, eval, ih, eval]
      ac_rfl

private theorem Polynomial.eval_append (x : ℕ → K) (p q : Polynomial) :
    eval x (p++q) = eval x p + eval x q := by
  induction p with
  | nil => simp [eval]
  | cons t p ih =>
    obtain ⟨w,a⟩ := t
    simp [eval, ih, add_assoc]

private theorem Polynomial.eval_merge (x : ℕ → K) (n : ℕ) (p q : Polynomial) :
    eval x (merge n p q) = eval x p + eval x q := by
  induction n generalizing p q with
  | zero => exact eval_append x p q
  | succ n ih =>
    rcases p with _ | ⟨⟨u,a⟩,p⟩ <;> rcases q with _ | ⟨⟨v,b⟩,q⟩
    · simp [merge, eval]
    · simp [merge, eval]
    · simp [merge, eval]
    · rw [merge]
      split_ifs with h cancel order
      · subst v
        rw [ih]
        simp only [eval]
        have eq : (a : K) + (b : K) = 0 := by exact_mod_cast cancel
        calc
          eval x p+eval x q =
              ((a:K)+(b:K))*powersValue x 0 u + (eval x p+eval x q) := by simp [eq]
          _ = _ := by ring
      · subst v
        simp only [eval, Rat.cast_add, ih]
        ring
      · simp only [eval, ih]
        ring
      · simp only [eval, ih]
        ring

@[simp] theorem Polynomial.eval_add (x : ℕ → K) (p q : Polynomial) :
    eval x (p.add q) = eval x p + eval x q :=
  eval_merge x _ p q

@[simp] theorem Polynomial.eval_neg (x : ℕ → K) (p : Polynomial) :
    eval x p.neg = -eval x p := by
  induction p with
  | nil => simp [neg, eval]
  | cons t p ih =>
    obtain ⟨w,a⟩ := t
    change eval x ((w,-a)::neg p) = _
    simp only [eval, Rat.cast_neg, ih]
    ring

private theorem Polynomial.eval_shift (x : ℕ → K) (w : Powers) (a : ℚ) (p : Polynomial) :
    eval x (p.shift w a) = (a : K)*powersValue x 0 w*eval x p := by
  induction p with
  | nil => simp [shift, eval]
  | cons t p ih =>
    obtain ⟨v,b⟩ := t
    change eval x ((addPowers w v,a*b)::shift w a p) = _
    simp only [eval, powersValue_add, Rat.cast_mul, ih]
    ring

private theorem Polynomial.eval_convolve (x : ℕ → K) (p q : Polynomial) :
    eval x (p.convolve q) = eval x p * eval x q := by
  induction p with
  | nil => simp [convolve, eval]
  | cons t p ih =>
    obtain ⟨w,a⟩ := t
    change eval x ((shift w a q).add (convolve p q)) = _
    rw [eval_add, eval_shift, ih, eval, add_mul]

@[simp] theorem Polynomial.eval_mul (x : ℕ → K) (p q : Polynomial) :
    eval x (p.mul q) = eval x p * eval x q := by
  rcases p with _ | ⟨⟨w,a⟩, _ | ⟨u,p⟩⟩ <;>
    rcases q with _ | ⟨⟨v,b⟩, _ | ⟨t,q⟩⟩ <;>
    simp [mul, eval_convolve, eval_shift, eval, mul_comm]

@[simp] theorem Polynomial.eval_constant (x : ℕ → K) (a : ℚ) :
    eval x (constant a) = (a : K) := by
  simp [constant, eval_insert, powersValue, eval]

omit [CharZero K] in
private theorem powersValue_variable (x : ℕ → K) (start i : ℕ) :
    powersValue x start (variablePowers i) = x (start+i) := by
  induction i generalizing start with
  | zero => simp [variablePowers, powersValue]
  | succ i ih =>
    simp only [variablePowers, powersValue, pow_zero, one_mul, ih]
    congr 1
    omega

@[simp] theorem Polynomial.eval_indeterminate (x : ℕ → K) (i : ℕ) :
    eval x (indeterminate i) = x i := by
  simp [indeterminate, eval, powersValue_variable]

@[simp] theorem Polynomial.eval_power (x : ℕ → K) (p : Polynomial) (n : ℕ) :
    eval x (p.power n) = (eval x p)^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

private theorem Denominator.extra_join (d e : Denominator) : (d.extra (d.join e)).add d = d.join e := by
  cases d
  cases e
  simp [extra, add, join, Nat.sub_add_cancel (Nat.le_max_left ..)]

private theorem Denominator.join_comm (d e : Denominator) : d.join e = e.join d := by
  cases d
  cases e
  simp [join, max_comm]

def Denominator.eval (x : ℕ → K) (d : Denominator) : K :=
  (x 0)^d.radius * (x 0-2)^d.horizon * (sineSquared (x 1))^d.angular

omit [CharZero K] in
private theorem Denominator.eval_add (x : ℕ → K) (d e : Denominator) :
    (d.add e).eval x = d.eval x * e.eval x := by
  simp only [add, eval, pow_add]
  ac_rfl

omit [CharZero K] in
private theorem Denominator.eval_ne (x : ℕ → K) (d : Denominator)
    (hr : x 0 ≠ 0) (hh : x 0-2 ≠ 0) (hs : sineSquared (x 1) ≠ 0) : d.eval x ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hh)) (pow_ne_zero _ hs)

@[simp] private theorem Denominator.eval_poly (x : ℕ → K) (d : Denominator) :
    d.poly.eval x = d.eval x := by
  simp [poly, eval, sineSquared, pow_two, sub_eq_add_neg]

@[simp] private theorem Denominator.eval_scale (x : ℕ → K) (d : Denominator) (p : Polynomial) :
    (d.scale p).eval x = p.eval x*d.eval x := by
  unfold scale
  split_ifs with h
  · simp [eval, h.1, h.2.1, h.2.2]
  · simp

def Fraction.eval (x : ℕ → K) (a : Fraction) : K := a.num.eval x / a.den.eval x

@[simp] theorem Fraction.eval_constant (x : ℕ → K) (a : ℚ) :
    (constant a).eval x = (a : K) := by
  simp [constant, eval, Denominator.eval]

@[simp] theorem Fraction.eval_indeterminate (x : ℕ → K) (i : ℕ) :
    (indeterminate i).eval x = x i := by
  simp [indeterminate, eval, Denominator.eval]

@[simp] theorem Fraction.eval_inverse (x : ℕ → K) (d : Denominator) :
    (inverse d).eval x = 1/d.eval x := by simp [inverse, eval]

@[simp] theorem Fraction.eval_zero (x : ℕ → K) : (0 : Fraction).eval x = 0 := by
  change (constant 0).eval x = 0
  simp

@[simp] theorem Fraction.eval_neg (x : ℕ → K) (a : Fraction) :
    (-a).eval x = -a.eval x := by
  change a.num.neg.eval x / a.den.eval x = _
  rw [Polynomial.eval_neg, neg_div]
  rfl

@[simp] theorem Fraction.eval_mul (x : ℕ → K) (a b : Fraction) :
    (a*b).eval x = a.eval x * b.eval x := by
  change (if a.num = [] then a else if b.num = [] then b else
    ⟨a.num.mul b.num, a.den.add b.den⟩ : Fraction).eval x = _
  split_ifs with ha hb
  · simp [eval, ha, Polynomial.eval]
  · simp [eval, hb, Polynomial.eval]
  · simp only [eval, Polynomial.eval_mul, Denominator.eval_add, div_mul_div_comm]

@[simp] theorem Fraction.eval_add (x : ℕ → K) (hr : x 0 ≠ 0) (hh : x 0-2 ≠ 0)
    (hs : sineSquared (x 1) ≠ 0) (a b : Fraction) :
    (a+b).eval x = a.eval x + b.eval x := by
  change (if a.num = [] then b else if b.num = [] then a else a.addNonempty b).eval x = _
  split_ifs with ha hb
  · simp [eval, ha, Polynomial.eval]
  · simp [eval, hb, Polynomial.eval]
  change (((a.den.extra (a.den.join b.den)).scale a.num).add
    ((b.den.extra (a.den.join b.den)).scale b.num)).eval x / (a.den.join b.den).eval x = _
  simp only [Polynomial.eval_add, Denominator.eval_scale, add_div]
  have left := congrArg (Denominator.eval x) (a.den.extra_join b.den)
  have right := congrArg (Denominator.eval x) (b.den.extra_join a.den)
  rw [← Denominator.join_comm a.den b.den] at right
  simp only [Denominator.eval_add] at left right
  congr 1
  · rw [← left, mul_comm ((a.den.extra _).eval x) (a.den.eval x),
      mul_div_mul_right _ _ (Denominator.eval_ne x _ hr hh hs)]
    rfl
  · rw [← right, mul_comm ((b.den.extra _).eval x) (b.den.eval x),
      mul_div_mul_right _ _ (Denominator.eval_ne x _ hr hh hs)]
    rfl

theorem Fraction.eq_of_zero_numerator (x : ℕ → K) (hr : x 0 ≠ 0) (hh : x 0-2 ≠ 0)
    (hs : sineSquared (x 1) ≠ 0) (a b : Fraction) (h : (a + -b).num = []) :
    a.eval x = b.eval x := by
  have eq : (a + -b).eval x = 0 := by simp [eval, h, Polynomial.eval]
  apply sub_eq_zero.mp
  simpa [Fraction.eval_add x hr hh hs, ← sub_eq_add_neg] using eq

end SchwarzschildEinstein.PureOdd.AngularArithmetic
