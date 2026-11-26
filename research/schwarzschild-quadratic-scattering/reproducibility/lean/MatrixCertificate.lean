import Init
import MatrixCertificateData
import AngularObstructionPilot

namespace SchwarzschildMatrix

/-- One term in a Laurent polynomial in radius, with coefficients in Z[k, ell]. -/
structure LaurentTerm where
  radius : Int
  frequency : Nat
  angular : Nat
  coefficient : Int

abbrev Laurent := List LaurentTerm
abbrev LaurentRow := Laurent × Laurent × Laurent

def multiplyLaurent (p q : Laurent) : Laurent :=
  p.flatMap fun a => q.map fun b =>
    ⟨a.radius + b.radius, a.frequency + b.frequency,
      a.angular + b.angular, a.coefficient * b.coefficient⟩

def scaleLaurent (n : Int) (p : Laurent) : Laurent :=
  p.map fun t => { t with coefficient := n * t.coefficient }

def shiftRadius (power : Int) (p : Laurent) : Laurent :=
  p.map fun t => { t with radius := t.radius + power }

def f : Laurent := [⟨0, 0, 0, 1⟩, ⟨-1, 0, 0, -2⟩]

/-- Regge–Wheeler potential f * ((scale ell)(scale ell + 1)/r² - 6/r³). -/
def potential (scale : Int) : Laurent :=
  multiplyLaurent f [⟨-2, 0, 2, scale * scale⟩, ⟨-2, 0, 1, scale⟩, ⟨-3, 0, 0, -6⟩]

def radialDerivative (p : Laurent) : Laurent :=
  multiplyLaurent f (p.filterMap fun t =>
    if t.radius == 0 then none else
      some { t with radius := t.radius - 1, coefficient := t.radius * t.coefficient })

def a : Laurent := [⟨2, 2, 0, 1⟩] ++ shiftRadius 2 (potential 1)
def b : Laurent := scaleLaurent 2 (shiftRadius (-1) f)
def c : Laurent := [⟨-2, 0, 0, 1⟩]

/-- D + right multiplication by the manuscript's parent-basis matrix. -/
def derivative (row : LaurentRow) : LaurentRow :=
  let (p, q, s) := row
  (radialDerivative p ++ multiplyLaurent a q,
   radialDerivative q ++ scaleLaurent 2 (multiplyLaurent c p) ++ multiplyLaurent b q ++
      scaleLaurent 2 (multiplyLaurent a s),
   radialDerivative s ++ multiplyLaurent c q ++ scaleLaurent 2 (multiplyLaurent b s))

def operator (row : LaurentRow) : LaurentRow :=
  let daughter : Laurent := [⟨0, 2, 0, 4⟩] ++ potential 2
  let (p, q, s) := row
  let (dp, dq, ds) := derivative (derivative row)
  (dp ++ scaleLaurent (-1) (multiplyLaurent daughter p),
   dq ++ scaleLaurent (-1) (multiplyLaurent daughter q),
   ds ++ scaleLaurent (-1) (multiplyLaurent daughter s))

def columnLabels : List (Nat × Int) :=
  (List.range 12).map (fun (i : Nat) => (0, (i : Int) - 7)) ++
  (List.range 10).map (fun (i : Nat) => (1, (i : Int) - 7)) ++
  (List.range 8).map (fun (i : Nat) => (2, (i : Int) - 7))

def insertMonomial (t : Monomial) : List Monomial → List Monomial
  | [] => [t]
  | u :: rest =>
    if t.1 == u.1 && t.2.1 == u.2.1 then
      (t.1, t.2.1, t.2.2 + u.2.2) :: rest
    else u :: insertMonomial t rest

def coefficient (row : LaurentRow) (label : Nat × Int) : List Monomial :=
  let terms := match label.1 with
    | 0 => row.1
    | 1 => row.2.1
    | _ => row.2.2
  let collected := terms.foldr (fun t acc =>
    if t.radius == label.2 then insertMonomial (t.frequency, t.angular, t.coefficient) acc else acc) []
  collected.filter fun t => t.2.2 != 0

/-- One column, rebuilt from its radial monomial and the exact Laurent operator. -/
def matrixColumn (label : Nat × Int) : List (List Monomial) :=
  let term : Laurent := [⟨label.2, 0, 0, 1⟩]
  let basis : LaurentRow := match label.1 with
    | 0 => (term, [], [])
    | 1 => ([], term, [])
    | _ => ([], [], term)
  let image := operator basis
  rowLabels.map (coefficient image)

def rows : List Nat := List.range 41

def weightAt (i : Nat) : Polynomial := (witness[i]?).getD []
def termsAt (column : List (List Monomial)) (i : Nat) : List Monomial := (column[i]?).getD []

private def addAngular : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => (x + y) :: addAngular p q

private def add : Polynomial → Polynomial → Polynomial
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => addAngular x y :: add p q

private def shiftAngularScale (n : Nat) (s : Int) (row : List Int) : List Int :=
  if row.isEmpty then [] else List.replicate n 0 ++ row.map (s * ·)

private def multiplyMonomial (p : Polynomial) (t : Monomial) : Polynomial :=
  List.replicate t.1 [] ++ p.map (shiftAngularScale t.2.1 t.2.2)

private def multiply (p : Polynomial) (q : List Monomial) : Polynomial :=
  q.foldr (fun t acc => add (multiplyMonomial p t) acc) []

private def scale (n : Int) (p : Polynomial) : Polynomial :=
  p.map (List.map (n * ·))

private def isZero (p : Polynomial) : Bool :=
  p.all fun row => row.all (· == 0)

/-- Projection by the archived witness with its common denominator cleared. -/
def project (column : List (List Monomial)) : Polynomial :=
  rows.foldr (fun i acc => add (multiply (weightAt i) (termsAt column i)) acc) []

def coordinateProjectionMatches (items : List Nat) (weight : Nat → Polynomial)
    (column : Nat × Int) (target : Polynomial) : Bool :=
  isZero (add (items.foldr
    (fun i acc => add (multiply (weight i) (termsAt (matrixColumn column) i)) acc) [])
    (scale (-1) target))

private def q : List Monomial := [(0, 0, -1), (0, 1, -1), (0, 2, 4), (0, 3, 4)]
private def angularPolynomial : Polynomial := [angularCoefficients]
private def target : Polynomial := multiply angularPolynomial (q.map fun t => (6, t.2))
private def sourceResidual : Polynomial :=
  add (scale angularScale (project clearedSource)) (scale (-(6 * witnessScale * sourceScale)) target)

set_option maxRecDepth 12000
set_option maxHeartbeats 10000000

/- The reductions are independent so the kernel can release each checked column
and each checked frequency coefficient before proceeding to the next. -/

private theorem matrixShape :
    rowLabels.length = 41 ∧ columnLabels.length = 30 ∧
      (columnLabels.flatMap matrixColumn).countP (! ·.isEmpty) = 326 ∧
      ((columnLabels.flatMap matrixColumn).flatMap id).length = 588 := by
  decide +kernel

theorem column_order : columnLabels = [
  (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
  (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2),
  (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0)] := by
  decide +kernel

private theorem column0 : isZero (project (matrixColumn (0, -7))) = true := by
  decide +kernel

private theorem column1 : isZero (project (matrixColumn (0, -6))) = true := by
  decide +kernel

private theorem column2 : isZero (project (matrixColumn (0, -5))) = true := by
  decide +kernel

private theorem column3 : isZero (project (matrixColumn (0, -4))) = true := by
  decide +kernel

private theorem column4 : isZero (project (matrixColumn (0, -3))) = true := by
  decide +kernel

private theorem column5 : isZero (project (matrixColumn (0, -2))) = true := by
  decide +kernel

private theorem column6 : isZero (project (matrixColumn (0, -1))) = true := by
  decide +kernel

private theorem column7 : isZero (project (matrixColumn (0, 0))) = true := by
  decide +kernel

private theorem column8 : isZero (project (matrixColumn (0, 1))) = true := by
  decide +kernel

private theorem column9 : isZero (project (matrixColumn (0, 2))) = true := by
  decide +kernel

private theorem column10 : isZero (project (matrixColumn (0, 3))) = true := by
  decide +kernel

private theorem column11 : isZero (project (matrixColumn (0, 4))) = true := by
  decide +kernel

private theorem column12 : isZero (project (matrixColumn (1, -7))) = true := by
  decide +kernel

private theorem column13 : isZero (project (matrixColumn (1, -6))) = true := by
  decide +kernel

private theorem column14 : isZero (project (matrixColumn (1, -5))) = true := by
  decide +kernel

private theorem column15 : isZero (project (matrixColumn (1, -4))) = true := by
  decide +kernel

private theorem column16 : isZero (project (matrixColumn (1, -3))) = true := by
  decide +kernel

private theorem column17 : isZero (project (matrixColumn (1, -2))) = true := by
  decide +kernel

private theorem column18 : isZero (project (matrixColumn (1, -1))) = true := by
  decide +kernel

private theorem column19 : isZero (project (matrixColumn (1, 0))) = true := by
  decide +kernel

private theorem column20 : isZero (project (matrixColumn (1, 1))) = true := by
  decide +kernel

private theorem column21 : isZero (project (matrixColumn (1, 2))) = true := by
  decide +kernel

private theorem column22 : isZero (project (matrixColumn (2, -7))) = true := by
  decide +kernel

private theorem column23 : isZero (project (matrixColumn (2, -6))) = true := by
  decide +kernel

private theorem column24 : isZero (project (matrixColumn (2, -5))) = true := by
  decide +kernel

private theorem column25 : isZero (project (matrixColumn (2, -4))) = true := by
  decide +kernel

private theorem column26 : isZero (project (matrixColumn (2, -3))) = true := by
  decide +kernel

private theorem column27 : isZero (project (matrixColumn (2, -2))) = true := by
  decide +kernel

private theorem column28 : isZero (project (matrixColumn (2, -1))) = true := by
  decide +kernel

private theorem column29 : isZero (project (matrixColumn (2, 0))) = true := by
  decide +kernel

private theorem columnIdentities :
    columnLabels.all (fun column => isZero (project (matrixColumn column))) = true := by
  rw [column_order]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    column0, column1, column2, column3, column4, column5, column6, column7,
    column8, column9, column10, column11, column12, column13, column14, column15,
    column16, column17, column18, column19, column20, column21, column22, column23,
    column24, column25, column26, column27, column28, column29]

private def slotZero (p : Polynomial) (i : Nat) : Bool :=
  ((p[i]?).getD []).all (· == 0)

private theorem isZero_of_slots (p : Polynomial) (kCount : Nat) (hsize : p.length ≤ kCount)
    (hslots : (List.range kCount).all (slotZero p) = true) : isZero p = true := by
  apply List.all_eq_true.mpr
  intro row hm
  rcases List.mem_iff_getElem.mp hm with ⟨i, hi, heq⟩
  have hr : i ∈ List.range kCount := List.mem_range.mpr (Nat.lt_of_lt_of_le hi hsize)
  have h := List.all_eq_true.mp hslots i hr
  simpa only [slotZero, List.getElem?_eq_getElem hi, Option.getD_some, heq] using h

private theorem source_degree_bound : sourceResidual.length ≤ 19 := by
  decide +kernel

private theorem sourceSlot0 : slotZero sourceResidual 0 = true := by
  decide +kernel

private theorem sourceSlot1 : slotZero sourceResidual 1 = true := by
  decide +kernel

private theorem sourceSlot2 : slotZero sourceResidual 2 = true := by
  decide +kernel

private theorem sourceSlot3 : slotZero sourceResidual 3 = true := by
  decide +kernel

private theorem sourceSlot4 : slotZero sourceResidual 4 = true := by
  decide +kernel

private theorem sourceSlot5 : slotZero sourceResidual 5 = true := by
  decide +kernel

private theorem sourceSlot6 : slotZero sourceResidual 6 = true := by
  decide +kernel

private theorem sourceSlot7 : slotZero sourceResidual 7 = true := by
  decide +kernel

private theorem sourceSlot8 : slotZero sourceResidual 8 = true := by
  decide +kernel

private theorem sourceSlot9 : slotZero sourceResidual 9 = true := by
  decide +kernel

private theorem sourceSlot10 : slotZero sourceResidual 10 = true := by
  decide +kernel

private theorem sourceSlot11 : slotZero sourceResidual 11 = true := by
  decide +kernel

private theorem sourceSlot12 : slotZero sourceResidual 12 = true := by
  decide +kernel

private theorem sourceSlot13 : slotZero sourceResidual 13 = true := by
  decide +kernel

private theorem sourceSlot14 : slotZero sourceResidual 14 = true := by
  decide +kernel

private theorem sourceSlot15 : slotZero sourceResidual 15 = true := by
  decide +kernel

private theorem sourceSlot16 : slotZero sourceResidual 16 = true := by
  decide +kernel

private theorem sourceSlot17 : slotZero sourceResidual 17 = true := by
  decide +kernel

private theorem sourceSlot18 : slotZero sourceResidual 18 = true := by
  decide +kernel

private theorem sourceIdentity : isZero sourceResidual = true := by
  apply isZero_of_slots sourceResidual 19 source_degree_bound
  rw [show List.range 19 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from (by decide +kernel)]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    sourceSlot0, sourceSlot1, sourceSlot2, sourceSlot3, sourceSlot4, sourceSlot5, sourceSlot6, sourceSlot7,
    sourceSlot8, sourceSlot9, sourceSlot10, sourceSlot11, sourceSlot12, sourceSlot13, sourceSlot14, sourceSlot15,
    sourceSlot16, sourceSlot17, sourceSlot18]

open Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

section Evaluation

variable {K : Type u} [CommRing K]

/-- Evaluate an angular coefficient row with Horner's rule. -/
def evalAngular (x : K) : List Int → K
  | [] => 0
  | a :: p => (a : K) + x * evalAngular x p

/-- Evaluate the polynomial, with the outer list indexed by frequency power. -/
def evalPoly (k x : K) : Polynomial → K
  | [] => 0
  | a :: p => evalAngular x a + k * evalPoly k x p

def evalMonomial (k x : K) (t : Monomial) : K :=
  (t.2.2 : K) * k ^ t.1 * x ^ t.2.1

def total {ι : Type v} (items : List ι) (f : ι → K) : K :=
  items.foldr (fun i acc => f i + acc) 0

private theorem total_congr {ι : Type v} (items : List ι) (f g : ι → K)
    (h : ∀ i ∈ items, f i = g i) : total items f = total items g := by
  induction items with
  | nil => rfl
  | cons i items ih =>
    simp only [total, List.foldr_cons]
    rw [h i (List.mem_cons_self), ← total, ← total]
    rw [ih fun j hm => h j (List.mem_cons_of_mem _ hm)]

private theorem total_zero {ι : Type v} (items : List ι) :
    total items (fun _ => (0 : K)) = 0 := by
  induction items with
  | nil => rfl
  | cons i items ih =>
    change 0 + total items (fun _ => 0) = 0
    rw [ih, Semiring.add_zero]

private theorem total_add {ι : Type v} (items : List ι) (f g : ι → K) :
    total items (fun i => f i + g i) = total items f + total items g := by
  induction items with
  | nil => exact (Semiring.add_zero (0 : K)).symm
  | cons i items ih =>
    change f i + g i + total items (fun j => f j + g j) =
      (f i + total items f) + (g i + total items g)
    rw [ih]
    grind

private theorem total_mul_left {ι : Type v} (items : List ι) (a : K) (f : ι → K) :
    total items (fun i => a * f i) = a * total items f := by
  induction items with
  | nil => exact (Semiring.mul_zero a).symm
  | cons i items ih =>
    change a * f i + total items (fun j => a * f j) = a * (f i + total items f)
    rw [ih, Semiring.left_distrib]

private theorem total_mul_right {ι : Type v} (items : List ι) (a : K) (f : ι → K) :
    total items (fun i => f i * a) = total items f * a := by
  induction items with
  | nil => exact (Semiring.zero_mul a).symm
  | cons i items ih =>
    change f i * a + total items (fun j => f j * a) = (f i + total items f) * a
    rw [ih, Semiring.right_distrib]

private theorem total_swap {ι : Type v} {κ : Type w} (is : List ι) (js : List κ)
    (f : ι → κ → K) :
    total is (fun i => total js (f i)) = total js (fun j => total is (fun i => f i j)) := by
  induction is with
  | nil => exact (total_zero js).symm
  | cons i is ih =>
    change total js (f i) + total is (fun i => total js (f i)) =
      total js (fun j => f i j + total is (fun i => f i j))
    rw [ih, total_add]

private theorem evalAngular_add (x : K) (p q : List Int) :
    evalAngular x (addAngular p q) = evalAngular x p + evalAngular x q := by
  induction p generalizing q with
  | nil => simp [addAngular, evalAngular, AddCommMonoid.zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [addAngular, evalAngular, Semiring.add_zero]
    | cons b q =>
      simp only [addAngular, evalAngular, Ring.intCast_add, ih]
      grind

private theorem eval_add (k x : K) (p q : Polynomial) :
    evalPoly k x (add p q) = evalPoly k x p + evalPoly k x q := by
  induction p generalizing q with
  | nil => simp [add, evalPoly, AddCommMonoid.zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [add, evalPoly, Semiring.add_zero]
    | cons b q =>
      simp only [add, evalPoly, evalAngular_add, ih]
      grind

private theorem evalAngular_scale (x : K) (n : Int) (p : List Int) :
    evalAngular x (p.map (n * ·)) = (n : K) * evalAngular x p := by
  induction p with
  | nil => simp [evalAngular, Semiring.mul_zero]
  | cons a p ih =>
    simp only [List.map_cons, evalAngular, Ring.intCast_mul, ih]
    grind

private theorem eval_scale (k x : K) (n : Int) (p : Polynomial) :
    evalPoly k x (scale n p) = (n : K) * evalPoly k x p := by
  induction p with
  | nil => simp [scale, evalPoly, Semiring.mul_zero]
  | cons a p ih =>
    simp only [scale, List.map_cons, evalPoly, evalAngular_scale] at *
    grind

private theorem evalAngular_shift (x : K) (n : Nat) (p : List Int) :
    evalAngular x (List.replicate n 0 ++ p) = x ^ n * evalAngular x p := by
  induction n with
  | zero => simp [Semiring.pow_zero, Semiring.one_mul]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evalAngular, Ring.intCast_zero,
      AddCommMonoid.zero_add, ih, Semiring.pow_succ]
    grind

private theorem eval_shift (k x : K) (n : Nat) (p : Polynomial) :
    evalPoly k x (List.replicate n [] ++ p) = k ^ n * evalPoly k x p := by
  induction n with
  | zero => simp [Semiring.pow_zero, Semiring.one_mul]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evalPoly, evalAngular,
      AddCommMonoid.zero_add, ih, Semiring.pow_succ]
    grind

private theorem evalAngular_shift_scale (x : K) (n : Nat) (s : Int) (row : List Int) :
    evalAngular x (shiftAngularScale n s row) = (s : K) * x ^ n * evalAngular x row := by
  cases row with
  | nil => simp [shiftAngularScale, evalAngular, Semiring.mul_zero]
  | cons a row =>
    simp only [shiftAngularScale, List.isEmpty_cons, Bool.false_eq_true, ite_false,
      evalAngular_shift, evalAngular_scale]
    grind

private theorem eval_map_shift_angular (k x : K) (n : Nat) (s : Int) (p : Polynomial) :
    evalPoly k x (p.map (shiftAngularScale n s)) = (s : K) * x ^ n * evalPoly k x p := by
  induction p with
  | nil => simp [evalPoly, Semiring.mul_zero]
  | cons a p ih =>
    simp only [List.map_cons, evalPoly, evalAngular_shift_scale, ih]
    grind

private theorem eval_multiplyMonomial (k x : K) (p : Polynomial) (t : Monomial) :
    evalPoly k x (multiplyMonomial p t) = evalPoly k x p * evalMonomial k x t := by
  change evalPoly k x (List.replicate t.1 [] ++ p.map (shiftAngularScale t.2.1 t.2.2)) = _
  rw [eval_shift, eval_map_shift_angular, evalMonomial]
  grind

private theorem eval_multiply (k x : K) (p : Polynomial) (ts : List Monomial) :
    evalPoly k x (multiply p ts) = evalPoly k x p * total ts (evalMonomial k x) := by
  induction ts with
  | nil => simp [multiply, total, evalPoly, Semiring.mul_zero]
  | cons t ts ih =>
    simp only [multiply, List.foldr_cons, eval_add, eval_multiplyMonomial, total] at *
    rw [ih, Semiring.left_distrib]

private theorem evalAngular_of_zero (x : K) (p : List Int)
    (hp : p.all (· == 0) = true) : evalAngular x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hp
    simp [evalAngular, hp.1, Ring.intCast_zero, ih hp.2, Semiring.mul_zero, Semiring.add_zero]

private theorem eval_of_zero (k x : K) (p : Polynomial) (hp : isZero p = true) :
    evalPoly k x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true] at hp
    simp [evalPoly, evalAngular_of_zero x a hp.1, ih hp.2, Semiring.mul_zero, Semiring.add_zero]

private theorem eval_project_over (k x : K) (weight : Nat → Polynomial)
    (column : List (List Monomial)) (items : List Nat) :
    evalPoly k x (items.foldr (fun i acc => add (multiply (weight i) (termsAt column i)) acc) []) =
      total items (fun i => evalPoly k x (weight i) * total (termsAt column i) (evalMonomial k x)) := by
  induction items with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldr_cons, eval_add, eval_multiply, total] at *
    rw [ih]

private theorem eval_project (k x : K) (column : List (List Monomial)) :
    evalPoly k x (project column) =
      total rows (fun i => evalPoly k x (weightAt i) * total (termsAt column i) (evalMonomial k x)) :=
  eval_project_over k x weightAt column rows

private theorem evalAngular_cast (n : Int) (p : List Int) :
    ((SchwarzschildAngularObstruction.evalPoly n p : Int) : K) = evalAngular (n : K) p := by
  induction p with
  | nil => exact Ring.intCast_zero
  | cons a p ih =>
    simp only [SchwarzschildAngularObstruction.evalPoly, evalAngular, Ring.intCast_add, Ring.intCast_mul, ih]

end Evaluation

section Exclusion

variable {K : Type u} [Field K] [IsCharP K 0]

private def qValue (ell : K) : K := (2 * ell + 1) * (2 * ell - 1) * (ell + 1)

def gamma (ell : K) : K :=
  (2 * ell - 1) * (2 * ell) * (2 * ell + 1) * (2 * ell + 2) / 24

def sourceClearance (k ell : K) : K :=
  (sourceScale : K) * 6 * qValue ell * (k - gamma ell)

/-- The matrix entry at the supplied angular label and frequency. -/
def matrixEntry (k ell : K) (column : Nat × Int) (row : Nat) : K :=
  total (termsAt (matrixColumn column) row) (evalMonomial k ell)

def clearedSourceEntry (k ell : K) (row : Nat) : K :=
  total (termsAt clearedSource row) (evalMonomial k ell)

def sourceEntry (k ell : K) (row : Nat) : K :=
  clearedSourceEntry k ell row / sourceClearance k ell

def witnessEntry (k ell : K) (row : Nat) : K :=
  evalPoly k ell (weightAt row)

private theorem intCast_nonzero (z : Int) (h : z ≠ 0) : (z : K) ≠ 0 := by
  intro hzero
  have hz := (IsCharP.intCast_eq_zero_iff (α := K) 0 z).mp hzero
  exact h (by simpa using hz)

omit [IsCharP K 0] in
private theorem product_nonzero {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => (Field.of_mul_eq_zero h).elim ha hb

omit [IsCharP K 0] in
private theorem power_nonzero {a : K} (ha : a ≠ 0) (n : Nat) : a ^ n ≠ 0 := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact Ne.symm Field.zero_ne_one
  | succ n ih => rw [Semiring.pow_succ]; exact product_nonzero ih ha

private theorem q_nonzero (n : Nat) (hn : 2 ≤ n) : qValue (((n : Int) : K)) ≠ 0 := by
  have hfirst : (2 * (n : Int) + 1) ≠ 0 := by omega
  have hsecond : (2 * (n : Int) - 1) ≠ 0 := by omega
  have hthird : ((n : Int) + 1) ≠ 0 := by omega
  have f := intCast_nonzero (K := K) _ hfirst
  have s := intCast_nonzero (K := K) _ hsecond
  have t := intCast_nonzero (K := K) _ hthird
  have c1 : ((1 : Int) : K) = 1 := Ring.intCast_one
  have c2 : ((2 : Int) : K) = 2 := Ring.intCast_ofNat 2
  simp only [Ring.intCast_add, Ring.intCast_sub, Ring.intCast_mul, c1, c2] at f s t
  exact product_nonzero (product_nonzero f s) t

private theorem sourceClearance_nonzero (n : Nat) (hn : 2 ≤ n) (k : K)
    (hgamma : k ≠ gamma (((n : Int) : K))) :
    sourceClearance k (((n : Int) : K)) ≠ 0 := by
  have hscale : (sourceScale : K) ≠ 0 :=
    intCast_nonzero _ (by decide +kernel)
  have hsix : (6 : K) ≠ 0 := by
    have h := intCast_nonzero (K := K) 6 (by decide)
    have c6 : ((6 : Int) : K) = 6 := Ring.intCast_ofNat 6
    rwa [c6] at h
  have hfreq : k - gamma (((n : Int) : K)) ≠ 0 := by
    intro heq
    apply hgamma
    grind
  exact product_nonzero (product_nonzero (product_nonzero hscale hsix) (q_nonzero n hn)) hfreq

private theorem angularCoefficients_match :
    angularCoefficients = SchwarzschildAngularObstruction.coefficients := by
  decide +kernel

omit [IsCharP K 0] in
private theorem eval_target (k ell : K) :
    evalPoly k ell target = qValue ell * k ^ (6 : Nat) * evalAngular ell angularCoefficients := by
  rw [target, eval_multiply]
  simp only [q, angularPolynomial, evalPoly, Semiring.mul_zero, Semiring.add_zero,
    List.map_cons, List.map_nil, total, List.foldr_cons, List.foldr_nil, evalMonomial,
    Ring.intCast_neg_one, Semiring.pow_zero,
    Semiring.pow_one, Semiring.mul_one, qValue]
  grind

omit [IsCharP K 0] in
private theorem source_projection_formula (sourceIdentity : isZero sourceResidual = true)
    (k ell : K) :
    (angularScale : K) * total rows (fun i => witnessEntry k ell i * clearedSourceEntry k ell i) =
      ((6 * witnessScale * sourceScale : Int) : K) *
        (qValue ell * k ^ (6 : Nat) * evalAngular ell angularCoefficients) := by
  have h := eval_of_zero k ell sourceResidual sourceIdentity
  rw [sourceResidual, eval_add, eval_scale, eval_project, eval_scale, eval_target] at h
  simp only [Ring.intCast_neg, Ring.neg_mul] at h
  change (angularScale : K) * total rows
      (fun i => witnessEntry k ell i * clearedSourceEntry k ell i) + _ = 0 at h
  grind

private theorem source_projection_nonzero
    (sourceIdentity : isZero sourceResidual = true)
    (n : Nat) (hn : 2 ≤ n) (k : K) (hk : k ≠ 0) :
    total rows (fun i => witnessEntry k (((n : Int) : K)) i *
      clearedSourceEntry k (((n : Int) : K)) i) ≠ 0 := by
  let ell : K := ((n : Int) : K)
  have hangular : evalAngular ell angularCoefficients ≠ 0 := by
    rw [angularCoefficients_match, ← evalAngular_cast]
    exact intCast_nonzero _ (SchwarzschildAngularObstruction.nonzero_at_physical_labels n hn)
  have hscale : ((6 * witnessScale * sourceScale : Int) : K) ≠ 0 :=
    intCast_nonzero _ (by decide +kernel)
  intro heq
  have h := source_projection_formula sourceIdentity k ell
  change total rows (fun i => witnessEntry k ell i * clearedSourceEntry k ell i) = 0 at heq
  rw [heq, Semiring.mul_zero] at h
  exact product_nonzero hscale
    (product_nonzero (product_nonzero (q_nonzero n hn) (power_nonzero hk 6)) hangular) h.symm

omit [IsCharP K 0] in
private theorem projected_column_zero
    (columnIdentities : columnLabels.all (fun column => isZero (project (matrixColumn column))) = true)
    (k ell : K) (column : Nat × Int) (hm : column ∈ columnLabels) :
    total rows (fun i => witnessEntry k ell i * matrixEntry k ell column i) = 0 := by
  have hp := List.all_eq_true.mp columnIdentities column hm
  exact (eval_project k ell (matrixColumn column)) ▸ eval_of_zero k ell _ hp

def matrixApply (k ell : K) (x : (Nat × Int) → K) (row : Nat) : K :=
  total columnLabels (fun column => matrixEntry k ell column row * x column)

omit [IsCharP K 0] in
private theorem projection_match_eval (items : List Nat) (weight : Nat → Polynomial)
    (k ell : K) (column : Nat × Int) (target : Polynomial)
    (check : coordinateProjectionMatches items weight column target = true) :
    total items (fun i => evalPoly k ell (weight i)*matrixEntry k ell column i) =
      evalPoly k ell target := by
  unfold coordinateProjectionMatches at check
  have eq := eval_of_zero k ell _ check
  rw [eval_add,eval_project_over,eval_scale] at eq
  unfold matrixEntry
  grind

omit [IsCharP K 0] in
private theorem total_single {A : Type v} [DecidableEq A] (items : List A)
    (unique : items.Nodup) {coordinate : A} (member : coordinate ∈ items) (value : K) :
    total items (fun i => if i = coordinate then value else 0) = value := by
  induction items with
  | nil => simp at member
  | cons a items ih =>
    have rest := (List.nodup_cons.mp unique).2
    change (if a = coordinate then value else 0) +
      total items (fun i => if i = coordinate then value else 0) = value
    by_cases eq : a = coordinate
    · subst a
      have none := (List.nodup_cons.mp unique).1
      have vanishes : total items (fun i => if i = coordinate then value else 0) = 0 := by
        calc
          _ = total items (fun _ => (0 : K)) := by
            apply total_congr
            intro i hi
            have unequal : i ≠ coordinate := fun q => none (q ▸ hi)
            simp only [if_neg unequal]
          _ = 0 := total_zero items
      rw [if_pos rfl,vanishes,Semiring.add_zero]
    · have ht : coordinate ∈ items := (List.mem_cons.mp member).resolve_left (fun h => eq h.symm)
      rw [if_neg eq,ih rest ht,AddCommMonoid.zero_add]

omit [IsCharP K 0] in
/-- A checked row combination isolates one coefficient of a homogeneous solution. -/
theorem coordinate_from_kernel_projection (items : List Nat) (active : List (Nat × Int))
    (weight : Nat → Polynomial) (coordinate : Nat × Int) (target : Polynomial)
    (member : coordinate ∈ columnLabels) (k ell : K) (x : (Nat × Int) → K)
    (support : ∀ col ∈ columnLabels, col ∉ active → x col = 0)
    (equations : ∀ i ∈ items, matrixApply k ell x i = 0)
    (checks : active.all (fun col =>
      coordinateProjectionMatches items weight col (if col = coordinate then target else [])) = true)
    (known : coordinate ∈ active) :
    evalPoly k ell target*x coordinate = 0 := by
  have vanish : total items (fun i => evalPoly k ell (weight i)*matrixApply k ell x i) = 0 := by
    rw [← total_zero items]
    apply total_congr
    intro i hi
    rw [equations i hi,Semiring.mul_zero]
  have unique : columnLabels.Nodup := by decide +kernel
  have sumEq : total items (fun i => evalPoly k ell (weight i)*matrixApply k ell x i) =
      total columnLabels (fun col => if col = coordinate then evalPoly k ell target*x coordinate else 0) := by
    calc
      _ = total items (fun i => total columnLabels
          (fun col => (evalPoly k ell (weight i)*matrixEntry k ell col i)*x col)) := by
        apply total_congr
        intro i _
        rw [matrixApply,← total_mul_left]
        apply total_congr
        intro col _
        exact (Semiring.mul_assoc _ _ _).symm
      _ = total columnLabels (fun col => total items
          (fun i => (evalPoly k ell (weight i)*matrixEntry k ell col i)*x col)) := total_swap _ _ _
      _ = _ := by
        apply total_congr
        intro col hi
        rw [total_mul_right]
        by_cases ha : col ∈ active
        · have projection := projection_match_eval items weight k ell col _
            (List.all_eq_true.mp checks col ha)
          rw [projection]
          by_cases isCoordinate : col = coordinate
          · subst col
            simp only [if_true]
          · simp only [if_neg isCoordinate,evalPoly,Semiring.zero_mul]
        · have isOther : col ≠ coordinate := fun h => ha (h ▸ known)
          rw [support col hi ha,Semiring.mul_zero,if_neg isOther]
  rw [← total_single columnLabels unique member (evalPoly k ell target*x coordinate),← sumEq]
  exact vanish

omit [IsCharP K 0] in
private theorem weighted_apply_zero
    (columnIdentities : columnLabels.all (fun column => isZero (project (matrixColumn column))) = true)
    (k ell : K) (x : (Nat × Int) → K) :
    total rows (fun i => witnessEntry k ell i * matrixApply k ell x i) = 0 := by
  calc
    _ = total rows (fun i => total columnLabels
        (fun col => (witnessEntry k ell i * matrixEntry k ell col i) * x col)) := by
      apply total_congr
      intro i _
      rw [matrixApply, ← total_mul_left]
      apply total_congr
      intro col _
      exact (Semiring.mul_assoc _ _ _).symm
    _ = total columnLabels (fun col => total rows
        (fun i => (witnessEntry k ell i * matrixEntry k ell col i) * x col)) := total_swap _ _ _
    _ = total columnLabels (fun _ => 0) := by
      apply total_congr
      intro col hm
      rw [total_mul_right, projected_column_zero columnIdentities k ell col hm, Semiring.zero_mul]
    _ = 0 := total_zero _

private theorem no_solution_of_checks
    (columnIdentities : columnLabels.all (fun column => isZero (project (matrixColumn column))) = true)
    (sourceIdentity : isZero sourceResidual = true)
    (n : Nat) (hn : 2 ≤ n) (k : K) (hk : k ≠ 0)
    (hgamma : k ≠ gamma (((n : Int) : K))) :
    ¬ ∃ x : (Nat × Int) → K, ∀ i ∈ rows,
      matrixApply k (((n : Int) : K)) x i = sourceEntry k (((n : Int) : K)) i := by
  rintro ⟨x, hx⟩
  let ell : K := ((n : Int) : K)
  let d := sourceClearance k ell
  have hd : d ≠ 0 := sourceClearance_nonzero n hn k hgamma
  apply source_projection_nonzero sourceIdentity n hn k hk
  calc
    _ = total rows (fun i => (witnessEntry k ell i * matrixApply k ell x i) * d) := by
      apply total_congr
      intro i hm
      rw [hx i hm, sourceEntry, Semiring.mul_assoc, Field.div_mul_cancel hd]
    _ = 0 := by rw [total_mul_right, weighted_apply_zero columnIdentities, Semiring.zero_mul]

end Exclusion

attribute [local instance] Lean.Grind.Ring.intCast

section Results

variable {K : Type u} [Lean.Grind.Field K] [Lean.Grind.IsCharP K 0]

omit [Lean.Grind.IsCharP K 0] in
/-- The saved witness annihilates each column of the reconstructed Laurent matrix. -/
theorem annihilates_column (k ell : K) (column : Nat × Int) (hm : column ∈ columnLabels) :
    total rows (fun i => witnessEntry k ell i * matrixEntry k ell column i) = 0 :=
  projected_column_zero columnIdentities k ell column hm

omit [Lean.Grind.IsCharP K 0] in
/-- Exact polynomial form of the odd-source projection after clearing denominators. -/
theorem source_projection_identity (k ell : K) :
    (angularScale : K) * total rows (fun i => witnessEntry k ell i * clearedSourceEntry k ell i) =
      ((6 * witnessScale * sourceScale : Int) : K) *
        (qValue ell * k ^ (6 : Nat) * evalAngular ell angularCoefficients) :=
  source_projection_formula sourceIdentity k ell

/-- The projection of the denominator-cleared odd source is nonzero. -/
theorem projected_source_nonzero (n : Nat) (hn : 2 ≤ n) (k : K) (hk : k ≠ 0) :
    total rows (fun i => witnessEntry k (((n : Int) : K)) i *
      clearedSourceEntry k (((n : Int) : K)) i) ≠ 0 :=
  source_projection_nonzero sourceIdentity n hn k hk

/-- At every physical angular label, the Laurent system has no solution.
In the scattering problem, k is purely imaginary and nonzero, and Gamma is real. -/
theorem no_solution (n : Nat) (hn : 2 ≤ n) (k : K) (hk : k ≠ 0)
    (hgamma : k ≠ gamma (((n : Int) : K))) :
    ¬ ∃ x : (Nat × Int) → K, ∀ i ∈ rows,
      matrixApply k (((n : Int) : K)) x i = sourceEntry k (((n : Int) : K)) i :=
  no_solution_of_checks columnIdentities sourceIdentity n hn k hk hgamma

end Results

#print axioms annihilates_column
#print axioms source_projection_identity
#print axioms projected_source_nonzero
#print axioms no_solution

end SchwarzschildMatrix
