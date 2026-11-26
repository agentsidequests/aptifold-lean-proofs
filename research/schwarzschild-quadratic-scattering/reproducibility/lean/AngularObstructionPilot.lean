import Init

/-!
Aptifold's Schwarzschild angular obstruction.

The coefficients are the numerator's angular polynomial A, in ascending order,
multiplied by its positive common denominator 1983396792657499914240000.
The input is the `pure_odd_obstruction.numerator` field in the referee supplement's
`certificate/data/obstruction.json` (SHA-256 706383d67b06c2bbe255e0ea3ada5f54cb2d4194c67a3b57c1edaff470050e00).
This proof checks nonvanishing of the encoded polynomial. It takes the paper's
identification of A with the projected left-null witness as input.
-/

namespace SchwarzschildAngularObstruction

def coefficients : List Int := [
  0, 0, 0,
  0, -8323210058846732491941273600000, 180406990025700898944803927040000,
  1760050934507005271060964090624000, -8237638705740480206875644760512000, -65823430024623935312649448176481920,
  -87948166128505834544360052799152960, 250837504631258262940849978453246272, 921308517206105665321977750139127904,
  643434556710400473179677853521143000, -1960567150588519836777021334668423204, -4936408077861040632727389723990148464,
  -2685395728223570847898899776409776514, 6864247592751588789935174873031778554, 14937203640347392848378571112610237516,
  8121909161375487201391592342494955742, -13455039294046829725602372808496387361, -29026168010545920424785748163764643751,
  -17321194965395995209378704230939810848, 15657273607273839443999220750751898611, 37889777198212541519412354854714000366,
  25472091867732820869382069302010850755, -9919863284595264303935422250705517087, -33751786654597467978496391383630954683,
  -25854132018336167007856174577726324621, 1312947848547900900347825183852896476, 20417220324835760882400661367745945976,
  18062384027668048717792482409562602516, 3128476629599944226728033439868652398, -8080184315394360850690858923201823717,
  -8542228633472139127800079695499566357, -2782171910012773831420394406628540811, 1880486194949781357366065781458688880,
  2618173905846334727472914193275181060, 1117209024566246351267396192483998486, -184401792594955901961791300164285137,
  -462277278986875758888626173724324922, -202099732044847474786608530237202085, 9016700831058792660206730373413013,
  31056447913225991851774066320449597, -10730826113336750730473463717310407, -19892604560209271916223285132418118,
  -768784347514867884113945186635282, 12593550903328147443763895171961996, 10230795650944073390702143238344310,
  2253882878519411532620045417134421, -2173397935677596887280225657897565, -2189833666785798658216425144311045,
  -776371127829083011491855193282443, 81464082996653511529311100764509, 217264102636903239069721392182192,
  99041945697644282229560715400398, 11602923205707230619808013233178, -9124643225685419128031056905072,
  -4900091097845456381189489064696, -764010695178763429939550640432, 135390234705796983862984684032,
  64162082615957097896416500288, 2874784208692394523692918016, -2182620435714804894259368960,
  -387582062718362367582720000, -8450608905756229976064000, 1983396792657499914240000]

def evalPoly (x : Int) : List Int → Int
  | [] => 0
  | a :: tail => a + x * evalPoly x tail

private def addConstant (a : Int) : List Int → List Int
  | [] => [a]
  | b :: tail => (a + b) :: tail

private def mulByXPlus (s : Int) : List Int → List Int
  | [] => []
  | a :: tail => (s * a) :: addConstant a (mulByXPlus s tail)

private def translate (s : Int) : List Int → List Int
  | [] => []
  | a :: tail => addConstant a (mulByXPlus s (translate s tail))

private theorem eval_addConstant (a x : Int) (p : List Int) :
    evalPoly x (addConstant a p) = a + evalPoly x p := by
  cases p <;> simp [addConstant, evalPoly, Int.add_assoc]

private theorem eval_mulByXPlus (s x : Int) (p : List Int) :
    evalPoly x (mulByXPlus s p) = (s + x) * evalPoly x p := by
  induction p with
  | nil => simp [mulByXPlus, evalPoly]
  | cons a p ih =>
    simp only [mulByXPlus, evalPoly, eval_addConstant, ih]
    rw [Int.mul_add x a, ← Int.add_assoc, ← Int.add_mul s x a, Int.mul_add (s + x) a]
    rw [Int.mul_left_comm x (s + x)]

private theorem eval_translate (s x : Int) (p : List Int) :
    evalPoly x (translate s p) = evalPoly (s + x) p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [translate, eval_addConstant, eval_mulByXPlus, ih, evalPoly]

private theorem eval_nonneg (x : Int) (hx : 0 ≤ x) (p : List Int)
    (hp : p.all (fun c => decide (0 ≤ c)) = true) : 0 ≤ evalPoly x p := by
  induction p with
  | nil => simp [evalPoly]
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact Int.add_nonneg hp.1 (Int.mul_nonneg hx (ih hp.2))

private theorem eval_pos (x : Int) (hx : 0 ≤ x) (p : List Int)
    (hp : p.all (fun c => decide (0 ≤ c)) = true) (h0 : 0 < p.headD 0) :
    0 < evalPoly x p := by
  cases p with
  | nil => simp at h0
  | cons a p =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    have htail := Int.mul_nonneg hx (eval_nonneg x hx p hp.2)
    simp only [List.headD_cons] at h0
    simp only [evalPoly]
    omega

private theorem initialLabels :
    (List.range 16).all (fun n => decide (evalPoly ((n + 2 : Nat) : Int) coefficients ≠ 0)) =
      true := by
  decide +kernel

private theorem translatedSigns :
    (translate 18 coefficients).all (fun c => decide (0 ≤ c)) = true := by
  decide +kernel

private theorem translatedConstant : 0 < (translate 18 coefficients).headD 0 := by
  decide +kernel

/-- The encoded angular factor has no zeros at any integer label from 2 onward. -/
theorem nonzero_at_physical_labels (n : Nat) (hn : 2 ≤ n) :
    evalPoly (n : Int) coefficients ≠ 0 := by
  by_cases h : n < 18
  · have hidx : n - 2 ∈ List.range 16 := List.mem_range.mpr (by omega)
    have hlabel : n - 2 + 2 = n := by omega
    have hvalue := (List.all_eq_true.mp initialLabels) (n - 2) hidx
    simpa only [hlabel, decide_eq_true_eq] using hvalue
  · have hx : 0 ≤ (n : Int) - 18 := by omega
    have hsum : 18 + ((n : Int) - 18) = (n : Int) := by omega
    have hpositive := eval_pos ((n : Int) - 18) hx (translate 18 coefficients)
      translatedSigns translatedConstant
    rw [eval_translate, hsum] at hpositive
    omega

#print axioms nonzero_at_physical_labels

end SchwarzschildAngularObstruction
