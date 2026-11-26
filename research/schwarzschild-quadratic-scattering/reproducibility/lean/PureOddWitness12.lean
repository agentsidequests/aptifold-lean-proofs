import PureOddWitness11

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f540 : Formula := .add f536 f539
def num540 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den540 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel540 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def p540 : Fraction := ⟨num540, den540⟩
theorem h540 : Reduced f540 p540 := .add h536 h539 ⟨cancel540, by decide +kernel, by decide +kernel⟩

def f541 : Formula := .mul f103 f335
def num541 : Expr := .bands [

]

def den541 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel541 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p541 : Fraction := ⟨num541, den541⟩
theorem h541 : Reduced f541 p541 := .mul h103 h335 ⟨cancel541, by decide +kernel, by decide +kernel⟩

def f542 : Formula := .div f541 f107
def num542 : Expr := .bands [

]

def den542 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel542 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p542 : Fraction := ⟨num542, den542⟩
theorem h542 : Reduced f542 p542 := .div h541 h107 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel542, by decide +kernel, by decide +kernel⟩

def f543 : Formula := .add f540 f542
def num543 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den543 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel543 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p543 : Fraction := ⟨num543, den543⟩
theorem h543 : Reduced f543 p543 := .add h540 h542 ⟨cancel543, by decide +kernel, by decide +kernel⟩

def f544 : Formula := .neg f543
def p544 : Fraction := p543.neg
theorem h544 : Reduced f544 p544 := .neg h543

def f545 : Formula := .add f524 f544
def num545 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den545 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel545 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x40, 1⟩,
  ⟨5, 0, 1, 0x60, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x30, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def p545 : Fraction := ⟨num545, den545⟩
theorem h545 : Reduced f545 p545 := .add h524 h544 ⟨cancel545, by decide +kernel, by decide +kernel⟩

def f546 : Formula := .mul f33 f545
def num546 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den546 : Expr := .bands [
  ⟨4, 0, 1, 0xc, 0x0, 1⟩,
  ⟨5, 0, 3, 0x800000000000000000000000000040000000000000000000000000000, 0x4, 1⟩
]

def cancel546 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p546 : Fraction := ⟨num546, den546⟩
theorem h546 : Reduced f546 p546 := .mul h33 h545 ⟨cancel546, by decide +kernel, by decide +kernel⟩

def f547 : Formula := .mul f127 f289
def num547 : Expr := .bands [
  ⟨4, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨7, 4, 1, 0x1, 0x0, 1⟩
]

def den547 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel547 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p547 : Fraction := ⟨num547, den547⟩
theorem h547 : Reduced f547 p547 := .mul h127 h289 ⟨cancel547, by decide +kernel, by decide +kernel⟩

def f548 : Formula := .div f547 f81
def num548 : Expr := .bands [
  ⟨1, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨2, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x1, 0x0, 1⟩
]

def den548 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel548 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p548 : Fraction := ⟨num548, den548⟩
theorem h548 : Reduced f548 p548 := .div h547 h81 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel548, by decide +kernel, by decide +kernel⟩

def f549 : Formula := .mul f14 f310
def num549 : Expr := .bands [
  ⟨0, 1, 1, 0x4, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000002, 1⟩,
  ⟨2, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den549 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel549 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p549 : Fraction := ⟨num549, den549⟩
theorem h549 : Reduced f549 p549 := .mul h14 h310 ⟨cancel549, by decide +kernel, by decide +kernel⟩

def f550 : Formula := .mul f549 f288
def num550 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x4, 1⟩,
  ⟨1, 2, 3, 0x200000000000000000000000000020000000000000000000000000002, 0x0, 1⟩,
  ⟨2, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x0, 0x1, 1⟩
]

def den550 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel550 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p550 : Fraction := ⟨num550, den550⟩
theorem h550 : Reduced f550 p550 := .mul h549 h288 ⟨cancel550, by decide +kernel, by decide +kernel⟩

def f551 : Formula := .add f550 f311
def num551 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x1000000000000000000000000000100000000000000000000000000010, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000001400000000000000000000000000100000000000000000000000000004, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000800000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den551 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel551 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p551 : Fraction := ⟨num551, den551⟩
theorem h551 : Reduced f551 p551 := .add h550 h311 ⟨cancel551, by decide +kernel, by decide +kernel⟩

def f552 : Formula := .div f551 f67
def num552 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x1000000000000000000000000000100000000000000000000000000010, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000001400000000000000000000000000100000000000000000000000000004, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000800000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den552 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel552 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p552 : Fraction := ⟨num552, den552⟩
theorem h552 : Reduced f552 p552 := .div h551 h67 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel552, by decide +kernel, by decide +kernel⟩

def f553 : Formula := .add f548 f552
def num553 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x800000000000000000000000000080000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x20000000000000000000000000004000000000000000000000000000600000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den553 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel553 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x80, 1⟩,
  ⟨1, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x60, 1⟩,
  ⟨3, 0, 1, 0x10, 0x0, 1⟩
]

def p553 : Fraction := ⟨num553, den553⟩
theorem h553 : Reduced f553 p553 := .add h548 h552 ⟨cancel553, by decide +kernel, by decide +kernel⟩

def f554 : Formula := .div f380 f18
def num554 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000002, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den554 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel554 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p554 : Fraction := ⟨num554, den554⟩
theorem h554 : Reduced f554 p554 := .div h380 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel554, by decide +kernel, by decide +kernel⟩

def f555 : Formula := .neg f554
def p555 : Fraction := p554.neg
theorem h555 : Reduced f555 p555 := .neg h554

def f556 : Formula := .add f553 f555
def num556 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x14, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000008, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den556 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel556 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p556 : Fraction := ⟨num556, den556⟩
theorem h556 : Reduced f556 p556 := .add h553 h555 ⟨cancel556, by decide +kernel, by decide +kernel⟩

def f557 : Formula := .mul f146 f328
def num557 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000009, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den557 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel557 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p557 : Fraction := ⟨num557, den557⟩
theorem h557 : Reduced f557 p557 := .mul h146 h328 ⟨cancel557, by decide +kernel, by decide +kernel⟩

def f558 : Formula := .div f557 f149
def num558 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000009, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den558 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel558 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p558 : Fraction := ⟨num558, den558⟩
theorem h558 : Reduced f558 p558 := .div h557 h149 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel558, by decide +kernel, by decide +kernel⟩

def f559 : Formula := .add f556 f558
def num559 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000020000000000000000000000000000, 0x2, 1⟩,
  ⟨1, 0, 5, 0x200000000000000000000000000040000000000000000000000000000, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000004, 1⟩,
  ⟨2, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000002, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den559 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel559 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p559 : Fraction := ⟨num559, den559⟩
theorem h559 : Reduced f559 p559 := .add h556 h558 ⟨cancel559, by decide +kernel, by decide +kernel⟩

def f560 : Formula := .mul f113 f559
def num560 : Expr := .bands [
  ⟨0, 0, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 6, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 6, 0x100000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 4, 0x20000000000000000000000000000, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den560 : Expr := .bands [
  ⟨3, 0, 2, 0x20, 0x400000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x200000000000000000000000000000, 0x10, 1⟩
]

def cancel560 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p560 : Fraction := ⟨num560, den560⟩
theorem h560 : Reduced f560 p560 := .mul h113 h559 ⟨cancel560, by decide +kernel, by decide +kernel⟩

def f561 : Formula := .neg f152
def p561 : Fraction := p152.neg
theorem h561 : Reduced f561 p561 := .neg h152

def f562 : Formula := .add f560 f561
def num562 : Expr := .bands [
  ⟨0, 0, 4, 0x30000000000000000000000000000, 0x3000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den562 : Expr := .bands [
  ⟨3, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel562 : Expr := .bands [
  ⟨3, 0, 2, 0x40, 0x800000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x400000000000000000000000000000, 0x20, 1⟩
]

def p562 : Fraction := ⟨num562, den562⟩
theorem h562 : Reduced f562 p562 := .add h560 h561 ⟨cancel562, by decide +kernel, by decide +kernel⟩

def f563 : Formula := .mul f127 f335
def num563 : Expr := .bands [

]

def den563 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel563 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p563 : Fraction := ⟨num563, den563⟩
theorem h563 : Reduced f563 p563 := .mul h127 h335 ⟨cancel563, by decide +kernel, by decide +kernel⟩

def f564 : Formula := .div f563 f81
def num564 : Expr := .bands [

]

def den564 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel564 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def p564 : Fraction := ⟨num564, den564⟩
theorem h564 : Reduced f564 p564 := .div h563 h81 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel564, by decide +kernel, by decide +kernel⟩

def f565 : Formula := .mul f14 f193
def num565 : Expr := .bands [
  ⟨0, 1, 1, 0x2, 0x0, 1⟩
]

def den565 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel565 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p565 : Fraction := ⟨num565, den565⟩
theorem h565 : Reduced f565 p565 := .mul h14 h193 ⟨cancel565, by decide +kernel, by decide +kernel⟩

def f566 : Formula := .mul f565 f77
def num566 : Expr := .bands [

]

def den566 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel566 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p566 : Fraction := ⟨num566, den566⟩
theorem h566 : Reduced f566 p566 := .mul h565 h77 ⟨cancel566, by decide +kernel, by decide +kernel⟩

def f567 : Formula := .add f566 f343
def num567 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den567 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel567 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p567 : Fraction := ⟨num567, den567⟩
theorem h567 : Reduced f567 p567 := .add h566 h343 ⟨cancel567, by decide +kernel, by decide +kernel⟩

def f568 : Formula := .div f567 f67
def num568 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den568 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel568 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p568 : Fraction := ⟨num568, den568⟩
theorem h568 : Reduced f568 p568 := .div h567 h67 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel568, by decide +kernel, by decide +kernel⟩

def f569 : Formula := .add f564 f568
def num569 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den569 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel569 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p569 : Fraction := ⟨num569, den569⟩
theorem h569 : Reduced f569 p569 := .add h564 h568 ⟨cancel569, by decide +kernel, by decide +kernel⟩

def f570 : Formula := .div f402 f18
def num570 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den570 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel570 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p570 : Fraction := ⟨num570, den570⟩
theorem h570 : Reduced f570 p570 := .div h402 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel570, by decide +kernel, by decide +kernel⟩

def f571 : Formula := .neg f570
def p571 : Fraction := p570.neg
theorem h571 : Reduced f571 p571 := .neg h570

def f572 : Formula := .add f569 f571
def num572 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den572 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel572 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p572 : Fraction := ⟨num572, den572⟩
theorem h572 : Reduced f572 p572 := .add h569 h571 ⟨cancel572, by decide +kernel, by decide +kernel⟩

def f573 : Formula := .mul f146 f360
def num573 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den573 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel573 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p573 : Fraction := ⟨num573, den573⟩
theorem h573 : Reduced f573 p573 := .mul h146 h360 ⟨cancel573, by decide +kernel, by decide +kernel⟩

def f574 : Formula := .div f573 f149
def num574 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den574 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel574 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p574 : Fraction := ⟨num574, den574⟩
theorem h574 : Reduced f574 p574 := .div h573 h149 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel574, by decide +kernel, by decide +kernel⟩

def f575 : Formula := .add f572 f574
def num575 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den575 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel575 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p575 : Fraction := ⟨num575, den575⟩
theorem h575 : Reduced f575 p575 := .add h572 h574 ⟨cancel575, by decide +kernel, by decide +kernel⟩

def f576 : Formula := .mul f113 f575
def num576 : Expr := .bands [
  ⟨0, 0, 4, 0x1000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den576 : Expr := .bands [
  ⟨3, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel576 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p576 : Fraction := ⟨num576, den576⟩
theorem h576 : Reduced f576 p576 := .mul h113 h575 ⟨cancel576, by decide +kernel, by decide +kernel⟩

def f577 : Formula := .neg f576
def p577 : Fraction := p576.neg
theorem h577 : Reduced f577 p577 := .neg h576

def f578 : Formula := .add f562 f577
def num578 : Expr := .bands [
  ⟨0, 0, 4, 0x1000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den578 : Expr := .bands [
  ⟨3, 0, 2, 0x80000000000000000000000000000, 0x4, 1⟩
]

def cancel578 : Expr := .bands [
  ⟨3, 0, 2, 0x800000000000000000000000000000, 0x40, 1⟩,
  ⟨4, 0, 2, 0x40, 0x800000000000000000000000000000, 1⟩,
  ⟨5, 0, 2, 0x200000000000000000000000000000, 0x10, 1⟩
]

def p578 : Fraction := ⟨num578, den578⟩
theorem h578 : Reduced f578 p578 := .add h562 h577 ⟨cancel578, by decide +kernel, by decide +kernel⟩

def f579 : Formula := .mul f112 f578
def num579 : Expr := .bands [
  ⟨0, 0, 4, 0x10000000000000000000000000000, 0x1000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den579 : Expr := .bands [
  ⟨4, 0, 2, 0x40000000000000000000000000000, 0x2, 1⟩
]

def cancel579 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p579 : Fraction := ⟨num579, den579⟩
theorem h579 : Reduced f579 p579 := .mul h112 h578 ⟨cancel579, by decide +kernel, by decide +kernel⟩

def f580 : Formula := .mul f161 f411
def num580 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x9000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x4e00000000000000000000000000000000000000000000000000000000, 0x12000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x90000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0xc00000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den580 : Expr := .bands [
  ⟨6, 0, 1, 0x6, 0x0, 1⟩,
  ⟨7, 0, 3, 0x400000000000000000000000000020000000000000000000000000000, 0x2, 1⟩
]

def cancel580 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def p580 : Fraction := ⟨num580, den580⟩
theorem h580 : Reduced f580 p580 := .mul h161 h411 ⟨cancel580, by decide +kernel, by decide +kernel⟩

def f581 : Formula := .dr f413
def num581 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x2400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x0, 0x50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den581 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def cancel581 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p581 : Fraction := ⟨num581, den581⟩
theorem h581 : Reduced f581 p581 := .dr h413 ⟨cancel581, by decide +kernel, by decide +kernel⟩

def f582 : Formula := .mul f1 f286
def num582 : Expr := .bands [
  ⟨0, 0, 3, 0x3000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 4, 0x0, 0x8000000000000000000000000002000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x30000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 5, 0x0, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den582 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x10, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel582 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p582 : Fraction := ⟨num582, den582⟩
theorem h582 : Reduced f582 p582 := .mul h1 h286 ⟨cancel582, by decide +kernel, by decide +kernel⟩

def f583 : Formula := .mul f582 f189
def num583 : Expr := .bands [
  ⟨0, 0, 3, 0x3000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 4, 0x0, 0x8000000000000000000000000002000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x30000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 5, 0x0, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den583 : Expr := .bands [
  ⟨7, 0, 1, 0x20, 0x0, 1⟩,
  ⟨8, 0, 1, 0x0, 0x20, 1⟩,
  ⟨9, 0, 1, 0x8, 0x0, 1⟩
]

def cancel583 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p583 : Fraction := ⟨num583, den583⟩
theorem h583 : Reduced f583 p583 := .mul h582 h189 ⟨cancel583, by decide +kernel, by decide +kernel⟩

def f584 : Formula := .add f581 f583
def num584 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xf000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000000000000000000000000000000000000, 0x280000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x2000000000000000000000000000400000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 5, 0x0, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den584 : Expr := .bands [
  ⟨7, 0, 1, 0x20, 0x0, 1⟩,
  ⟨8, 0, 1, 0x0, 0x20, 1⟩,
  ⟨9, 0, 1, 0x8, 0x0, 1⟩
]

def cancel584 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def p584 : Fraction := ⟨num584, den584⟩
theorem h584 : Reduced f584 p584 := .add h581 h583 ⟨cancel584, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
