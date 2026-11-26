import QuadraticConservationArithmetic064

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2600 : Formula := .mul f2599 f2166
def num2600 : Expr := .bands [
  ⟨1, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2600 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2600 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2600 : Fraction := ⟨num2600, den2600⟩
theorem h2600 : Reduced f2600 p2600 := .mul h2599 h2166 ⟨cancel2600, by decide +kernel, by decide +kernel⟩

def f2601 : Formula := .mul f2182 f5
def num2601 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def den2601 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2601 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2601 : Fraction := ⟨num2601, den2601⟩
theorem h2601 : Reduced f2601 p2601 := .mul h2182 h5 ⟨cancel2601, by decide +kernel, by decide +kernel⟩

def f2602 : Formula := .div f2600 f2601
def num2602 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2602 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2602 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2602 : Fraction := ⟨num2602, den2602⟩
theorem h2602 : Reduced f2602 p2602 := .div h2600 h2601 [.integer (2), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2602, by decide +kernel, by decide +kernel⟩

def f2603 : Formula := .mul f16 f2356
def num2603 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2603 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2603 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2603 : Fraction := ⟨num2603, den2603⟩
theorem h2603 : Reduced f2603 p2603 := .mul h16 h2356 ⟨cancel2603, by decide +kernel, by decide +kernel⟩

def f2604 : Formula := .mul f2603 f491
def num2604 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2604 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2604 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2604 : Fraction := ⟨num2604, den2604⟩
theorem h2604 : Reduced f2604 p2604 := .mul h2603 h491 ⟨cancel2604, by decide +kernel, by decide +kernel⟩

def f2605 : Formula := .mul f2604 f2185
def num2605 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x60000000000000000000000000008000000000000000000000000000e00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2605 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2605 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2605 : Fraction := ⟨num2605, den2605⟩
theorem h2605 : Reduced f2605 p2605 := .mul h2604 h2185 ⟨cancel2605, by decide +kernel, by decide +kernel⟩

def f2606 : Formula := .div f2605 f2526
def num2606 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x60000000000000000000000000008000000000000000000000000000e00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2606 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2606 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2606 : Fraction := ⟨num2606, den2606⟩
theorem h2606 : Reduced f2606 p2606 := .div h2605 h2526 [.integer (4), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2606, by decide +kernel, by decide +kernel⟩

def f2607 : Formula := .add f2602 f2606
def num2607 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x60000000000000000000000000008000000000000000000000000000e00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2607 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2607 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def p2607 : Fraction := ⟨num2607, den2607⟩
theorem h2607 : Reduced f2607 p2607 := .add h2602 h2606 ⟨cancel2607, by decide +kernel, by decide +kernel⟩

def f2608 : Formula := .mul f16 f44
def num2608 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2608 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2608 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2608 : Fraction := ⟨num2608, den2608⟩
theorem h2608 : Reduced f2608 p2608 := .mul h16 h44 ⟨cancel2608, by decide +kernel, by decide +kernel⟩

def f2609 : Formula := .mul f2608 f5
def num2609 : Expr := .bands [
  ⟨0, 0, 3, 0x20000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2609 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2609 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2609 : Fraction := ⟨num2609, den2609⟩
theorem h2609 : Reduced f2609 p2609 := .mul h2608 h5 ⟨cancel2609, by decide +kernel, by decide +kernel⟩

def f2610 : Formula := .mul f2609 f2166
def num2610 : Expr := .bands [
  ⟨2, 1, 3, 0x10000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2610 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2610 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2610 : Fraction := ⟨num2610, den2610⟩
theorem h2610 : Reduced f2610 p2610 := .mul h2609 h2166 ⟨cancel2610, by decide +kernel, by decide +kernel⟩

def f2611 : Formula := .mul f2610 f2178
def num2611 : Expr := .bands [
  ⟨3, 2, 3, 0x40000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2611 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2611 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2611 : Fraction := ⟨num2611, den2611⟩
theorem h2611 : Reduced f2611 p2611 := .mul h2610 h2178 ⟨cancel2611, by decide +kernel, by decide +kernel⟩

def f2612 : Formula := .div f2611 f2199
def num2612 : Expr := .bands [
  ⟨0, 2, 3, 0x40000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2612 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2612 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2612 : Fraction := ⟨num2612, den2612⟩
theorem h2612 : Reduced f2612 p2612 := .div h2611 h2199 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2612, by decide +kernel, by decide +kernel⟩

def f2613 : Formula := .neg f2612
def p2613 : Fraction := p2612.neg
theorem h2613 : Reduced f2613 p2613 := .neg h2612

def f2614 : Formula := .add f2607 f2613
def num2614 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x3000000000000000000000000000100000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000003400000000000000000000000000100000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0xc0000000000000000000000000010000000000000000000000000001000000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2614 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2614 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x10, 0x0, 1⟩
]

def p2614 : Fraction := ⟨num2614, den2614⟩
theorem h2614 : Reduced f2614 p2614 := .add h2607 h2613 ⟨cancel2614, by decide +kernel, by decide +kernel⟩

def f2615 : Formula := .mul f2182 f16
def num2615 : Expr := .bands [
  ⟨1, 0, 2, 0x20000000000000000000000000000, 0x0, 1⟩
]

def den2615 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2615 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2615 : Fraction := ⟨num2615, den2615⟩
theorem h2615 : Reduced f2615 p2615 := .mul h2182 h16 ⟨cancel2615, by decide +kernel, by decide +kernel⟩

def f2616 : Formula := .add f2615 f3
def num2616 : Expr := .bands [
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den2616 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2616 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2616 : Fraction := ⟨num2616, den2616⟩
theorem h2616 : Reduced f2616 p2616 := .add h2615 h3 ⟨cancel2616, by decide +kernel, by decide +kernel⟩

def f2617 : Formula := .neg f2355
def p2617 : Fraction := p2355.neg
theorem h2617 : Reduced f2617 p2617 := .neg h2355

def f2618 : Formula := .add f2616 f2617
def num2618 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x30000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den2618 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2618 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2618 : Fraction := ⟨num2618, den2618⟩
theorem h2618 : Reduced f2618 p2618 := .add h2616 h2617 ⟨cancel2618, by decide +kernel, by decide +kernel⟩

def f2619 : Formula := .add f2618 f4
def num2619 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x30000000000000000000000000002, 1⟩,
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den2619 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2619 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2619 : Fraction := ⟨num2619, den2619⟩
theorem h2619 : Reduced f2619 p2619 := .add h2618 h4 ⟨cancel2619, by decide +kernel, by decide +kernel⟩

def f2620 : Formula := .mul f16 f2619
def num2620 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2620 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2620 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2620 : Fraction := ⟨num2620, den2620⟩
theorem h2620 : Reduced f2620 p2620 := .mul h16 h2619 ⟨cancel2620, by decide +kernel, by decide +kernel⟩

def f2621 : Formula := .mul f2620 f2221
def num2621 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x14000000000000000000000000000c0000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0xb00000000000000000000000000060000000000000000000000000000, 1⟩,
  ⟨3, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2621 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2621 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2621 : Fraction := ⟨num2621, den2621⟩
theorem h2621 : Reduced f2621 p2621 := .mul h2620 h2221 ⟨cancel2621, by decide +kernel, by decide +kernel⟩

def f2622 : Formula := .mul f2088 f2211
def num2622 : Expr := .bands [
  ⟨2, 0, 1, 0x8, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def den2622 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2622 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2622 : Fraction := ⟨num2622, den2622⟩
theorem h2622 : Reduced f2622 p2622 := .mul h2088 h2211 ⟨cancel2622, by decide +kernel, by decide +kernel⟩

def f2623 : Formula := .div f2621 f2622
def num2623 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2623 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2623 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2623 : Fraction := ⟨num2623, den2623⟩
theorem h2623 : Reduced f2623 p2623 := .div h2621 h2622 [.integer (2), .radius, .radius, .horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2623, by decide +kernel, by decide +kernel⟩

def f2624 : Formula := .neg f2623
def p2624 : Fraction := p2623.neg
theorem h2624 : Reduced f2624 p2624 := .neg h2623

def f2625 : Formula := .add f2614 f2624
def num2625 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2625 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2625 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def p2625 : Fraction := ⟨num2625, den2625⟩
theorem h2625 : Reduced f2625 p2625 := .add h2614 h2624 ⟨cancel2625, by decide +kernel, by decide +kernel⟩

def f2626 : Formula := .mul f3 f16
def num2626 : Expr := .bands [
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2626 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2626 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2626 : Fraction := ⟨num2626, den2626⟩
theorem h2626 : Reduced f2626 p2626 := .mul h3 h16 ⟨cancel2626, by decide +kernel, by decide +kernel⟩

def f2627 : Formula := .neg f1170
def p2627 : Fraction := p1170.neg
theorem h2627 : Reduced f2627 p2627 := .neg h1170

def f2628 : Formula := .add f2626 f2627
def num2628 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2628 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2628 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2628 : Fraction := ⟨num2628, den2628⟩
theorem h2628 : Reduced f2628 p2628 := .add h2626 h2627 ⟨cancel2628, by decide +kernel, by decide +kernel⟩

def f2629 : Formula := .add f2628 f8
def num2629 : Expr := .bands [
  ⟨0, 0, 2, 0x1, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2629 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2629 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2629 : Fraction := ⟨num2629, den2629⟩
theorem h2629 : Reduced f2629 p2629 := .add h2628 h8 ⟨cancel2629, by decide +kernel, by decide +kernel⟩

def f2630 : Formula := .mul f16 f2629
def num2630 : Expr := .bands [
  ⟨0, 0, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2630 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2630 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2630 : Fraction := ⟨num2630, den2630⟩
theorem h2630 : Reduced f2630 p2630 := .mul h16 h2629 ⟨cancel2630, by decide +kernel, by decide +kernel⟩

def f2631 : Formula := .mul f2630 f2167
def num2631 : Expr := .bands [
  ⟨4, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2631 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2631 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2631 : Fraction := ⟨num2631, den2631⟩
theorem h2631 : Reduced f2631 p2631 := .mul h2630 h2167 ⟨cancel2631, by decide +kernel, by decide +kernel⟩

def f2632 : Formula := .mul f0 f2140
def num2632 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def den2632 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2632 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2632 : Fraction := ⟨num2632, den2632⟩
theorem h2632 : Reduced f2632 p2632 := .mul h0 h2140 ⟨cancel2632, by decide +kernel, by decide +kernel⟩

def f2633 : Formula := .div f2631 f2632
def num2633 : Expr := .bands [
  ⟨0, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2633 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2633 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2633 : Fraction := ⟨num2633, den2633⟩
theorem h2633 : Reduced f2633 p2633 := .div h2631 h2632 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2633, by decide +kernel, by decide +kernel⟩

def f2634 : Formula := .add f2625 f2633
def num2634 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2634 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2634 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def p2634 : Fraction := ⟨num2634, den2634⟩
theorem h2634 : Reduced f2634 p2634 := .add h2625 h2633 ⟨cancel2634, by decide +kernel, by decide +kernel⟩

def f2635 : Formula := .mul f1174 f2634
def num2635 : Expr := .bands [
  ⟨0, 0, 5, 0x300000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 7, 0x4000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 0x18000000000000000000000000002c00000000000000000000000000280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x18000000000000000000000000002c00000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x16000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x20000000000000000000000000007000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 5, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x0, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2635 : Expr := .bands [
  ⟨6, 0, 1, 0x20, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x20, 1⟩,
  ⟨8, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2635 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2635 : Fraction := ⟨num2635, den2635⟩
theorem h2635 : Reduced f2635 p2635 := .mul h1174 h2634 ⟨cancel2635, by decide +kernel, by decide +kernel⟩

def f2636 : Formula := .mul f2223 f73
def num2636 : Expr := .bands [
  ⟨4, 2, 1, 0x4, 0x0, 1⟩
]

def den2636 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2636 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2636 : Fraction := ⟨num2636, den2636⟩
theorem h2636 : Reduced f2636 p2636 := .mul h2223 h73 ⟨cancel2636, by decide +kernel, by decide +kernel⟩

def f2637 : Formula := .mul f70 f2138
def num2637 : Expr := .bands [
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2637 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2637 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2637 : Fraction := ⟨num2637, den2637⟩
theorem h2637 : Reduced f2637 p2637 := .mul h70 h2138 ⟨cancel2637, by decide +kernel, by decide +kernel⟩

def f2638 : Formula := .add f2636 f2637
def num2638 : Expr := .bands [
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x4, 0x0, 1⟩
]

def den2638 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2638 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2638 : Fraction := ⟨num2638, den2638⟩
theorem h2638 : Reduced f2638 p2638 := .add h2636 h2637 ⟨cancel2638, by decide +kernel, by decide +kernel⟩

def f2639 : Formula := .mul f2088 f16
def num2639 : Expr := .bands [
  ⟨2, 0, 2, 0x20000000000000000000000000000, 0x0, 1⟩
]

def den2639 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2639 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2639 : Fraction := ⟨num2639, den2639⟩
theorem h2639 : Reduced f2639 p2639 := .mul h2088 h16 ⟨cancel2639, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
