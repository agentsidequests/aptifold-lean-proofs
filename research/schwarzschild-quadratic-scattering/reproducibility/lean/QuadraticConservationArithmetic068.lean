import QuadraticConservationArithmetic067

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2720 : Formula := .mul f2719 f2276
def num2720 : Expr := .bands [
  ⟨1, 2, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2720 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2720 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2720 : Fraction := ⟨num2720, den2720⟩
theorem h2720 : Reduced f2720 p2720 := .mul h2719 h2276 ⟨cancel2720, by decide +kernel, by decide +kernel⟩

def f2721 : Formula := .div f2720 f2601
def num2721 : Expr := .bands [
  ⟨0, 2, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2721 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2721 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2721 : Fraction := ⟨num2721, den2721⟩
theorem h2721 : Reduced f2721 p2721 := .div h2720 h2601 [.integer (2), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2721, by decide +kernel, by decide +kernel⟩

def f2722 : Formula := .mul f2603 f2274
def num2722 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2722 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2722 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2722 : Fraction := ⟨num2722, den2722⟩
theorem h2722 : Reduced f2722 p2722 := .mul h2603 h2274 ⟨cancel2722, by decide +kernel, by decide +kernel⟩

def f2723 : Formula := .mul f2722 f2304
def num2723 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000001400000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x9000000000000000000000000000c000000000000000000000000000900000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x0, 0x300000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2723 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2723 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2723 : Fraction := ⟨num2723, den2723⟩
theorem h2723 : Reduced f2723 p2723 := .mul h2722 h2304 ⟨cancel2723, by decide +kernel, by decide +kernel⟩

def f2724 : Formula := .div f2723 f2526
def num2724 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000001400000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x9000000000000000000000000000c000000000000000000000000000900000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x0, 0x300000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2724 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2724 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2724 : Fraction := ⟨num2724, den2724⟩
theorem h2724 : Reduced f2724 p2724 := .div h2723 h2526 [.integer (4), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2724, by decide +kernel, by decide +kernel⟩

def f2725 : Formula := .add f2721 f2724
def num2725 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000001400000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x9000000000000000000000000000c000000000000000000000000000900000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x10000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2725 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2725 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def p2725 : Fraction := ⟨num2725, den2725⟩
theorem h2725 : Reduced f2725 p2725 := .add h2721 h2724 ⟨cancel2725, by decide +kernel, by decide +kernel⟩

def f2726 : Formula := .mul f2609 f2276
def num2726 : Expr := .bands [
  ⟨2, 1, 3, 0x10000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2726 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2726 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2726 : Fraction := ⟨num2726, den2726⟩
theorem h2726 : Reduced f2726 p2726 := .mul h2609 h2276 ⟨cancel2726, by decide +kernel, by decide +kernel⟩

def f2727 : Formula := .mul f2726 f2291
def num2727 : Expr := .bands [
  ⟨3, 2, 3, 0x30000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2727 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2727 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2727 : Fraction := ⟨num2727, den2727⟩
theorem h2727 : Reduced f2727 p2727 := .mul h2726 h2291 ⟨cancel2727, by decide +kernel, by decide +kernel⟩

def f2728 : Formula := .div f2727 f2199
def num2728 : Expr := .bands [
  ⟨0, 2, 3, 0x30000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2728 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2728 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2728 : Fraction := ⟨num2728, den2728⟩
theorem h2728 : Reduced f2728 p2728 := .div h2727 h2199 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2728, by decide +kernel, by decide +kernel⟩

def f2729 : Formula := .neg f2728
def p2729 : Fraction := p2728.neg
theorem h2729 : Reduced f2729 p2729 := .neg h2728

def f2730 : Formula := .add f2725 f2729
def num2730 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000001400000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x9000000000000000000000000000c000000000000000000000000000900000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2730 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2730 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def p2730 : Fraction := ⟨num2730, den2730⟩
theorem h2730 : Reduced f2730 p2730 := .add h2725 h2729 ⟨cancel2730, by decide +kernel, by decide +kernel⟩

def f2731 : Formula := .mul f2620 f2400
def num2731 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x800000000000000000000000000050000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x700000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2731 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2731 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2731 : Fraction := ⟨num2731, den2731⟩
theorem h2731 : Reduced f2731 p2731 := .mul h2620 h2400 ⟨cancel2731, by decide +kernel, by decide +kernel⟩

def f2732 : Formula := .div f2731 f2622
def num2732 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x800000000000000000000000000050000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x700000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2732 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2732 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2732 : Fraction := ⟨num2732, den2732⟩
theorem h2732 : Reduced f2732 p2732 := .div h2731 h2622 [.integer (2), .radius, .radius, .horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2732, by decide +kernel, by decide +kernel⟩

def f2733 : Formula := .neg f2732
def p2733 : Fraction := p2732.neg
theorem h2733 : Reduced f2733 p2733 := .neg h2732

def f2734 : Formula := .add f2730 f2733
def num2734 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x500000000000000000000000000060000000000000000000000000000, 0x9000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2734 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2734 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2734 : Fraction := ⟨num2734, den2734⟩
theorem h2734 : Reduced f2734 p2734 := .add h2730 h2733 ⟨cancel2734, by decide +kernel, by decide +kernel⟩

def f2735 : Formula := .mul f2630 f2375
def num2735 : Expr := .bands [
  ⟨4, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2735 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2735 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2735 : Fraction := ⟨num2735, den2735⟩
theorem h2735 : Reduced f2735 p2735 := .mul h2630 h2375 ⟨cancel2735, by decide +kernel, by decide +kernel⟩

def f2736 : Formula := .div f2735 f2632
def num2736 : Expr := .bands [
  ⟨0, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2736 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2736 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2736 : Fraction := ⟨num2736, den2736⟩
theorem h2736 : Reduced f2736 p2736 := .div h2735 h2632 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2736, by decide +kernel, by decide +kernel⟩

def f2737 : Formula := .add f2734 f2736
def num2737 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x500000000000000000000000000060000000000000000000000000000, 0x9000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2737 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2737 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def p2737 : Fraction := ⟨num2737, den2737⟩
theorem h2737 : Reduced f2737 p2737 := .add h2734 h2736 ⟨cancel2737, by decide +kernel, by decide +kernel⟩

def f2738 : Formula := .neg f2634
def p2738 : Fraction := p2634.neg
theorem h2738 : Reduced f2738 p2738 := .neg h2634

def f2739 : Formula := .add f2737 f2738
def num2739 : Expr := .bands [
  ⟨0, 0, 3, 0x1200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x40000000000000000000000000000, 0x60000000000000000000000000008000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2739 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2739 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def p2739 : Fraction := ⟨num2739, den2739⟩
theorem h2739 : Reduced f2739 p2739 := .add h2737 h2738 ⟨cancel2739, by decide +kernel, by decide +kernel⟩

def f2740 : Formula := .mul f2598 f2183
def num2740 : Expr := .bands [
  ⟨0, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2740 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2740 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2740 : Fraction := ⟨num2740, den2740⟩
theorem h2740 : Reduced f2740 p2740 := .mul h2598 h2183 ⟨cancel2740, by decide +kernel, by decide +kernel⟩

def f2741 : Formula := .mul f2740 f28
def num2741 : Expr := .bands [

]

def den2741 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2741 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2741 : Fraction := ⟨num2741, den2741⟩
theorem h2741 : Reduced f2741 p2741 := .mul h2740 h28 ⟨cancel2741, by decide +kernel, by decide +kernel⟩

def f2742 : Formula := .div f2741 f2601
def num2742 : Expr := .bands [

]

def den2742 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2742 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2742 : Fraction := ⟨num2742, den2742⟩
theorem h2742 : Reduced f2742 p2742 := .div h2741 h2601 [.integer (2), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2742, by decide +kernel, by decide +kernel⟩

def f2743 : Formula := .mul f2603 f2183
def num2743 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2743 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2743 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2743 : Fraction := ⟨num2743, den2743⟩
theorem h2743 : Reduced f2743 p2743 := .mul h2603 h2183 ⟨cancel2743, by decide +kernel, by decide +kernel⟩

def f2744 : Formula := .mul f2743 f2191
def num2744 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2744 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2744 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2744 : Fraction := ⟨num2744, den2744⟩
theorem h2744 : Reduced f2744 p2744 := .mul h2743 h2191 ⟨cancel2744, by decide +kernel, by decide +kernel⟩

def f2745 : Formula := .div f2744 f2526
def num2745 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2745 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2745 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2745 : Fraction := ⟨num2745, den2745⟩
theorem h2745 : Reduced f2745 p2745 := .div h2744 h2526 [.integer (4), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2745, by decide +kernel, by decide +kernel⟩

def f2746 : Formula := .add f2742 f2745
def num2746 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2746 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2746 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2746 : Fraction := ⟨num2746, den2746⟩
theorem h2746 : Reduced f2746 p2746 := .add h2742 h2745 ⟨cancel2746, by decide +kernel, by decide +kernel⟩

def f2747 : Formula := .mul f2609 f28
def num2747 : Expr := .bands [

]

def den2747 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2747 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2747 : Fraction := ⟨num2747, den2747⟩
theorem h2747 : Reduced f2747 p2747 := .mul h2609 h28 ⟨cancel2747, by decide +kernel, by decide +kernel⟩

def f2748 : Formula := .mul f2747 f2290
def num2748 : Expr := .bands [

]

def den2748 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2748 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2748 : Fraction := ⟨num2748, den2748⟩
theorem h2748 : Reduced f2748 p2748 := .mul h2747 h2290 ⟨cancel2748, by decide +kernel, by decide +kernel⟩

def f2749 : Formula := .div f2748 f2199
def num2749 : Expr := .bands [

]

def den2749 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2749 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def p2749 : Fraction := ⟨num2749, den2749⟩
theorem h2749 : Reduced f2749 p2749 := .div h2748 h2199 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2749, by decide +kernel, by decide +kernel⟩

def f2750 : Formula := .neg f2749
def p2750 : Fraction := p2749.neg
theorem h2750 : Reduced f2750 p2750 := .neg h2749

def f2751 : Formula := .add f2746 f2750
def num2751 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2751 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2751 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2751 : Fraction := ⟨num2751, den2751⟩
theorem h2751 : Reduced f2751 p2751 := .add h2746 h2750 ⟨cancel2751, by decide +kernel, by decide +kernel⟩

def f2752 : Formula := .mul f2620 f2432
def num2752 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2752 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2752 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2752 : Fraction := ⟨num2752, den2752⟩
theorem h2752 : Reduced f2752 p2752 := .mul h2620 h2432 ⟨cancel2752, by decide +kernel, by decide +kernel⟩

def f2753 : Formula := .div f2752 f2622
def num2753 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2753 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2753 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2753 : Fraction := ⟨num2753, den2753⟩
theorem h2753 : Reduced f2753 p2753 := .div h2752 h2622 [.integer (2), .radius, .radius, .horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2753, by decide +kernel, by decide +kernel⟩

def f2754 : Formula := .neg f2753
def p2754 : Fraction := p2753.neg
theorem h2754 : Reduced f2754 p2754 := .neg h2753

def f2755 : Formula := .add f2751 f2754
def num2755 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2755 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2755 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def p2755 : Fraction := ⟨num2755, den2755⟩
theorem h2755 : Reduced f2755 p2755 := .add h2751 h2754 ⟨cancel2755, by decide +kernel, by decide +kernel⟩

def f2756 : Formula := .mul f2630 f2407
def num2756 : Expr := .bands [

]

def den2756 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2756 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2756 : Fraction := ⟨num2756, den2756⟩
theorem h2756 : Reduced f2756 p2756 := .mul h2630 h2407 ⟨cancel2756, by decide +kernel, by decide +kernel⟩

def f2757 : Formula := .div f2756 f2632
def num2757 : Expr := .bands [

]

def den2757 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2757 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p2757 : Fraction := ⟨num2757, den2757⟩
theorem h2757 : Reduced f2757 p2757 := .div h2756 h2632 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2757, by decide +kernel, by decide +kernel⟩

def f2758 : Formula := .add f2755 f2757
def num2758 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2758 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2758 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2758 : Fraction := ⟨num2758, den2758⟩
theorem h2758 : Reduced f2758 p2758 := .add h2755 h2757 ⟨cancel2758, by decide +kernel, by decide +kernel⟩

def f2759 : Formula := .neg f2758
def p2759 : Fraction := p2758.neg
theorem h2759 : Reduced f2759 p2759 := .neg h2758

end SchwarzschildEinstein.PureOdd.Master
