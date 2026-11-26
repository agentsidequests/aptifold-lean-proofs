import QuadraticConservationArithmetic000

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f40 : Formula := .mul f6 f6
def num40 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den40 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel40 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p40 : Fraction := ⟨num40, den40⟩
theorem h40 : Reduced f40 p40 := .mul h6 h6 ⟨cancel40, by decide +kernel, by decide +kernel⟩

def f41 : Formula := .div f8 f40
def num41 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den41 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel41 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p41 : Fraction := ⟨num41, den41⟩
theorem h41 : Reduced f41 p41 := .div h8 h40 [.horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel41, by decide +kernel, by decide +kernel⟩

def f42 : Formula := .add f16 f8
def num42 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000001, 0x0, 1⟩
]

def den42 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel42 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p42 : Fraction := ⟨num42, den42⟩
theorem h42 : Reduced f42 p42 := .add h16 h8 ⟨cancel42, by decide +kernel, by decide +kernel⟩

def f43 : Formula := .mul f16 f42
def num43 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den43 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel43 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p43 : Fraction := ⟨num43, den43⟩
theorem h43 : Reduced f43 p43 := .mul h16 h42 ⟨cancel43, by decide +kernel, by decide +kernel⟩

def f44 : Formula := .add f16 f9
def num44 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x1, 1⟩
]

def den44 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel44 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p44 : Fraction := ⟨num44, den44⟩
theorem h44 : Reduced f44 p44 := .add h16 h9 ⟨cancel44, by decide +kernel, by decide +kernel⟩

def f45 : Formula := .add f16 f0
def num45 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000002, 0x0, 1⟩
]

def den45 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel45 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p45 : Fraction := ⟨num45, den45⟩
theorem h45 : Reduced f45 p45 := .add h16 h0 ⟨cancel45, by decide +kernel, by decide +kernel⟩

def f46 : Formula := .mul f44 f45
def num46 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den46 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel46 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p46 : Fraction := ⟨num46, den46⟩
theorem h46 : Reduced f46 p46 := .mul h44 h45 ⟨cancel46, by decide +kernel, by decide +kernel⟩

def f47 : Formula := .integer (6)
def p47 : Fraction := .polynomial (.constant (6))
theorem h47 : Reduced f47 p47 := .integer (6)

def f48 : Formula := .div f47 f3
def num48 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩
]

def den48 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel48 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p48 : Fraction := ⟨num48, den48⟩
theorem h48 : Reduced f48 p48 := .div h47 h3 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel48, by decide +kernel, by decide +kernel⟩

def f49 : Formula := .add f46 f48
def num49 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den49 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel49 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p49 : Fraction := ⟨num49, den49⟩
theorem h49 : Reduced f49 p49 := .add h46 h48 ⟨cancel49, by decide +kernel, by decide +kernel⟩

def f50 : Formula := .mul f43 f49
def num50 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den50 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel50 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p50 : Fraction := ⟨num50, den50⟩
theorem h50 : Reduced f50 p50 := .mul h43 h49 ⟨cancel50, by decide +kernel, by decide +kernel⟩

def f51 : Formula := .mul f10 f3
def num51 : Expr := .bands [
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def den51 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel51 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p51 : Fraction := ⟨num51, den51⟩
theorem h51 : Reduced f51 p51 := .mul h10 h3 ⟨cancel51, by decide +kernel, by decide +kernel⟩

def f52 : Formula := .div f50 f51
def num52 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den52 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel52 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p52 : Fraction := ⟨num52, den52⟩
theorem h52 : Reduced f52 p52 := .div h50 h51 [.integer (4), .radius] (by decide +kernel) (by decide +kernel) ⟨cancel52, by decide +kernel, by decide +kernel⟩

def f53 : Formula := .div f46 f0
def num53 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den53 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel53 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p53 : Fraction := ⟨num53, den53⟩
theorem h53 : Reduced f53 p53 := .div h46 h0 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel53, by decide +kernel, by decide +kernel⟩

def f54 : Formula := .add f53 f8
def num54 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den54 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel54 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p54 : Fraction := ⟨num54, den54⟩
theorem h54 : Reduced f54 p54 := .add h53 h8 ⟨cancel54, by decide +kernel, by decide +kernel⟩

def f55 : Formula := .mul f53 f54
def num55 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den55 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel55 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p55 : Fraction := ⟨num55, den55⟩
theorem h55 : Reduced f55 p55 := .mul h53 h54 ⟨cancel55, by decide +kernel, by decide +kernel⟩

def f56 : Formula := .integer (3)
def p56 : Fraction := .polynomial (.constant (3))
theorem h56 : Reduced f56 p56 := .integer (3)

def f57 : Formula := .div f55 f56
def num57 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den57 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def cancel57 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p57 : Fraction := ⟨num57, den57⟩
theorem h57 : Reduced f57 p57 := .div h55 h56 [.integer (3)] (by decide +kernel) (by decide +kernel) ⟨cancel57, by decide +kernel, by decide +kernel⟩

def f58 : Formula := .mul f56 f6
def num58 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x6, 1⟩,
  ⟨1, 0, 1, 0x3, 0x0, 1⟩
]

def den58 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel58 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p58 : Fraction := ⟨num58, den58⟩
theorem h58 : Reduced f58 p58 := .mul h56 h6 ⟨cancel58, by decide +kernel, by decide +kernel⟩

def f59 : Formula := .mul f53 f3
def num59 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den59 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel59 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p59 : Fraction := ⟨num59, den59⟩
theorem h59 : Reduced f59 p59 := .mul h53 h3 ⟨cancel59, by decide +kernel, by decide +kernel⟩

def f60 : Formula := .add f59 f56
def num60 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den60 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel60 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p60 : Fraction := ⟨num60, den60⟩
theorem h60 : Reduced f60 p60 := .add h59 h56 ⟨cancel60, by decide +kernel, by decide +kernel⟩

def f61 : Formula := .mul f3 f60
def num61 : Expr := .bands [
  ⟨1, 0, 1, 0x6, 0x0, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den61 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel61 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p61 : Fraction := ⟨num61, den61⟩
theorem h61 : Reduced f61 p61 := .mul h3 h60 ⟨cancel61, by decide +kernel, by decide +kernel⟩

def f62 : Formula := .div f58 f61
def num62 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0xc, 1⟩,
  ⟨1, 0, 1, 0x6, 0x0, 1⟩
]

def den62 : Expr := .bands [
  ⟨2, 0, 1, 0x6, 0x0, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def cancel62 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p62 : Fraction := ⟨num62, den62⟩
theorem h62 : Reduced f62 p62 := .div h58 h61 [.radius, .parentPole] (by decide +kernel) (by decide +kernel) ⟨cancel62, by decide +kernel, by decide +kernel⟩

def f63 : Formula := .add f57 f62
def num63 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x90, 1⟩,
  ⟨1, 0, 1, 0x48, 0x0, 1⟩,
  ⟨2, 0, 5, 0x6000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000c0000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 0x10000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den63 : Expr := .bands [
  ⟨2, 0, 1, 0x48, 0x0, 1⟩,
  ⟨3, 0, 3, 0xc000000000000000000000000000c0000000000000000000000000000, 0x18, 1⟩
]

def cancel63 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p63 : Fraction := ⟨num63, den63⟩
theorem h63 : Reduced f63 p63 := .add h57 h62 ⟨cancel63, by decide +kernel, by decide +kernel⟩

def f64 : Formula := .add f57 f1
def num64 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨0, 1, 1, 0xc, 0x0, 1⟩
]

def den64 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def cancel64 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p64 : Fraction := ⟨num64, den64⟩
theorem h64 : Reduced f64 p64 := .add h57 h1 ⟨cancel64, by decide +kernel, by decide +kernel⟩

def f65 : Formula := .div f63 f64
def num65 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x90, 1⟩,
  ⟨1, 0, 1, 0x48, 0x0, 1⟩,
  ⟨2, 0, 5, 0x6000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000c0000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 0x10000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den65 : Expr := .bands [
  ⟨2, 0, 5, 0x6000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000c0000000000000000000000000000, 1⟩,
  ⟨2, 1, 1, 0x48, 0x0, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 0x10000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 1, 3, 0xc000000000000000000000000000c0000000000000000000000000000, 0x18, 1⟩
]

def cancel65 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def p65 : Fraction := ⟨num65, den65⟩
theorem h65 : Reduced f65 p65 := .div h63 h64 [.parentGap] (by decide +kernel) (by decide +kernel) ⟨cancel65, by decide +kernel, by decide +kernel⟩

def f66 : Formula := .mul f52 f65
def num66 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x9000000000000000000000000000900000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x4800000000000000000000000000480000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 7, 0x6000000000000000000000000001200000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x12000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 9, 0x100000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x800000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den66 : Expr := .bands [
  ⟨4, 0, 5, 0x40000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 1, 1, 0x30, 0x0, 1⟩
]

def cancel66 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def p66 : Fraction := ⟨num66, den66⟩
theorem h66 : Reduced f66 p66 := .mul h52 h65 ⟨cancel66, by decide +kernel, by decide +kernel⟩

def f67 : Formula := .div f49 f0
def num67 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den67 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel67 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p67 : Fraction := ⟨num67, den67⟩
theorem h67 : Reduced f67 p67 := .div h49 h0 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel67, by decide +kernel, by decide +kernel⟩

def f68 : Formula := .neg f67
def p68 : Fraction := p67.neg
theorem h68 : Reduced f68 p68 := .neg h67

def f69 : Formula := .dr f65
def num69 : Expr := .bands [
  ⟨0, 0, 1, 0x6c0, 0x0, 1⟩,
  ⟨1, 0, 3, 0x1b000000000000000000000000001b00000000000000000000000000000, 0x510, 1⟩,
  ⟨2, 0, 3, 0x120, 0x9000000000000000000000000000900000000000000000000000000000, 1⟩
]

def den69 : Expr := .bands [
  ⟨3, 0, 5, 0x240000000000000000000000000048000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2400000000000000000000000000480000000000000000000000000000, 1⟩,
  ⟨3, 1, 1, 0x1b0, 0x0, 1⟩,
  ⟨4, 0, 7, 0xc000000000000000000000000002400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000, 0xc0000000000000000000000000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 1, 3, 0x9000000000000000000000000000900000000000000000000000000000, 0x120, 1⟩,
  ⟨5, 0, 9, 0x100000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0xe00000000000000000000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨5, 1, 5, 0xc0000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000030, 0x2400000000000000000000000000300000000000000000000000000000, 1⟩
]

def cancel69 : Expr := .bands [
  ⟨1, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 1, 1, 0xc, 0x0, 1⟩
]

def p69 : Fraction := ⟨num69, den69⟩
theorem h69 : Reduced f69 p69 := .dr h65 ⟨cancel69, by decide +kernel, by decide +kernel⟩

def f70 : Formula := .mul f3 f3
def num70 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den70 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel70 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p70 : Fraction := ⟨num70, den70⟩
theorem h70 : Reduced f70 p70 := .mul h3 h3 ⟨cancel70, by decide +kernel, by decide +kernel⟩

def f71 : Formula := .mul f70 f64
def num71 : Expr := .bands [
  ⟨2, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨2, 1, 1, 0xc, 0x0, 1⟩
]

def den71 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def cancel71 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p71 : Fraction := ⟨num71, den71⟩
theorem h71 : Reduced f71 p71 := .mul h70 h64 ⟨cancel71, by decide +kernel, by decide +kernel⟩

def f72 : Formula := .div f8 f71
def num72 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def den72 : Expr := .bands [
  ⟨2, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨2, 1, 1, 0xc, 0x0, 1⟩
]

def cancel72 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p72 : Fraction := ⟨num72, den72⟩
theorem h72 : Reduced f72 p72 := .div h8 h71 [.radius, .radius, .parentGap] (by decide +kernel) (by decide +kernel) ⟨cancel72, by decide +kernel, by decide +kernel⟩

def f73 : Formula := .mul f1 f1
def num73 : Expr := .bands [
  ⟨0, 2, 1, 0x1, 0x0, 1⟩
]

def den73 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel73 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p73 : Fraction := ⟨num73, den73⟩
theorem h73 : Reduced f73 p73 := .mul h1 h1 ⟨cancel73, by decide +kernel, by decide +kernel⟩

def f74 : Formula := .div f43 f70
def num74 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den74 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel74 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p74 : Fraction := ⟨num74, den74⟩
theorem h74 : Reduced f74 p74 := .div h43 h70 [.radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel74, by decide +kernel, by decide +kernel⟩

def f75 : Formula := .mul f70 f3
def num75 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def den75 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel75 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p75 : Fraction := ⟨num75, den75⟩
theorem h75 : Reduced f75 p75 := .mul h70 h3 ⟨cancel75, by decide +kernel, by decide +kernel⟩

def f76 : Formula := .div f47 f75
def num76 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩
]

def den76 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel76 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p76 : Fraction := ⟨num76, den76⟩
theorem h76 : Reduced f76 p76 := .div h47 h75 [.radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel76, by decide +kernel, by decide +kernel⟩

def f77 : Formula := .neg f76
def p77 : Fraction := p76.neg
theorem h77 : Reduced f77 p77 := .neg h76

def f78 : Formula := .add f74 f77
def num78 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x6, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den78 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel78 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p78 : Fraction := ⟨num78, den78⟩
theorem h78 : Reduced f78 p78 := .add h74 h77 ⟨cancel78, by decide +kernel, by decide +kernel⟩

def f79 : Formula := .mul f6 f78
def num79 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den79 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel79 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p79 : Fraction := ⟨num79, den79⟩
theorem h79 : Reduced f79 p79 := .mul h6 h78 ⟨cancel79, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
