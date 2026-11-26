import MetricWitness000

namespace SchwarzschildMixtures.MetricWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f40 : Formula := .mul f37 f39
def num40 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x1, 1⟩
]

def den40 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel40 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p40 : Fraction := ⟨num40, den40⟩
theorem h40 : Reduced f40 p40 := .mul h37 h39 ⟨cancel40, by decide +kernel, by decide +kernel⟩

def f41 : Formula := .mul f40 f0
def num41 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x1, 1⟩
]

def den41 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel41 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p41 : Fraction := ⟨num41, den41⟩
theorem h41 : Reduced f41 p41 := .mul h40 h0 ⟨cancel41, by decide +kernel, by decide +kernel⟩

def f42 : Formula := .mul f0 f2
def num42 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den42 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel42 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p42 : Fraction := ⟨num42, den42⟩
theorem h42 : Reduced f42 p42 := .mul h0 h2 ⟨cancel42, by decide +kernel, by decide +kernel⟩

def f43 : Formula := .mul f41 f42
def num43 : Expr := .bands [
  ⟨2, 0, 2, 0x0, 0x10000000000000000000000000000, 1⟩
]

def den43 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel43 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p43 : Fraction := ⟨num43, den43⟩
theorem h43 : Reduced f43 p43 := .mul h41 h42 ⟨cancel43, by decide +kernel, by decide +kernel⟩

def f44 : Formula := .integer (0)
def p44 : Fraction := .polynomial (.constant (0))
theorem h44 : Reduced f44 p44 := .integer (0)

def f45 : Formula := .add f43 f44
def num45 : Expr := .bands [
  ⟨2, 0, 2, 0x0, 0x10000000000000000000000000000, 1⟩
]

def den45 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel45 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p45 : Fraction := ⟨num45, den45⟩
theorem h45 : Reduced f45 p45 := .add h43 h44 ⟨cancel45, by decide +kernel, by decide +kernel⟩

def f46 : Formula := .mul f45 f0
def num46 : Expr := .bands [
  ⟨2, 0, 2, 0x0, 0x10000000000000000000000000000, 1⟩
]

def den46 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel46 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p46 : Fraction := ⟨num46, den46⟩
theorem h46 : Reduced f46 p46 := .mul h45 h0 ⟨cancel46, by decide +kernel, by decide +kernel⟩

def f47 : Formula := .div f0 f20
def num47 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den47 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel47 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p47 : Fraction := ⟨num47, den47⟩
theorem h47 : Reduced f47 p47 := .div h0 h20 [.horizon] (by decide +kernel) (by decide +kernel) ⟨cancel47, by decide +kernel, by decide +kernel⟩

def f48 : Formula := .mul f0 f47
def num48 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den48 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel48 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p48 : Fraction := ⟨num48, den48⟩
theorem h48 : Reduced f48 p48 := .mul h0 h47 ⟨cancel48, by decide +kernel, by decide +kernel⟩

def f49 : Formula := .mul f48 f47
def num49 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den49 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel49 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p49 : Fraction := ⟨num49, den49⟩
theorem h49 : Reduced f49 p49 := .mul h48 h47 ⟨cancel49, by decide +kernel, by decide +kernel⟩

def f50 : Formula := .mul f49 f47
def num50 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den50 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0xc, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x6, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel50 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p50 : Fraction := ⟨num50, den50⟩
theorem h50 : Reduced f50 p50 := .mul h49 h47 ⟨cancel50, by decide +kernel, by decide +kernel⟩

def f51 : Formula := .mul f46 f50
def num51 : Expr := .bands [
  ⟨2, 0, 2, 0x0, 0x10000000000000000000000000000, 1⟩
]

def den51 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x18, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0xc, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel51 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p51 : Fraction := ⟨num51, den51⟩
theorem h51 : Reduced f51 p51 := .mul h46 h50 ⟨cancel51, by decide +kernel, by decide +kernel⟩

def f52 : Formula := .mul f21 f21
def num52 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den52 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel52 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p52 : Fraction := ⟨num52, den52⟩
theorem h52 : Reduced f52 p52 := .mul h21 h21 ⟨cancel52, by decide +kernel, by decide +kernel⟩

def f53 : Formula := .div f0 f52
def num53 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den53 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel53 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p53 : Fraction := ⟨num53, den53⟩
theorem h53 : Reduced f53 p53 := .div h0 h52 [.horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel53, by decide +kernel, by decide +kernel⟩

def f54 : Formula := .add f2 f0
def num54 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000001, 0x0, 1⟩
]

def den54 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel54 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p54 : Fraction := ⟨num54, den54⟩
theorem h54 : Reduced f54 p54 := .add h2 h0 ⟨cancel54, by decide +kernel, by decide +kernel⟩

def f55 : Formula := .mul f2 f54
def num55 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den55 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel55 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p55 : Fraction := ⟨num55, den55⟩
theorem h55 : Reduced f55 p55 := .mul h2 h54 ⟨cancel55, by decide +kernel, by decide +kernel⟩

def f56 : Formula := .add f2 f4
def num56 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x1, 1⟩
]

def den56 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel56 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p56 : Fraction := ⟨num56, den56⟩
theorem h56 : Reduced f56 p56 := .add h2 h4 ⟨cancel56, by decide +kernel, by decide +kernel⟩

def f57 : Formula := .add f2 f1
def num57 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000002, 0x0, 1⟩
]

def den57 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel57 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p57 : Fraction := ⟨num57, den57⟩
theorem h57 : Reduced f57 p57 := .add h2 h1 ⟨cancel57, by decide +kernel, by decide +kernel⟩

def f58 : Formula := .mul f56 f57
def num58 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den58 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel58 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p58 : Fraction := ⟨num58, den58⟩
theorem h58 : Reduced f58 p58 := .mul h56 h57 ⟨cancel58, by decide +kernel, by decide +kernel⟩

def f59 : Formula := .add f58 f31
def num59 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den59 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel59 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p59 : Fraction := ⟨num59, den59⟩
theorem h59 : Reduced f59 p59 := .add h58 h31 ⟨cancel59, by decide +kernel, by decide +kernel⟩

def f60 : Formula := .mul f55 f59
def num60 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den60 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel60 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p60 : Fraction := ⟨num60, den60⟩
theorem h60 : Reduced f60 p60 := .mul h55 h59 ⟨cancel60, by decide +kernel, by decide +kernel⟩

def f61 : Formula := .integer (4)
def p61 : Fraction := .polynomial (.constant (4))
theorem h61 : Reduced f61 p61 := .integer (4)

def f62 : Formula := .mul f61 f18
def num62 : Expr := .bands [
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def den62 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel62 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p62 : Fraction := ⟨num62, den62⟩
theorem h62 : Reduced f62 p62 := .mul h61 h18 ⟨cancel62, by decide +kernel, by decide +kernel⟩

def f63 : Formula := .div f60 f62
def num63 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den63 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel63 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p63 : Fraction := ⟨num63, den63⟩
theorem h63 : Reduced f63 p63 := .div h60 h62 [.integer (4), .radius] (by decide +kernel) (by decide +kernel) ⟨cancel63, by decide +kernel, by decide +kernel⟩

def f64 : Formula := .div f58 f1
def num64 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den64 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel64 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p64 : Fraction := ⟨num64, den64⟩
theorem h64 : Reduced f64 p64 := .div h58 h1 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel64, by decide +kernel, by decide +kernel⟩

def f65 : Formula := .add f64 f0
def num65 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den65 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel65 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p65 : Fraction := ⟨num65, den65⟩
theorem h65 : Reduced f65 p65 := .add h64 h0 ⟨cancel65, by decide +kernel, by decide +kernel⟩

def f66 : Formula := .mul f64 f65
def num66 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den66 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel66 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p66 : Fraction := ⟨num66, den66⟩
theorem h66 : Reduced f66 p66 := .mul h64 h65 ⟨cancel66, by decide +kernel, by decide +kernel⟩

def f67 : Formula := .div f66 f11
def num67 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den67 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def cancel67 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p67 : Fraction := ⟨num67, den67⟩
theorem h67 : Reduced f67 p67 := .div h66 h11 [.integer (3)] (by decide +kernel) (by decide +kernel) ⟨cancel67, by decide +kernel, by decide +kernel⟩

def f68 : Formula := .mul f64 f18
def num68 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den68 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel68 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p68 : Fraction := ⟨num68, den68⟩
theorem h68 : Reduced f68 p68 := .mul h64 h18 ⟨cancel68, by decide +kernel, by decide +kernel⟩

def f69 : Formula := .add f68 f11
def num69 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den69 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel69 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p69 : Fraction := ⟨num69, den69⟩
theorem h69 : Reduced f69 p69 := .add h68 h11 ⟨cancel69, by decide +kernel, by decide +kernel⟩

def f70 : Formula := .mul f18 f69
def num70 : Expr := .bands [
  ⟨1, 0, 1, 0x6, 0x0, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den70 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel70 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p70 : Fraction := ⟨num70, den70⟩
theorem h70 : Reduced f70 p70 := .mul h18 h69 ⟨cancel70, by decide +kernel, by decide +kernel⟩

def f71 : Formula := .div f22 f70
def num71 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0xc, 1⟩,
  ⟨1, 0, 1, 0x6, 0x0, 1⟩
]

def den71 : Expr := .bands [
  ⟨2, 0, 1, 0x6, 0x0, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def cancel71 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p71 : Fraction := ⟨num71, den71⟩
theorem h71 : Reduced f71 p71 := .div h22 h70 [.radius, .parentPole] (by decide +kernel) (by decide +kernel) ⟨cancel71, by decide +kernel, by decide +kernel⟩

def f72 : Formula := .add f67 f71
def num72 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x90, 1⟩,
  ⟨1, 0, 1, 0x48, 0x0, 1⟩,
  ⟨2, 0, 5, 0x6000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000c0000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 0x10000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den72 : Expr := .bands [
  ⟨2, 0, 1, 0x48, 0x0, 1⟩,
  ⟨3, 0, 3, 0xc000000000000000000000000000c0000000000000000000000000000, 0x18, 1⟩
]

def cancel72 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p72 : Fraction := ⟨num72, den72⟩
theorem h72 : Reduced f72 p72 := .add h67 h71 ⟨cancel72, by decide +kernel, by decide +kernel⟩

def f73 : Formula := .add f67 f13
def num73 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨0, 1, 1, 0xc, 0x0, 1⟩
]

def den73 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def cancel73 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p73 : Fraction := ⟨num73, den73⟩
theorem h73 : Reduced f73 p73 := .add h67 h13 ⟨cancel73, by decide +kernel, by decide +kernel⟩

def f74 : Formula := .div f72 f73
def num74 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x90, 1⟩,
  ⟨1, 0, 1, 0x48, 0x0, 1⟩,
  ⟨2, 0, 5, 0x6000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000c0000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 0x10000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den74 : Expr := .bands [
  ⟨2, 0, 5, 0x6000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000c0000000000000000000000000000, 1⟩,
  ⟨2, 1, 1, 0x48, 0x0, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 0x10000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 1, 3, 0xc000000000000000000000000000c0000000000000000000000000000, 0x18, 1⟩
]

def cancel74 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩
]

def p74 : Fraction := ⟨num74, den74⟩
theorem h74 : Reduced f74 p74 := .div h72 h73 [.parentGap] (by decide +kernel) (by decide +kernel) ⟨cancel74, by decide +kernel, by decide +kernel⟩

def f75 : Formula := .mul f63 f74
def num75 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x9000000000000000000000000000900000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x4800000000000000000000000000480000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 7, 0x6000000000000000000000000001200000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x12000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 9, 0x100000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x800000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den75 : Expr := .bands [
  ⟨4, 0, 5, 0x40000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 1, 1, 0x30, 0x0, 1⟩
]

def cancel75 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def p75 : Fraction := ⟨num75, den75⟩
theorem h75 : Reduced f75 p75 := .mul h63 h74 ⟨cancel75, by decide +kernel, by decide +kernel⟩

def f76 : Formula := .div f59 f1
def num76 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x2, 1⟩
]

def den76 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel76 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p76 : Fraction := ⟨num76, den76⟩
theorem h76 : Reduced f76 p76 := .div h59 h1 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel76, by decide +kernel, by decide +kernel⟩

def f77 : Formula := .neg f76
def p77 : Fraction := p76.neg
theorem h77 : Reduced f77 p77 := .neg h76

def f78 : Formula := .dr f74
def num78 : Expr := .bands [
  ⟨0, 0, 1, 0x6c0, 0x0, 1⟩,
  ⟨1, 0, 3, 0x1b000000000000000000000000001b00000000000000000000000000000, 0x510, 1⟩,
  ⟨2, 0, 3, 0x120, 0x9000000000000000000000000000900000000000000000000000000000, 1⟩
]

def den78 : Expr := .bands [
  ⟨3, 0, 5, 0x240000000000000000000000000048000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2400000000000000000000000000480000000000000000000000000000, 1⟩,
  ⟨3, 1, 1, 0x1b0, 0x0, 1⟩,
  ⟨4, 0, 7, 0xc000000000000000000000000002400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000, 0xc0000000000000000000000000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 1, 3, 0x9000000000000000000000000000900000000000000000000000000000, 0x120, 1⟩,
  ⟨5, 0, 9, 0x100000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0xe00000000000000000000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨5, 1, 5, 0xc0000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000030, 0x2400000000000000000000000000300000000000000000000000000000, 1⟩
]

def cancel78 : Expr := .bands [
  ⟨1, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 1, 1, 0xc, 0x0, 1⟩
]

def p78 : Fraction := ⟨num78, den78⟩
theorem h78 : Reduced f78 p78 := .dr h74 ⟨cancel78, by decide +kernel, by decide +kernel⟩

def f79 : Formula := .mul f18 f18
def num79 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den79 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel79 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p79 : Fraction := ⟨num79, den79⟩
theorem h79 : Reduced f79 p79 := .mul h18 h18 ⟨cancel79, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.MetricWitness
