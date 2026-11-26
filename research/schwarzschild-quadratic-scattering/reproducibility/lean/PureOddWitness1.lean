import PureOddWitness0

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f45 : Formula := .mul f44 f20
def num45 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def den45 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel45 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p45 : Fraction := ⟨num45, den45⟩
theorem h45 : Reduced f45 p45 := .mul h44 h20 ⟨cancel45, by decide +kernel, by decide +kernel⟩

def f46 : Formula := .div f43 f45
def num46 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den46 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def cancel46 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p46 : Fraction := ⟨num46, den46⟩
theorem h46 : Reduced f46 p46 := .div h43 h45 [.integer (2), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel46, by decide +kernel, by decide +kernel⟩

def f47 : Formula := .mul f11 f2
def num47 : Expr := .bands [
  ⟨0, 0, 2, 0x30000000000000000000000000000, 0x0, 1⟩
]

def den47 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel47 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p47 : Fraction := ⟨num47, den47⟩
theorem h47 : Reduced f47 p47 := .mul h11 h2 ⟨cancel47, by decide +kernel, by decide +kernel⟩

def f48 : Formula := .add f47 f0
def num48 : Expr := .bands [
  ⟨0, 0, 2, 0x30000000000000000000000000001, 0x0, 1⟩
]

def den48 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel48 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p48 : Fraction := ⟨num48, den48⟩
theorem h48 : Reduced f48 p48 := .add h47 h0 ⟨cancel48, by decide +kernel, by decide +kernel⟩

def f49 : Formula := .mul f2 f48
def num49 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den49 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel49 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p49 : Fraction := ⟨num49, den49⟩
theorem h49 : Reduced f49 p49 := .mul h2 h48 ⟨cancel49, by decide +kernel, by decide +kernel⟩

def f50 : Formula := .mul f49 f37
def num50 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den50 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel50 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p50 : Fraction := ⟨num50, den50⟩
theorem h50 : Reduced f50 p50 := .mul h49 h37 ⟨cancel50, by decide +kernel, by decide +kernel⟩

def f51 : Formula := .dr f37
def num51 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den51 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel51 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p51 : Fraction := ⟨num51, den51⟩
theorem h51 : Reduced f51 p51 := .dr h37 ⟨cancel51, by decide +kernel, by decide +kernel⟩

def f52 : Formula := .div f0 f44
def num52 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den52 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel52 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p52 : Fraction := ⟨num52, den52⟩
theorem h52 : Reduced f52 p52 := .div h0 h44 [.integer (2), .radius] (by decide +kernel) (by decide +kernel) ⟨cancel52, by decide +kernel, by decide +kernel⟩

def f53 : Formula := .mul f18 f18
def num53 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den53 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel53 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p53 : Fraction := ⟨num53, den53⟩
theorem h53 : Reduced f53 p53 := .mul h18 h18 ⟨cancel53, by decide +kernel, by decide +kernel⟩

def f54 : Formula := .mul f13 f13
def num54 : Expr := .bands [
  ⟨0, 2, 1, 0x1, 0x0, 1⟩
]

def den54 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel54 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p54 : Fraction := ⟨num54, den54⟩
theorem h54 : Reduced f54 p54 := .mul h13 h13 ⟨cancel54, by decide +kernel, by decide +kernel⟩

def f55 : Formula := .div f35 f53
def num55 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den55 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel55 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p55 : Fraction := ⟨num55, den55⟩
theorem h55 : Reduced f55 p55 := .div h35 h53 [.radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel55, by decide +kernel, by decide +kernel⟩

def f56 : Formula := .mul f53 f18
def num56 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def den56 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel56 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p56 : Fraction := ⟨num56, den56⟩
theorem h56 : Reduced f56 p56 := .mul h53 h18 ⟨cancel56, by decide +kernel, by decide +kernel⟩

def f57 : Formula := .div f30 f56
def num57 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩
]

def den57 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel57 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p57 : Fraction := ⟨num57, den57⟩
theorem h57 : Reduced f57 p57 := .div h30 h56 [.radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel57, by decide +kernel, by decide +kernel⟩

def f58 : Formula := .neg f57
def p58 : Fraction := p57.neg
theorem h58 : Reduced f58 p58 := .neg h57

def f59 : Formula := .add f55 f58
def num59 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x6, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den59 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel59 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p59 : Fraction := ⟨num59, den59⟩
theorem h59 : Reduced f59 p59 := .add h55 h58 ⟨cancel59, by decide +kernel, by decide +kernel⟩

def f60 : Formula := .mul f21 f59
def num60 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den60 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel60 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p60 : Fraction := ⟨num60, den60⟩
theorem h60 : Reduced f60 p60 := .mul h21 h59 ⟨cancel60, by decide +kernel, by decide +kernel⟩

def f61 : Formula := .add f54 f60
def num61 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den61 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel61 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p61 : Fraction := ⟨num61, den61⟩
theorem h61 : Reduced f61 p61 := .add h54 h60 ⟨cancel61, by decide +kernel, by decide +kernel⟩

def f62 : Formula := .mul f53 f61
def num62 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den62 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel62 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p62 : Fraction := ⟨num62, den62⟩
theorem h62 : Reduced f62 p62 := .mul h53 h61 ⟨cancel62, by decide +kernel, by decide +kernel⟩

def f63 : Formula := .div f62 f21
def num63 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den63 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel63 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p63 : Fraction := ⟨num63, den63⟩
theorem h63 : Reduced f63 p63 := .div h62 h21 [.horizon] (by decide +kernel) (by decide +kernel) ⟨cancel63, by decide +kernel, by decide +kernel⟩

def f64 : Formula := .mul f52 f63
def num64 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den64 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel64 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p64 : Fraction := ⟨num64, den64⟩
theorem h64 : Reduced f64 p64 := .mul h52 h63 ⟨cancel64, by decide +kernel, by decide +kernel⟩

def f65 : Formula := .add f51 f64
def num65 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den65 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel65 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p65 : Fraction := ⟨num65, den65⟩
theorem h65 : Reduced f65 p65 := .add h51 h64 ⟨cancel65, by decide +kernel, by decide +kernel⟩

def f66 : Formula := .mul f50 f65
def num66 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x60000000000000000000000000008000000000000000000000000000e00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den66 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel66 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p66 : Fraction := ⟨num66, den66⟩
theorem h66 : Reduced f66 p66 := .mul h50 h65 ⟨cancel66, by decide +kernel, by decide +kernel⟩

def f67 : Formula := .integer (4)
def p67 : Fraction := .polynomial (.constant (4))
theorem h67 : Reduced f67 p67 := .integer (4)

def f68 : Formula := .mul f67 f18
def num68 : Expr := .bands [
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def den68 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel68 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p68 : Fraction := ⟨num68, den68⟩
theorem h68 : Reduced f68 p68 := .mul h67 h18 ⟨cancel68, by decide +kernel, by decide +kernel⟩

def f69 : Formula := .mul f68 f20
def num69 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def den69 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel69 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p69 : Fraction := ⟨num69, den69⟩
theorem h69 : Reduced f69 p69 := .mul h68 h20 ⟨cancel69, by decide +kernel, by decide +kernel⟩

def f70 : Formula := .div f66 f69
def num70 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x60000000000000000000000000008000000000000000000000000000e00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den70 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel70 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p70 : Fraction := ⟨num70, den70⟩
theorem h70 : Reduced f70 p70 := .div h66 h69 [.integer (4), .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel70, by decide +kernel, by decide +kernel⟩

def f71 : Formula := .add f46 f70
def num71 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x60000000000000000000000000008000000000000000000000000000e00000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den71 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel71 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def p71 : Fraction := ⟨num71, den71⟩
theorem h71 : Reduced f71 p71 := .add h46 h70 ⟨cancel71, by decide +kernel, by decide +kernel⟩

def f72 : Formula := .add f2 f4
def num72 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x1, 1⟩
]

def den72 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel72 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p72 : Fraction := ⟨num72, den72⟩
theorem h72 : Reduced f72 p72 := .add h2 h4 ⟨cancel72, by decide +kernel, by decide +kernel⟩

def f73 : Formula := .mul f2 f72
def num73 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den73 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel73 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p73 : Fraction := ⟨num73, den73⟩
theorem h73 : Reduced f73 p73 := .mul h2 h72 ⟨cancel73, by decide +kernel, by decide +kernel⟩

def f74 : Formula := .mul f73 f20
def num74 : Expr := .bands [
  ⟨0, 0, 3, 0x20000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den74 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel74 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p74 : Fraction := ⟨num74, den74⟩
theorem h74 : Reduced f74 p74 := .mul h73 h20 ⟨cancel74, by decide +kernel, by decide +kernel⟩

def f75 : Formula := .mul f74 f42
def num75 : Expr := .bands [
  ⟨2, 1, 3, 0x10000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den75 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel75 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p75 : Fraction := ⟨num75, den75⟩
theorem h75 : Reduced f75 p75 := .mul h74 h42 ⟨cancel75, by decide +kernel, by decide +kernel⟩

def f76 : Formula := .dr f42
def num76 : Expr := .bands [
  ⟨1, 1, 1, 0x4, 0x0, 1⟩,
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den76 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel76 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p76 : Fraction := ⟨num76, den76⟩
theorem h76 : Reduced f76 p76 := .dr h42 ⟨cancel76, by decide +kernel, by decide +kernel⟩

def f77 : Formula := .integer (0)
def p77 : Fraction := .polynomial (.constant (0))
theorem h77 : Reduced f77 p77 := .integer (0)

def f78 : Formula := .mul f77 f63
def num78 : Expr := .bands [

]

def den78 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel78 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p78 : Fraction := ⟨num78, den78⟩
theorem h78 : Reduced f78 p78 := .mul h77 h63 ⟨cancel78, by decide +kernel, by decide +kernel⟩

def f79 : Formula := .add f76 f78
def num79 : Expr := .bands [
  ⟨1, 1, 1, 0x4, 0x0, 1⟩,
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den79 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel79 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p79 : Fraction := ⟨num79, den79⟩
theorem h79 : Reduced f79 p79 := .add h76 h78 ⟨cancel79, by decide +kernel, by decide +kernel⟩

def f80 : Formula := .mul f75 f79
def num80 : Expr := .bands [
  ⟨3, 2, 3, 0x40000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den80 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel80 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p80 : Fraction := ⟨num80, den80⟩
theorem h80 : Reduced f80 p80 := .mul h75 h79 ⟨cancel80, by decide +kernel, by decide +kernel⟩

def f81 : Formula := .mul f67 f56
def num81 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def den81 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel81 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p81 : Fraction := ⟨num81, den81⟩
theorem h81 : Reduced f81 p81 := .mul h67 h56 ⟨cancel81, by decide +kernel, by decide +kernel⟩

def f82 : Formula := .div f80 f81
def num82 : Expr := .bands [
  ⟨0, 2, 3, 0x40000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den82 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel82 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p82 : Fraction := ⟨num82, den82⟩
theorem h82 : Reduced f82 p82 := .div h80 h81 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel82, by decide +kernel, by decide +kernel⟩

def f83 : Formula := .neg f82
def p83 : Fraction := p82.neg
theorem h83 : Reduced f83 p83 := .neg h82

def f84 : Formula := .add f71 f83
def num84 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x3000000000000000000000000000100000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000003400000000000000000000000000100000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0xc0000000000000000000000000010000000000000000000000000001000000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den84 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel84 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x10, 0x0, 1⟩
]

def p84 : Fraction := ⟨num84, den84⟩
theorem h84 : Reduced f84 p84 := .add h71 h83 ⟨cancel84, by decide +kernel, by decide +kernel⟩

def f85 : Formula := .mul f44 f2
def num85 : Expr := .bands [
  ⟨1, 0, 2, 0x20000000000000000000000000000, 0x0, 1⟩
]

def den85 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel85 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p85 : Fraction := ⟨num85, den85⟩
theorem h85 : Reduced f85 p85 := .mul h44 h2 ⟨cancel85, by decide +kernel, by decide +kernel⟩

def f86 : Formula := .add f85 f18
def num86 : Expr := .bands [
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den86 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel86 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p86 : Fraction := ⟨num86, den86⟩
theorem h86 : Reduced f86 p86 := .add h85 h18 ⟨cancel86, by decide +kernel, by decide +kernel⟩

def f87 : Formula := .neg f47
def p87 : Fraction := p47.neg
theorem h87 : Reduced f87 p87 := .neg h47

def f88 : Formula := .add f86 f87
def num88 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x30000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den88 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel88 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p88 : Fraction := ⟨num88, den88⟩
theorem h88 : Reduced f88 p88 := .add h86 h87 ⟨cancel88, by decide +kernel, by decide +kernel⟩

def f89 : Formula := .add f88 f19
def num89 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x30000000000000000000000000002, 1⟩,
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den89 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel89 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p89 : Fraction := ⟨num89, den89⟩
theorem h89 : Reduced f89 p89 := .add h88 h19 ⟨cancel89, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
