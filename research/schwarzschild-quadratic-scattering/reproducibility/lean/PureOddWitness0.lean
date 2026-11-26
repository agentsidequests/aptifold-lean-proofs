import PureOddProgram

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f0 : Formula := .integer (1)
def p0 : Fraction := .polynomial (.constant (1))
theorem h0 : Reduced f0 p0 := .integer (1)

def f1 : Formula := .integer (2)
def p1 : Fraction := .polynomial (.constant (2))
theorem h1 : Reduced f1 p1 := .integer (2)

def f2 : Formula := .angular
def p2 : Fraction := .polynomial (Expr.angular)
theorem h2 : Reduced f2 p2 := .angular

def f3 : Formula := .mul f1 f2
def num3 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000000, 0x0, 1⟩
]

def den3 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel3 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p3 : Fraction := ⟨num3, den3⟩
theorem h3 : Reduced f3 p3 := .mul h1 h2 ⟨cancel3, by decide +kernel, by decide +kernel⟩

def f4 : Formula := .neg f0
def p4 : Fraction := p0.neg
theorem h4 : Reduced f4 p4 := .neg h0

def f5 : Formula := .add f3 f4
def num5 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000000, 0x1, 1⟩
]

def den5 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel5 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p5 : Fraction := ⟨num5, den5⟩
theorem h5 : Reduced f5 p5 := .add h3 h4 ⟨cancel5, by decide +kernel, by decide +kernel⟩

def f6 : Formula := .add f3 f1
def num6 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000002, 0x0, 1⟩
]

def den6 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel6 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p6 : Fraction := ⟨num6, den6⟩
theorem h6 : Reduced f6 p6 := .add h3 h1 ⟨cancel6, by decide +kernel, by decide +kernel⟩

def f7 : Formula := .mul f5 f6
def num7 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000020000000000000000000000000000, 0x2, 1⟩
]

def den7 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel7 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p7 : Fraction := ⟨num7, den7⟩
theorem h7 : Reduced f7 p7 := .mul h5 h6 ⟨cancel7, by decide +kernel, by decide +kernel⟩

def f8 : Formula := .div f7 f1
def num8 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den8 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel8 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p8 : Fraction := ⟨num8, den8⟩
theorem h8 : Reduced f8 p8 := .div h7 h1 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel8, by decide +kernel, by decide +kernel⟩

def f9 : Formula := .add f8 f0
def num9 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den9 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel9 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p9 : Fraction := ⟨num9, den9⟩
theorem h9 : Reduced f9 p9 := .add h8 h0 ⟨cancel9, by decide +kernel, by decide +kernel⟩

def f10 : Formula := .mul f8 f9
def num10 : Expr := .bands [
  ⟨0, 0, 5, 0x40000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den10 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel10 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p10 : Fraction := ⟨num10, den10⟩
theorem h10 : Reduced f10 p10 := .mul h8 h9 ⟨cancel10, by decide +kernel, by decide +kernel⟩

def f11 : Formula := .integer (3)
def p11 : Fraction := .polynomial (.constant (3))
theorem h11 : Reduced f11 p11 := .integer (3)

def f12 : Formula := .div f10 f11
def num12 : Expr := .bands [
  ⟨0, 0, 5, 0x40000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den12 : Expr := .bands [
  ⟨0, 0, 1, 0x3, 0x0, 1⟩
]

def cancel12 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p12 : Fraction := ⟨num12, den12⟩
theorem h12 : Reduced f12 p12 := .div h10 h11 [.integer (3)] (by decide +kernel) (by decide +kernel) ⟨cancel12, by decide +kernel, by decide +kernel⟩

def f13 : Formula := .frequency
def p13 : Fraction := .polynomial (Expr.frequency)
theorem h13 : Reduced f13 p13 := .frequency

def f14 : Formula := .mul f1 f13
def num14 : Expr := .bands [
  ⟨0, 1, 1, 0x2, 0x0, 1⟩
]

def den14 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel14 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p14 : Fraction := ⟨num14, den14⟩
theorem h14 : Reduced f14 p14 := .mul h1 h13 ⟨cancel14, by decide +kernel, by decide +kernel⟩

def f15 : Formula := .neg f14
def p15 : Fraction := p14.neg
theorem h15 : Reduced f15 p15 := .neg h14

def f16 : Formula := .add f12 f15
def num16 : Expr := .bands [
  ⟨0, 0, 5, 0x40000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨0, 1, 1, 0x0, 0x6, 1⟩
]

def den16 : Expr := .bands [
  ⟨0, 0, 1, 0x3, 0x0, 1⟩
]

def cancel16 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p16 : Fraction := ⟨num16, den16⟩
theorem h16 : Reduced f16 p16 := .add h12 h15 ⟨cancel16, by decide +kernel, by decide +kernel⟩

def f17 : Formula := .div f0 f16
def num17 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x3, 1⟩
]

def den17 : Expr := .bands [
  ⟨0, 0, 5, 0x100000000000000000000000000010000000000000000000000000000, 0x40000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨0, 1, 1, 0x6, 0x0, 1⟩
]

def cancel17 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def p17 : Fraction := ⟨num17, den17⟩
theorem h17 : Reduced f17 p17 := .div h0 h16 [.daughterGap] (by decide +kernel) (by decide +kernel) ⟨cancel17, by decide +kernel, by decide +kernel⟩

def f18 : Formula := .radius
def p18 : Fraction := .polynomial (NumeratorData.x 1)
theorem h18 : Reduced f18 p18 := .radius

def f19 : Formula := .neg f1
def p19 : Fraction := p1.neg
theorem h19 : Reduced f19 p19 := .neg h1

def f20 : Formula := .add f18 f19
def num20 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den20 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel20 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p20 : Fraction := ⟨num20, den20⟩
theorem h20 : Reduced f20 p20 := .add h18 h19 ⟨cancel20, by decide +kernel, by decide +kernel⟩

def f21 : Formula := .div f20 f18
def num21 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den21 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel21 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p21 : Fraction := ⟨num21, den21⟩
theorem h21 : Reduced f21 p21 := .div h20 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel21, by decide +kernel, by decide +kernel⟩

def f22 : Formula := .mul f11 f21
def num22 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x6, 1⟩,
  ⟨1, 0, 1, 0x3, 0x0, 1⟩
]

def den22 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel22 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p22 : Fraction := ⟨num22, den22⟩
theorem h22 : Reduced f22 p22 := .mul h11 h21 ⟨cancel22, by decide +kernel, by decide +kernel⟩

def f23 : Formula := .mul f8 f18
def num23 : Expr := .bands [
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den23 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel23 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p23 : Fraction := ⟨num23, den23⟩
theorem h23 : Reduced f23 p23 := .mul h8 h18 ⟨cancel23, by decide +kernel, by decide +kernel⟩

def f24 : Formula := .add f23 f11
def num24 : Expr := .bands [
  ⟨0, 0, 1, 0x3, 0x0, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den24 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel24 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p24 : Fraction := ⟨num24, den24⟩
theorem h24 : Reduced f24 p24 := .add h23 h11 ⟨cancel24, by decide +kernel, by decide +kernel⟩

def f25 : Formula := .mul f18 f24
def num25 : Expr := .bands [
  ⟨1, 0, 1, 0x3, 0x0, 1⟩,
  ⟨2, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den25 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel25 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p25 : Fraction := ⟨num25, den25⟩
theorem h25 : Reduced f25 p25 := .mul h18 h24 ⟨cancel25, by decide +kernel, by decide +kernel⟩

def f26 : Formula := .div f22 f25
def num26 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x6, 1⟩,
  ⟨1, 0, 1, 0x3, 0x0, 1⟩
]

def den26 : Expr := .bands [
  ⟨2, 0, 1, 0x3, 0x0, 1⟩,
  ⟨3, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def cancel26 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p26 : Fraction := ⟨num26, den26⟩
theorem h26 : Reduced f26 p26 := .div h22 h25 [.radius, .daughterPole] (by decide +kernel) (by decide +kernel) ⟨cancel26, by decide +kernel, by decide +kernel⟩

def f27 : Formula := .add f12 f26
def num27 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x12, 1⟩,
  ⟨1, 0, 1, 0x9, 0x0, 1⟩,
  ⟨2, 0, 5, 0xc000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x8000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000, 0x20000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den27 : Expr := .bands [
  ⟨2, 0, 1, 0x9, 0x0, 1⟩,
  ⟨3, 0, 3, 0x600000000000000000000000000030000000000000000000000000000, 0x3, 1⟩
]

def cancel27 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p27 : Fraction := ⟨num27, den27⟩
theorem h27 : Reduced f27 p27 := .add h12 h26 ⟨cancel27, by decide +kernel, by decide +kernel⟩

def f28 : Formula := .integer (8)
def p28 : Fraction := .polynomial (.constant (8))
theorem h28 : Reduced f28 p28 := .integer (8)

def f29 : Formula := .mul f28 f21
def num29 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def den29 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel29 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p29 : Fraction := ⟨num29, den29⟩
theorem h29 : Reduced f29 p29 := .mul h28 h21 ⟨cancel29, by decide +kernel, by decide +kernel⟩

def f30 : Formula := .integer (6)
def p30 : Fraction := .polynomial (.constant (6))
theorem h30 : Reduced f30 p30 := .integer (6)

def f31 : Formula := .div f30 f18
def num31 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩
]

def den31 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel31 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p31 : Fraction := ⟨num31, den31⟩
theorem h31 : Reduced f31 p31 := .div h30 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel31, by decide +kernel, by decide +kernel⟩

def f32 : Formula := .add f7 f31
def num32 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩,
  ⟨1, 0, 3, 0x400000000000000000000000000020000000000000000000000000000, 0x2, 1⟩
]

def den32 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel32 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p32 : Fraction := ⟨num32, den32⟩
theorem h32 : Reduced f32 p32 := .add h7 h31 ⟨cancel32, by decide +kernel, by decide +kernel⟩

def f33 : Formula := .div f29 f32
def num33 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def den33 : Expr := .bands [
  ⟨0, 0, 1, 0x3, 0x0, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def cancel33 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p33 : Fraction := ⟨num33, den33⟩
theorem h33 : Reduced f33 p33 := .div h29 h32 [.integer (2), .daughterPole] (by decide +kernel) (by decide +kernel) ⟨cancel33, by decide +kernel, by decide +kernel⟩

def f34 : Formula := .add f2 f0
def num34 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000001, 0x0, 1⟩
]

def den34 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel34 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p34 : Fraction := ⟨num34, den34⟩
theorem h34 : Reduced f34 p34 := .add h2 h0 ⟨cancel34, by decide +kernel, by decide +kernel⟩

def f35 : Formula := .mul f2 f34
def num35 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den35 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel35 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p35 : Fraction := ⟨num35, den35⟩
theorem h35 : Reduced f35 p35 := .mul h2 h34 ⟨cancel35, by decide +kernel, by decide +kernel⟩

def f36 : Formula := .mul f35 f13
def num36 : Expr := .bands [
  ⟨0, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den36 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel36 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p36 : Fraction := ⟨num36, den36⟩
theorem h36 : Reduced f36 p36 := .mul h35 h13 ⟨cancel36, by decide +kernel, by decide +kernel⟩

def f37 : Formula := .div f21 f1
def num37 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den37 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel37 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p37 : Fraction := ⟨num37, den37⟩
theorem h37 : Reduced f37 p37 := .div h21 h1 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel37, by decide +kernel, by decide +kernel⟩

def f38 : Formula := .mul f36 f37
def num38 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den38 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel38 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p38 : Fraction := ⟨num38, den38⟩
theorem h38 : Reduced f38 p38 := .mul h36 h37 ⟨cancel38, by decide +kernel, by decide +kernel⟩

def f39 : Formula := .mul f13 f18
def num39 : Expr := .bands [
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den39 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel39 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p39 : Fraction := ⟨num39, den39⟩
theorem h39 : Reduced f39 p39 := .mul h13 h18 ⟨cancel39, by decide +kernel, by decide +kernel⟩

def f40 : Formula := .neg f39
def p40 : Fraction := p39.neg
theorem h40 : Reduced f40 p40 := .neg h39

def f41 : Formula := .mul f1 f21
def num41 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den41 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel41 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p41 : Fraction := ⟨num41, den41⟩
theorem h41 : Reduced f41 p41 := .mul h1 h21 ⟨cancel41, by decide +kernel, by decide +kernel⟩

def f42 : Formula := .div f40 f41
def num42 : Expr := .bands [
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den42 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel42 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p42 : Fraction := ⟨num42, den42⟩
theorem h42 : Reduced f42 p42 := .div h40 h41 [.integer (2), .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel42, by decide +kernel, by decide +kernel⟩

def f43 : Formula := .mul f38 f42
def num43 : Expr := .bands [
  ⟨1, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den43 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel43 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p43 : Fraction := ⟨num43, den43⟩
theorem h43 : Reduced f43 p43 := .mul h38 h42 ⟨cancel43, by decide +kernel, by decide +kernel⟩

def f44 : Formula := .mul f1 f18
def num44 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den44 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel44 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p44 : Fraction := ⟨num44, den44⟩
theorem h44 : Reduced f44 p44 := .mul h1 h18 ⟨cancel44, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
