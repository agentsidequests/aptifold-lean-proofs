import MixedConservationRows

namespace SchwarzschildMixtures.MixedConservationWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f0 : Formula := .integer (1)
def p0 : Fraction := .polynomial (.constant (1))
theorem h0 : Reduced f0 p0 := .integer (1)

def f1 : Formula := .integer (8)
def p1 : Fraction := .polynomial (.constant (8))
theorem h1 : Reduced f1 p1 := .integer (8)

def f2 : Formula := .div f0 f1
def num2 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2 : Fraction := ⟨num2, den2⟩
theorem h2 : Reduced f2 p2 := .div h0 h1 [.integer (8)] (by decide +kernel) (by decide +kernel) ⟨cancel2, by decide +kernel, by decide +kernel⟩

def f3 : Formula := .radius
def p3 : Fraction := .polynomial (NumeratorData.x 1)
theorem h3 : Reduced f3 p3 := .radius

def f4 : Formula := .integer (2)
def p4 : Fraction := .polynomial (.constant (2))
theorem h4 : Reduced f4 p4 := .integer (2)

def f5 : Formula := .neg f4
def p5 : Fraction := p4.neg
theorem h5 : Reduced f5 p5 := .neg h4

def f6 : Formula := .add f3 f5
def num6 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den6 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel6 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p6 : Fraction := ⟨num6, den6⟩
theorem h6 : Reduced f6 p6 := .add h3 h5 ⟨cancel6, by decide +kernel, by decide +kernel⟩

def f7 : Formula := .div f6 f3
def num7 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den7 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel7 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p7 : Fraction := ⟨num7, den7⟩
theorem h7 : Reduced f7 p7 := .div h6 h3 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel7, by decide +kernel, by decide +kernel⟩

def f8 : Formula := .div f7 f4
def num8 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den8 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel8 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p8 : Fraction := ⟨num8, den8⟩
theorem h8 : Reduced f8 p8 := .div h7 h4 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel8, by decide +kernel, by decide +kernel⟩

def f9 : Formula := .dr f8
def num9 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den9 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel9 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p9 : Fraction := ⟨num9, den9⟩
theorem h9 : Reduced f9 p9 := .dr h8 ⟨cancel9, by decide +kernel, by decide +kernel⟩

def f10 : Formula := .mul f4 f3
def num10 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den10 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel10 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p10 : Fraction := ⟨num10, den10⟩
theorem h10 : Reduced f10 p10 := .mul h4 h3 ⟨cancel10, by decide +kernel, by decide +kernel⟩

def f11 : Formula := .div f0 f10
def num11 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den11 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel11 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p11 : Fraction := ⟨num11, den11⟩
theorem h11 : Reduced f11 p11 := .div h0 h10 [.integer (2), .radius] (by decide +kernel) (by decide +kernel) ⟨cancel11, by decide +kernel, by decide +kernel⟩

def f12 : Formula := .mul f3 f3
def num12 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den12 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel12 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p12 : Fraction := ⟨num12, den12⟩
theorem h12 : Reduced f12 p12 := .mul h3 h3 ⟨cancel12, by decide +kernel, by decide +kernel⟩

def f13 : Formula := .frequency
def p13 : Fraction := .polynomial (Expr.frequency)
theorem h13 : Reduced f13 p13 := .frequency

def f14 : Formula := .mul f13 f13
def num14 : Expr := .bands [
  ⟨0, 2, 1, 0x1, 0x0, 1⟩
]

def den14 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel14 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p14 : Fraction := ⟨num14, den14⟩
theorem h14 : Reduced f14 p14 := .mul h13 h13 ⟨cancel14, by decide +kernel, by decide +kernel⟩

def f15 : Formula := .angular
def p15 : Fraction := .polynomial (Expr.angular)
theorem h15 : Reduced f15 p15 := .angular

def f16 : Formula := .add f15 f0
def num16 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000001, 0x0, 1⟩
]

def den16 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel16 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p16 : Fraction := ⟨num16, den16⟩
theorem h16 : Reduced f16 p16 := .add h15 h0 ⟨cancel16, by decide +kernel, by decide +kernel⟩

def f17 : Formula := .mul f15 f16
def num17 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den17 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel17 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p17 : Fraction := ⟨num17, den17⟩
theorem h17 : Reduced f17 p17 := .mul h15 h16 ⟨cancel17, by decide +kernel, by decide +kernel⟩

def f18 : Formula := .div f17 f12
def num18 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den18 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel18 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p18 : Fraction := ⟨num18, den18⟩
theorem h18 : Reduced f18 p18 := .div h17 h12 [.radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel18, by decide +kernel, by decide +kernel⟩

def f19 : Formula := .integer (6)
def p19 : Fraction := .polynomial (.constant (6))
theorem h19 : Reduced f19 p19 := .integer (6)

def f20 : Formula := .mul f12 f3
def num20 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def den20 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel20 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p20 : Fraction := ⟨num20, den20⟩
theorem h20 : Reduced f20 p20 := .mul h12 h3 ⟨cancel20, by decide +kernel, by decide +kernel⟩

def f21 : Formula := .div f19 f20
def num21 : Expr := .bands [
  ⟨0, 0, 1, 0x6, 0x0, 1⟩
]

def den21 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel21 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p21 : Fraction := ⟨num21, den21⟩
theorem h21 : Reduced f21 p21 := .div h19 h20 [.radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel21, by decide +kernel, by decide +kernel⟩

def f22 : Formula := .neg f21
def p22 : Fraction := p21.neg
theorem h22 : Reduced f22 p22 := .neg h21

def f23 : Formula := .add f18 f22
def num23 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x6, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den23 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel23 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p23 : Fraction := ⟨num23, den23⟩
theorem h23 : Reduced f23 p23 := .add h18 h22 ⟨cancel23, by decide +kernel, by decide +kernel⟩

def f24 : Formula := .mul f7 f23
def num24 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den24 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel24 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p24 : Fraction := ⟨num24, den24⟩
theorem h24 : Reduced f24 p24 := .mul h7 h23 ⟨cancel24, by decide +kernel, by decide +kernel⟩

def f25 : Formula := .add f14 f24
def num25 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den25 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel25 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p25 : Fraction := ⟨num25, den25⟩
theorem h25 : Reduced f25 p25 := .add h14 h24 ⟨cancel25, by decide +kernel, by decide +kernel⟩

def f26 : Formula := .mul f12 f25
def num26 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den26 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel26 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p26 : Fraction := ⟨num26, den26⟩
theorem h26 : Reduced f26 p26 := .mul h12 h25 ⟨cancel26, by decide +kernel, by decide +kernel⟩

def f27 : Formula := .div f26 f7
def num27 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den27 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel27 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p27 : Fraction := ⟨num27, den27⟩
theorem h27 : Reduced f27 p27 := .div h26 h7 [.horizon] (by decide +kernel) (by decide +kernel) ⟨cancel27, by decide +kernel, by decide +kernel⟩

def f28 : Formula := .mul f11 f27
def num28 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den28 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel28 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p28 : Fraction := ⟨num28, den28⟩
theorem h28 : Reduced f28 p28 := .mul h11 h27 ⟨cancel28, by decide +kernel, by decide +kernel⟩

def f29 : Formula := .add f9 f28
def num29 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den29 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel29 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p29 : Fraction := ⟨num29, den29⟩
theorem h29 : Reduced f29 p29 := .add h9 h28 ⟨cancel29, by decide +kernel, by decide +kernel⟩

def f30 : Formula := .mul f13 f3
def num30 : Expr := .bands [
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den30 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel30 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p30 : Fraction := ⟨num30, den30⟩
theorem h30 : Reduced f30 p30 := .mul h13 h3 ⟨cancel30, by decide +kernel, by decide +kernel⟩

def f31 : Formula := .neg f30
def p31 : Fraction := p30.neg
theorem h31 : Reduced f31 p31 := .neg h30

def f32 : Formula := .mul f4 f7
def num32 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den32 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel32 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p32 : Fraction := ⟨num32, den32⟩
theorem h32 : Reduced f32 p32 := .mul h4 h7 ⟨cancel32, by decide +kernel, by decide +kernel⟩

def f33 : Formula := .div f31 f32
def num33 : Expr := .bands [
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den33 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel33 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p33 : Fraction := ⟨num33, den33⟩
theorem h33 : Reduced f33 p33 := .div h31 h32 [.integer (2), .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel33, by decide +kernel, by decide +kernel⟩

def f34 : Formula := .mul f13 f33
def num34 : Expr := .bands [
  ⟨2, 2, 1, 0x0, 0x1, 1⟩
]

def den34 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel34 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p34 : Fraction := ⟨num34, den34⟩
theorem h34 : Reduced f34 p34 := .mul h13 h33 ⟨cancel34, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.MixedConservationWitness
