import QuadraticConservationExport

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f0 : Formula := .integer (2)
def p0 : Fraction := .polynomial (.constant (2))
theorem h0 : Reduced f0 p0 := .integer (2)

def f1 : Formula := .frequency
def p1 : Fraction := .polynomial (Expr.frequency)
theorem h1 : Reduced f1 p1 := .frequency

def f2 : Formula := .mul f0 f1
def num2 : Expr := .bands [
  ⟨0, 1, 1, 0x2, 0x0, 1⟩
]

def den2 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2 : Fraction := ⟨num2, den2⟩
theorem h2 : Reduced f2 p2 := .mul h0 h1 ⟨cancel2, by decide +kernel, by decide +kernel⟩

def f3 : Formula := .radius
def p3 : Fraction := .polynomial (NumeratorData.x 1)
theorem h3 : Reduced f3 p3 := .radius

def f4 : Formula := .neg f0
def p4 : Fraction := p0.neg
theorem h4 : Reduced f4 p4 := .neg h0

def f5 : Formula := .add f3 f4
def num5 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den5 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel5 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p5 : Fraction := ⟨num5, den5⟩
theorem h5 : Reduced f5 p5 := .add h3 h4 ⟨cancel5, by decide +kernel, by decide +kernel⟩

def f6 : Formula := .div f5 f3
def num6 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den6 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel6 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p6 : Fraction := ⟨num6, den6⟩
theorem h6 : Reduced f6 p6 := .div h5 h3 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel6, by decide +kernel, by decide +kernel⟩

def f7 : Formula := .div f2 f6
def num7 : Expr := .bands [
  ⟨1, 1, 1, 0x2, 0x0, 1⟩
]

def den7 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel7 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p7 : Fraction := ⟨num7, den7⟩
theorem h7 : Reduced f7 p7 := .div h2 h6 [.horizon] (by decide +kernel) (by decide +kernel) ⟨cancel7, by decide +kernel, by decide +kernel⟩

def f8 : Formula := .integer (1)
def p8 : Fraction := .polynomial (.constant (1))
theorem h8 : Reduced f8 p8 := .integer (1)

def f9 : Formula := .neg f8
def p9 : Fraction := p8.neg
theorem h9 : Reduced f9 p9 := .neg h8

def f10 : Formula := .integer (4)
def p10 : Fraction := .polynomial (.constant (4))
theorem h10 : Reduced f10 p10 := .integer (4)

def f11 : Formula := .div f8 f10
def num11 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den11 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel11 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p11 : Fraction := ⟨num11, den11⟩
theorem h11 : Reduced f11 p11 := .div h8 h10 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel11, by decide +kernel, by decide +kernel⟩

def f12 : Formula := .mul f8 f3
def num12 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den12 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel12 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p12 : Fraction := ⟨num12, den12⟩
theorem h12 : Reduced f12 p12 := .mul h8 h3 ⟨cancel12, by decide +kernel, by decide +kernel⟩

def f13 : Formula := .mul f12 f3
def num13 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den13 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel13 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p13 : Fraction := ⟨num13, den13⟩
theorem h13 : Reduced f13 p13 := .mul h12 h3 ⟨cancel13, by decide +kernel, by decide +kernel⟩

def f14 : Formula := .mul f11 f13
def num14 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den14 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel14 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p14 : Fraction := ⟨num14, den14⟩
theorem h14 : Reduced f14 p14 := .mul h11 h13 ⟨cancel14, by decide +kernel, by decide +kernel⟩

def f15 : Formula := .mul f14 f8
def num15 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den15 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel15 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p15 : Fraction := ⟨num15, den15⟩
theorem h15 : Reduced f15 p15 := .mul h14 h8 ⟨cancel15, by decide +kernel, by decide +kernel⟩

def f16 : Formula := .angular
def p16 : Fraction := .polynomial (Expr.angular)
theorem h16 : Reduced f16 p16 := .angular

def f17 : Formula := .mul f8 f16
def num17 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den17 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel17 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p17 : Fraction := ⟨num17, den17⟩
theorem h17 : Reduced f17 p17 := .mul h8 h16 ⟨cancel17, by decide +kernel, by decide +kernel⟩

def f18 : Formula := .mul f17 f16
def num18 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den18 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel18 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p18 : Fraction := ⟨num18, den18⟩
theorem h18 : Reduced f18 p18 := .mul h17 h16 ⟨cancel18, by decide +kernel, by decide +kernel⟩

def f19 : Formula := .mul f15 f18
def num19 : Expr := .bands [
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den19 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel19 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p19 : Fraction := ⟨num19, den19⟩
theorem h19 : Reduced f19 p19 := .mul h15 h18 ⟨cancel19, by decide +kernel, by decide +kernel⟩

def f20 : Formula := .integer (-1)
def p20 : Fraction := .polynomial (.constant (-1))
theorem h20 : Reduced f20 p20 := .integer (-1)

def f21 : Formula := .div f20 f0
def num21 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den21 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel21 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p21 : Fraction := ⟨num21, den21⟩
theorem h21 : Reduced f21 p21 := .div h20 h0 [.integer (2)] (by decide +kernel) (by decide +kernel) ⟨cancel21, by decide +kernel, by decide +kernel⟩

def f22 : Formula := .mul f21 f12
def num22 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x1, 1⟩
]

def den22 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel22 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p22 : Fraction := ⟨num22, den22⟩
theorem h22 : Reduced f22 p22 := .mul h21 h12 ⟨cancel22, by decide +kernel, by decide +kernel⟩

def f23 : Formula := .mul f22 f8
def num23 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x1, 1⟩
]

def den23 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel23 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p23 : Fraction := ⟨num23, den23⟩
theorem h23 : Reduced f23 p23 := .mul h22 h8 ⟨cancel23, by decide +kernel, by decide +kernel⟩

def f24 : Formula := .mul f23 f18
def num24 : Expr := .bands [
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den24 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel24 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p24 : Fraction := ⟨num24, den24⟩
theorem h24 : Reduced f24 p24 := .mul h23 h18 ⟨cancel24, by decide +kernel, by decide +kernel⟩

def f25 : Formula := .mul f20 f8
def num25 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den25 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel25 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p25 : Fraction := ⟨num25, den25⟩
theorem h25 : Reduced f25 p25 := .mul h20 h8 ⟨cancel25, by decide +kernel, by decide +kernel⟩

def f26 : Formula := .mul f25 f8
def num26 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den26 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel26 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p26 : Fraction := ⟨num26, den26⟩
theorem h26 : Reduced f26 p26 := .mul h25 h8 ⟨cancel26, by decide +kernel, by decide +kernel⟩

def f27 : Formula := .mul f26 f8
def num27 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den27 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel27 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p27 : Fraction := ⟨num27, den27⟩
theorem h27 : Reduced f27 p27 := .mul h26 h8 ⟨cancel27, by decide +kernel, by decide +kernel⟩

def f28 : Formula := .integer (0)
def p28 : Fraction := .polynomial (.constant (0))
theorem h28 : Reduced f28 p28 := .integer (0)

def f29 : Formula := .add f27 f28
def num29 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den29 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel29 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p29 : Fraction := ⟨num29, den29⟩
theorem h29 : Reduced f29 p29 := .add h27 h28 ⟨cancel29, by decide +kernel, by decide +kernel⟩

def f30 : Formula := .add f24 f29
def num30 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den30 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel30 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p30 : Fraction := ⟨num30, den30⟩
theorem h30 : Reduced f30 p30 := .add h24 h29 ⟨cancel30, by decide +kernel, by decide +kernel⟩

def f31 : Formula := .add f19 f30
def num31 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den31 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel31 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p31 : Fraction := ⟨num31, den31⟩
theorem h31 : Reduced f31 p31 := .add h19 h30 ⟨cancel31, by decide +kernel, by decide +kernel⟩

def f32 : Formula := .div f8 f3
def num32 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den32 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel32 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p32 : Fraction := ⟨num32, den32⟩
theorem h32 : Reduced f32 p32 := .div h8 h3 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel32, by decide +kernel, by decide +kernel⟩

def f33 : Formula := .mul f8 f32
def num33 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den33 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel33 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p33 : Fraction := ⟨num33, den33⟩
theorem h33 : Reduced f33 p33 := .mul h8 h32 ⟨cancel33, by decide +kernel, by decide +kernel⟩

def f34 : Formula := .mul f33 f32
def num34 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den34 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel34 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p34 : Fraction := ⟨num34, den34⟩
theorem h34 : Reduced f34 p34 := .mul h33 h32 ⟨cancel34, by decide +kernel, by decide +kernel⟩

def f35 : Formula := .mul f31 f34
def num35 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den35 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel35 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p35 : Fraction := ⟨num35, den35⟩
theorem h35 : Reduced f35 p35 := .mul h31 h34 ⟨cancel35, by decide +kernel, by decide +kernel⟩

def f36 : Formula := .div f8 f5
def num36 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den36 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel36 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p36 : Fraction := ⟨num36, den36⟩
theorem h36 : Reduced f36 p36 := .div h8 h5 [.horizon] (by decide +kernel) (by decide +kernel) ⟨cancel36, by decide +kernel, by decide +kernel⟩

def f37 : Formula := .mul f8 f36
def num37 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den37 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel37 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p37 : Fraction := ⟨num37, den37⟩
theorem h37 : Reduced f37 p37 := .mul h8 h36 ⟨cancel37, by decide +kernel, by decide +kernel⟩

def f38 : Formula := .mul f37 f36
def num38 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den38 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel38 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p38 : Fraction := ⟨num38, den38⟩
theorem h38 : Reduced f38 p38 := .mul h37 h36 ⟨cancel38, by decide +kernel, by decide +kernel⟩

def f39 : Formula := .mul f35 f38
def num39 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den39 : Expr := .bands [
  ⟨2, 0, 1, 0x10, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel39 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p39 : Fraction := ⟨num39, den39⟩
theorem h39 : Reduced f39 p39 := .mul h35 h38 ⟨cancel39, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
