import PureOddWitness1

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f90 : Formula := .mul f2 f89
def num90 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den90 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel90 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p90 : Fraction := ⟨num90, den90⟩
theorem h90 : Reduced f90 p90 := .mul h2 h89 ⟨cancel90, by decide +kernel, by decide +kernel⟩

def f91 : Formula := .mul f37 f37
def num91 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den91 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel91 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p91 : Fraction := ⟨num91, den91⟩
theorem h91 : Reduced f91 p91 := .mul h37 h37 ⟨cancel91, by decide +kernel, by decide +kernel⟩

def f92 : Formula := .mul f90 f91
def num92 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x14000000000000000000000000000c0000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0xb00000000000000000000000000060000000000000000000000000000, 1⟩,
  ⟨3, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den92 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel92 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p92 : Fraction := ⟨num92, den92⟩
theorem h92 : Reduced f92 p92 := .mul h90 h91 ⟨cancel92, by decide +kernel, by decide +kernel⟩

def f93 : Formula := .mul f1 f53
def num93 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def den93 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel93 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p93 : Fraction := ⟨num93, den93⟩
theorem h93 : Reduced f93 p93 := .mul h1 h53 ⟨cancel93, by decide +kernel, by decide +kernel⟩

def f94 : Formula := .mul f20 f20
def num94 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den94 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel94 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p94 : Fraction := ⟨num94, den94⟩
theorem h94 : Reduced f94 p94 := .mul h20 h20 ⟨cancel94, by decide +kernel, by decide +kernel⟩

def f95 : Formula := .mul f93 f94
def num95 : Expr := .bands [
  ⟨2, 0, 1, 0x8, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def den95 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel95 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p95 : Fraction := ⟨num95, den95⟩
theorem h95 : Reduced f95 p95 := .mul h93 h94 ⟨cancel95, by decide +kernel, by decide +kernel⟩

def f96 : Formula := .div f92 f95
def num96 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den96 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel96 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p96 : Fraction := ⟨num96, den96⟩
theorem h96 : Reduced f96 p96 := .div h92 h95 [.integer (2), .radius, .radius, .horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel96, by decide +kernel, by decide +kernel⟩

def f97 : Formula := .neg f96
def p97 : Fraction := p96.neg
theorem h97 : Reduced f97 p97 := .neg h96

def f98 : Formula := .add f84 f97
def num98 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den98 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel98 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def p98 : Fraction := ⟨num98, den98⟩
theorem h98 : Reduced f98 p98 := .add h84 h97 ⟨cancel98, by decide +kernel, by decide +kernel⟩

def f99 : Formula := .mul f18 f2
def num99 : Expr := .bands [
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den99 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel99 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p99 : Fraction := ⟨num99, den99⟩
theorem h99 : Reduced f99 p99 := .mul h18 h2 ⟨cancel99, by decide +kernel, by decide +kernel⟩

def f100 : Formula := .neg f3
def p100 : Fraction := p3.neg
theorem h100 : Reduced f100 p100 := .neg h3

def f101 : Formula := .add f99 f100
def num101 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den101 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel101 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p101 : Fraction := ⟨num101, den101⟩
theorem h101 : Reduced f101 p101 := .add h99 h100 ⟨cancel101, by decide +kernel, by decide +kernel⟩

def f102 : Formula := .add f101 f0
def num102 : Expr := .bands [
  ⟨0, 0, 2, 0x1, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den102 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel102 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p102 : Fraction := ⟨num102, den102⟩
theorem h102 : Reduced f102 p102 := .add h101 h0 ⟨cancel102, by decide +kernel, by decide +kernel⟩

def f103 : Formula := .mul f2 f102
def num103 : Expr := .bands [
  ⟨0, 0, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den103 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel103 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p103 : Fraction := ⟨num103, den103⟩
theorem h103 : Reduced f103 p103 := .mul h2 h102 ⟨cancel103, by decide +kernel, by decide +kernel⟩

def f104 : Formula := .mul f42 f42
def num104 : Expr := .bands [
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den104 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel104 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p104 : Fraction := ⟨num104, den104⟩
theorem h104 : Reduced f104 p104 := .mul h42 h42 ⟨cancel104, by decide +kernel, by decide +kernel⟩

def f105 : Formula := .mul f103 f104
def num105 : Expr := .bands [
  ⟨4, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den105 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel105 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p105 : Fraction := ⟨num105, den105⟩
theorem h105 : Reduced f105 p105 := .mul h103 h104 ⟨cancel105, by decide +kernel, by decide +kernel⟩

def f106 : Formula := .mul f56 f18
def num106 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def den106 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel106 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p106 : Fraction := ⟨num106, den106⟩
theorem h106 : Reduced f106 p106 := .mul h56 h18 ⟨cancel106, by decide +kernel, by decide +kernel⟩

def f107 : Formula := .mul f1 f106
def num107 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def den107 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel107 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p107 : Fraction := ⟨num107, den107⟩
theorem h107 : Reduced f107 p107 := .mul h1 h106 ⟨cancel107, by decide +kernel, by decide +kernel⟩

def f108 : Formula := .div f105 f107
def num108 : Expr := .bands [
  ⟨0, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den108 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def cancel108 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p108 : Fraction := ⟨num108, den108⟩
theorem h108 : Reduced f108 p108 := .div h105 h107 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel108, by decide +kernel, by decide +kernel⟩

def f109 : Formula := .add f98 f108
def num109 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den109 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel109 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def p109 : Fraction := ⟨num109, den109⟩
theorem h109 : Reduced f109 p109 := .add h98 h108 ⟨cancel109, by decide +kernel, by decide +kernel⟩

def f110 : Formula := .mul f33 f109
def num110 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den110 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x18, 1⟩,
  ⟨5, 0, 3, 0x14, 0x1000000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨6, 0, 3, 0x800000000000000000000000000040000000000000000000000000000, 0x4, 1⟩
]

def cancel110 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p110 : Fraction := ⟨num110, den110⟩
theorem h110 : Reduced f110 p110 := .mul h33 h109 ⟨cancel110, by decide +kernel, by decide +kernel⟩

def f111 : Formula := .div f1 f18
def num111 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def den111 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel111 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p111 : Fraction := ⟨num111, den111⟩
theorem h111 : Reduced f111 p111 := .div h1 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel111, by decide +kernel, by decide +kernel⟩

def f112 : Formula := .neg f111
def p112 : Fraction := p111.neg
theorem h112 : Reduced f112 p112 := .neg h111

def f113 : Formula := .div f2 f5
def num113 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den113 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000000, 0x1, 1⟩
]

def cancel113 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p113 : Fraction := ⟨num113, den113⟩
theorem h113 : Reduced f113 p113 := .div h2 h5 [.twiceMinus] (by decide +kernel) (by decide +kernel) ⟨cancel113, by decide +kernel, by decide +kernel⟩

def f114 : Formula := .mul f56 f54
def num114 : Expr := .bands [
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den114 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel114 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p114 : Fraction := ⟨num114, den114⟩
theorem h114 : Reduced f114 p114 := .mul h56 h54 ⟨cancel114, by decide +kernel, by decide +kernel⟩

def f115 : Formula := .mul f2 f2
def num115 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den115 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel115 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p115 : Fraction := ⟨num115, den115⟩
theorem h115 : Reduced f115 p115 := .mul h2 h2 ⟨cancel115, by decide +kernel, by decide +kernel⟩

def f116 : Formula := .mul f44 f115
def num116 : Expr := .bands [
  ⟨1, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den116 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel116 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p116 : Fraction := ⟨num116, den116⟩
theorem h116 : Reduced f116 p116 := .mul h44 h115 ⟨cancel116, by decide +kernel, by decide +kernel⟩

def f117 : Formula := .neg f116
def p117 : Fraction := p116.neg
theorem h117 : Reduced f117 p117 := .neg h116

def f118 : Formula := .add f114 f117
def num118 : Expr := .bands [
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den118 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel118 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p118 : Fraction := ⟨num118, den118⟩
theorem h118 : Reduced f118 p118 := .add h114 h117 ⟨cancel118, by decide +kernel, by decide +kernel⟩

def f119 : Formula := .neg f85
def p119 : Fraction := p85.neg
theorem h119 : Reduced f119 p119 := .neg h85

def f120 : Formula := .add f118 f119
def num120 : Expr := .bands [
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den120 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel120 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p120 : Fraction := ⟨num120, den120⟩
theorem h120 : Reduced f120 p120 := .add h118 h119 ⟨cancel120, by decide +kernel, by decide +kernel⟩

def f121 : Formula := .add f120 f44
def num121 : Expr := .bands [
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den121 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel121 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p121 : Fraction := ⟨num121, den121⟩
theorem h121 : Reduced f121 p121 := .add h120 h44 ⟨cancel121, by decide +kernel, by decide +kernel⟩

def f122 : Formula := .mul f67 f115
def num122 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den122 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel122 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p122 : Fraction := ⟨num122, den122⟩
theorem h122 : Reduced f122 p122 := .mul h67 h115 ⟨cancel122, by decide +kernel, by decide +kernel⟩

def f123 : Formula := .add f121 f122
def num123 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den123 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel123 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p123 : Fraction := ⟨num123, den123⟩
theorem h123 : Reduced f123 p123 := .add h121 h122 ⟨cancel123, by decide +kernel, by decide +kernel⟩

def f124 : Formula := .mul f67 f2
def num124 : Expr := .bands [
  ⟨0, 0, 2, 0x40000000000000000000000000000, 0x0, 1⟩
]

def den124 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel124 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p124 : Fraction := ⟨num124, den124⟩
theorem h124 : Reduced f124 p124 := .mul h67 h2 ⟨cancel124, by decide +kernel, by decide +kernel⟩

def f125 : Formula := .add f123 f124
def num125 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den125 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel125 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p125 : Fraction := ⟨num125, den125⟩
theorem h125 : Reduced f125 p125 := .add h123 h124 ⟨cancel125, by decide +kernel, by decide +kernel⟩

def f126 : Formula := .neg f67
def p126 : Fraction := p67.neg
theorem h126 : Reduced f126 p126 := .neg h67

def f127 : Formula := .add f125 f126
def num127 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den127 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel127 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p127 : Fraction := ⟨num127, den127⟩
theorem h127 : Reduced f127 p127 := .add h125 h126 ⟨cancel127, by decide +kernel, by decide +kernel⟩

def f128 : Formula := .mul f127 f104
def num128 : Expr := .bands [
  ⟨4, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨7, 4, 1, 0x1, 0x0, 1⟩
]

def den128 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel128 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p128 : Fraction := ⟨num128, den128⟩
theorem h128 : Reduced f128 p128 := .mul h127 h104 ⟨cancel128, by decide +kernel, by decide +kernel⟩

def f129 : Formula := .div f128 f81
def num129 : Expr := .bands [
  ⟨1, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨2, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x1, 0x0, 1⟩
]

def den129 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel129 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p129 : Fraction := ⟨num129, den129⟩
theorem h129 : Reduced f129 p129 := .div h128 h81 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel129, by decide +kernel, by decide +kernel⟩

def f130 : Formula := .mul f14 f65
def num130 : Expr := .bands [
  ⟨0, 1, 1, 0x8, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den130 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel130 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p130 : Fraction := ⟨num130, den130⟩
theorem h130 : Reduced f130 p130 := .mul h14 h65 ⟨cancel130, by decide +kernel, by decide +kernel⟩

def f131 : Formula := .mul f130 f42
def num131 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x8, 1⟩,
  ⟨1, 2, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x0, 0x1, 1⟩
]

def den131 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel131 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p131 : Fraction := ⟨num131, den131⟩
theorem h131 : Reduced f131 p131 := .mul h130 h42 ⟨cancel131, by decide +kernel, by decide +kernel⟩

def f132 : Formula := .mul f65 f65
def num132 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x2000000000000000000000000000200000000000000000000000000040, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000002400000000000000000000000000200000000000000000000000000010, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000c00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x10, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000008, 1⟩,
  ⟨6, 2, 3, 0x200000000000000000000000000020000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x1, 0x0, 1⟩
]

def den132 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel132 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p132 : Fraction := ⟨num132, den132⟩
theorem h132 : Reduced f132 p132 := .mul h65 h65 ⟨cancel132, by decide +kernel, by decide +kernel⟩

def f133 : Formula := .add f131 f132
def num133 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x2000000000000000000000000000200000000000000000000000000040, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000002400000000000000000000000000200000000000000000000000000010, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000c00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den133 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel133 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p133 : Fraction := ⟨num133, den133⟩
theorem h133 : Reduced f133 p133 := .add h131 h132 ⟨cancel133, by decide +kernel, by decide +kernel⟩

def f134 : Formula := .div f133 f67
def num134 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x2000000000000000000000000000200000000000000000000000000040, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000002400000000000000000000000000200000000000000000000000000010, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000c00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den134 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel134 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p134 : Fraction := ⟨num134, den134⟩
theorem h134 : Reduced f134 p134 := .div h133 h67 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel134, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
