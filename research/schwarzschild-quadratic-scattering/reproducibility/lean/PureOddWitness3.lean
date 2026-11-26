import PureOddWitness2

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f135 : Formula := .add f129 f134
def num135 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 3, 0x1000000000000000000000000000100000000000000000000000000010, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x20000000000000000000000000004000000000000000000000000000a00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den135 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel135 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x80, 1⟩,
  ⟨1, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x60, 1⟩,
  ⟨3, 0, 1, 0x10, 0x0, 1⟩
]

def p135 : Fraction := ⟨num135, den135⟩
theorem h135 : Reduced f135 p135 := .add h129 h134 ⟨cancel135, by decide +kernel, by decide +kernel⟩

def f136 : Formula := .mul f13 f37
def num136 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den136 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel136 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p136 : Fraction := ⟨num136, den136⟩
theorem h136 : Reduced f136 p136 := .mul h13 h37 ⟨cancel136, by decide +kernel, by decide +kernel⟩

def f137 : Formula := .mul f136 f42
def num137 : Expr := .bands [
  ⟨1, 2, 1, 0x0, 0x1, 1⟩
]

def den137 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel137 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p137 : Fraction := ⟨num137, den137⟩
theorem h137 : Reduced f137 p137 := .mul h136 h42 ⟨cancel137, by decide +kernel, by decide +kernel⟩

def f138 : Formula := .mul f37 f65
def num138 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den138 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel138 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p138 : Fraction := ⟨num138, den138⟩
theorem h138 : Reduced f138 p138 := .mul h37 h65 ⟨cancel138, by decide +kernel, by decide +kernel⟩

def f139 : Formula := .add f137 f138
def num139 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den139 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel139 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p139 : Fraction := ⟨num139, den139⟩
theorem h139 : Reduced f139 p139 := .add h137 h138 ⟨cancel139, by decide +kernel, by decide +kernel⟩

def f140 : Formula := .div f139 f18
def num140 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den140 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel140 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p140 : Fraction := ⟨num140, den140⟩
theorem h140 : Reduced f140 p140 := .div h139 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel140, by decide +kernel, by decide +kernel⟩

def f141 : Formula := .neg f140
def p141 : Fraction := p140.neg
theorem h141 : Reduced f141 p141 := .neg h140

def f142 : Formula := .add f135 f141
def num142 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x30, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000010, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den142 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel142 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p142 : Fraction := ⟨num142, den142⟩
theorem h142 : Reduced f142 p142 := .add h135 h141 ⟨cancel142, by decide +kernel, by decide +kernel⟩

def f143 : Formula := .mul f18 f115
def num143 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den143 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel143 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p143 : Fraction := ⟨num143, den143⟩
theorem h143 : Reduced f143 p143 := .mul h18 h115 ⟨cancel143, by decide +kernel, by decide +kernel⟩

def f144 : Formula := .add f143 f99
def num144 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den144 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel144 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p144 : Fraction := ⟨num144, den144⟩
theorem h144 : Reduced f144 p144 := .add h143 h99 ⟨cancel144, by decide +kernel, by decide +kernel⟩

def f145 : Formula := .add f144 f18
def num145 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den145 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel145 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p145 : Fraction := ⟨num145, den145⟩
theorem h145 : Reduced f145 p145 := .add h144 h18 ⟨cancel145, by decide +kernel, by decide +kernel⟩

def f146 : Formula := .add f145 f126
def num146 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den146 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel146 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p146 : Fraction := ⟨num146, den146⟩
theorem h146 : Reduced f146 p146 := .add h145 h126 ⟨cancel146, by decide +kernel, by decide +kernel⟩

def f147 : Formula := .mul f146 f91
def num147 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 3, 0x400000000000000000000000000040000000000000000000000000014, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000008, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den147 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel147 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p147 : Fraction := ⟨num147, den147⟩
theorem h147 : Reduced f147 p147 := .mul h146 h91 ⟨cancel147, by decide +kernel, by decide +kernel⟩

def f148 : Formula := .mul f1 f20
def num148 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den148 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel148 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p148 : Fraction := ⟨num148, den148⟩
theorem h148 : Reduced f148 p148 := .mul h1 h20 ⟨cancel148, by decide +kernel, by decide +kernel⟩

def f149 : Formula := .mul f148 f53
def num149 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def den149 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel149 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p149 : Fraction := ⟨num149, den149⟩
theorem h149 : Reduced f149 p149 := .mul h148 h53 ⟨cancel149, by decide +kernel, by decide +kernel⟩

def f150 : Formula := .div f147 f149
def num150 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den150 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel150 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p150 : Fraction := ⟨num150, den150⟩
theorem h150 : Reduced f150 p150 := .div h147 h149 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel150, by decide +kernel, by decide +kernel⟩

def f151 : Formula := .add f142 f150
def num151 : Expr := .bands [
  ⟨0, 0, 3, 0x800000000000000000000000000080000000000000000000000000000, 0x8, 1⟩,
  ⟨1, 0, 5, 0x0, 0x20000000000000000000000000004000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000002, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den151 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel151 : Expr := .bands [
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def p151 : Fraction := ⟨num151, den151⟩
theorem h151 : Reduced f151 p151 := .add h142 h150 ⟨cancel151, by decide +kernel, by decide +kernel⟩

def f152 : Formula := .mul f113 f151
def num152 : Expr := .bands [
  ⟨0, 0, 4, 0x8000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨1, 0, 6, 0x0, 0x200000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 6, 0x100000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 4, 0x20000000000000000000000000000, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den152 : Expr := .bands [
  ⟨3, 0, 2, 0x20, 0x400000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x200000000000000000000000000000, 0x10, 1⟩
]

def cancel152 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p152 : Fraction := ⟨num152, den152⟩
theorem h152 : Reduced f152 p152 := .mul h113 h151 ⟨cancel152, by decide +kernel, by decide +kernel⟩

def f153 : Formula := .mul f112 f152
def num153 : Expr := .bands [
  ⟨0, 0, 4, 0x80000000000000000000000000000, 0x8000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 6, 0x200000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 6, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den153 : Expr := .bands [
  ⟨4, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨5, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel153 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p153 : Fraction := ⟨num153, den153⟩
theorem h153 : Reduced f153 p153 := .mul h112 h152 ⟨cancel153, by decide +kernel, by decide +kernel⟩

def f154 : Formula := .add f3 f0
def num154 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den154 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel154 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p154 : Fraction := ⟨num154, den154⟩
theorem h154 : Reduced f154 p154 := .add h3 h0 ⟨cancel154, by decide +kernel, by decide +kernel⟩

def f155 : Formula := .mul f3 f154
def num155 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000020000000000000000000000000000, 0x0, 1⟩
]

def den155 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel155 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p155 : Fraction := ⟨num155, den155⟩
theorem h155 : Reduced f155 p155 := .mul h3 h154 ⟨cancel155, by decide +kernel, by decide +kernel⟩

def f156 : Formula := .mul f155 f32
def num156 : Expr := .bands [
  ⟨0, 0, 3, 0x18000000000000000000000000000c0000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x100000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000000000000000000040000000000000000000000000000, 1⟩
]

def den156 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel156 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p156 : Fraction := ⟨num156, den156⟩
theorem h156 : Reduced f156 p156 := .mul h155 h32 ⟨cancel156, by decide +kernel, by decide +kernel⟩

def f157 : Formula := .div f1 f156
def num157 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den157 : Expr := .bands [
  ⟨0, 0, 3, 0xc00000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x80000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def cancel157 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p157 : Fraction := ⟨num157, den157⟩
theorem h157 : Reduced f157 p157 := .div h1 h156 [.integer (4), .angular, .twicePlus, .daughterPole] (by decide +kernel) (by decide +kernel) ⟨cancel157, by decide +kernel, by decide +kernel⟩

def f158 : Formula := .integer (24)
def p158 : Fraction := .polynomial (.constant (24))
theorem h158 : Reduced f158 p158 := .integer (24)

def f159 : Formula := .mul f21 f21
def num159 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den159 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel159 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p159 : Fraction := ⟨num159, den159⟩
theorem h159 : Reduced f159 p159 := .mul h21 h21 ⟨cancel159, by decide +kernel, by decide +kernel⟩

def f160 : Formula := .mul f158 f159
def num160 : Expr := .bands [
  ⟨0, 0, 1, 0x60, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x60, 1⟩,
  ⟨2, 0, 1, 0x18, 0x0, 1⟩
]

def den160 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel160 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p160 : Fraction := ⟨num160, den160⟩
theorem h160 : Reduced f160 p160 := .mul h158 h159 ⟨cancel160, by decide +kernel, by decide +kernel⟩

def f161 : Formula := .div f160 f32
def num161 : Expr := .bands [
  ⟨0, 0, 1, 0x30, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x30, 1⟩,
  ⟨2, 0, 1, 0xc, 0x0, 1⟩
]

def den161 : Expr := .bands [
  ⟨1, 0, 1, 0x3, 0x0, 1⟩,
  ⟨2, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def cancel161 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p161 : Fraction := ⟨num161, den161⟩
theorem h161 : Reduced f161 p161 := .div h160 h32 [.integer (2), .daughterPole] (by decide +kernel) (by decide +kernel) ⟨cancel161, by decide +kernel, by decide +kernel⟩

def f162 : Formula := .mul f11 f56
def num162 : Expr := .bands [
  ⟨3, 0, 1, 0x3, 0x0, 1⟩
]

def den162 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel162 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p162 : Fraction := ⟨num162, den162⟩
theorem h162 : Reduced f162 p162 := .mul h11 h56 ⟨cancel162, by decide +kernel, by decide +kernel⟩

def f163 : Formula := .mul f162 f54
def num163 : Expr := .bands [
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den163 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel163 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p163 : Fraction := ⟨num163, den163⟩
theorem h163 : Reduced f163 p163 := .mul h162 h54 ⟨cancel163, by decide +kernel, by decide +kernel⟩

def f164 : Formula := .mul f11 f18
def num164 : Expr := .bands [
  ⟨1, 0, 1, 0x3, 0x0, 1⟩
]

def den164 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel164 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p164 : Fraction := ⟨num164, den164⟩
theorem h164 : Reduced f164 p164 := .mul h11 h18 ⟨cancel164, by decide +kernel, by decide +kernel⟩

def f165 : Formula := .mul f164 f115
def num165 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den165 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel165 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p165 : Fraction := ⟨num165, den165⟩
theorem h165 : Reduced f165 p165 := .mul h164 h115 ⟨cancel165, by decide +kernel, by decide +kernel⟩

def f166 : Formula := .add f163 f165
def num166 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den166 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel166 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p166 : Fraction := ⟨num166, den166⟩
theorem h166 : Reduced f166 p166 := .add h163 h165 ⟨cancel166, by decide +kernel, by decide +kernel⟩

def f167 : Formula := .add f166 f18
def num167 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den167 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel167 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p167 : Fraction := ⟨num167, den167⟩
theorem h167 : Reduced f167 p167 := .add h166 h18 ⟨cancel167, by decide +kernel, by decide +kernel⟩

def f168 : Formula := .mul f30 f115
def num168 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den168 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel168 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p168 : Fraction := ⟨num168, den168⟩
theorem h168 : Reduced f168 p168 := .mul h30 h115 ⟨cancel168, by decide +kernel, by decide +kernel⟩

def f169 : Formula := .neg f168
def p169 : Fraction := p168.neg
theorem h169 : Reduced f169 p169 := .neg h168

def f170 : Formula := .add f167 f169
def num170 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den170 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel170 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p170 : Fraction := ⟨num170, den170⟩
theorem h170 : Reduced f170 p170 := .add h167 h169 ⟨cancel170, by decide +kernel, by decide +kernel⟩

def f171 : Formula := .add f170 f19
def num171 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000002, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den171 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel171 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p171 : Fraction := ⟨num171, den171⟩
theorem h171 : Reduced f171 p171 := .add h170 h19 ⟨cancel171, by decide +kernel, by decide +kernel⟩

def f172 : Formula := .neg f171
def p172 : Fraction := p171.neg
theorem h172 : Reduced f172 p172 := .neg h171

def f173 : Formula := .mul f172 f115
def num173 : Expr := .bands [
  ⟨0, 0, 5, 0x60000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x30000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den173 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel173 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p173 : Fraction := ⟨num173, den173⟩
theorem h173 : Reduced f173 p173 := .mul h172 h115 ⟨cancel173, by decide +kernel, by decide +kernel⟩

def f174 : Formula := .mul f173 f104
def num174 : Expr := .bands [
  ⟨4, 2, 5, 0x60000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x0, 0x30000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨7, 4, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den174 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel174 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p174 : Fraction := ⟨num174, den174⟩
theorem h174 : Reduced f174 p174 := .mul h173 h104 ⟨cancel174, by decide +kernel, by decide +kernel⟩

def f175 : Formula := .mul f67 f20
def num175 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def den175 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel175 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p175 : Fraction := ⟨num175, den175⟩
theorem h175 : Reduced f175 p175 := .mul h67 h20 ⟨cancel175, by decide +kernel, by decide +kernel⟩

def f176 : Formula := .mul f175 f106
def num176 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def den176 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel176 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p176 : Fraction := ⟨num176, den176⟩
theorem h176 : Reduced f176 p176 := .mul h175 h106 ⟨cancel176, by decide +kernel, by decide +kernel⟩

def f177 : Formula := .div f174 f176
def num177 : Expr := .bands [
  ⟨0, 2, 5, 0x60000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 2, 5, 0x0, 0x30000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 4, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den177 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x80, 1⟩,
  ⟨1, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x60, 1⟩,
  ⟨3, 0, 1, 0x10, 0x0, 1⟩
]

def cancel177 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p177 : Fraction := ⟨num177, den177⟩
theorem h177 : Reduced f177 p177 := .div h174 h176 [.integer (4), .radius, .radius, .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel177, by decide +kernel, by decide +kernel⟩

def f178 : Formula := .mul f14 f37
def num178 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den178 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel178 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p178 : Fraction := ⟨num178, den178⟩
theorem h178 : Reduced f178 p178 := .mul h14 h37 ⟨cancel178, by decide +kernel, by decide +kernel⟩

def f179 : Formula := .mul f178 f79
def num179 : Expr := .bands [
  ⟨0, 2, 1, 0x4, 0x0, 1⟩,
  ⟨1, 2, 1, 0x0, 0x1, 1⟩
]

def den179 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel179 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p179 : Fraction := ⟨num179, den179⟩
theorem h179 : Reduced f179 p179 := .mul h178 h79 ⟨cancel179, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
