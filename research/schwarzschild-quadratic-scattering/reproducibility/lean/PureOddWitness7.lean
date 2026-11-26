import PureOddWitness6

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f315 : Formula := .add f291 f314
def num315 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xa000000000000000000000000000a000000000000000000000000001400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 7, 0x0, 0x20000000000000000000000000004000000000000000000000000000a0000000000000000000000000008000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000200000000000000000000000000030000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x1000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x70000000000000000000000000006000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den315 : Expr := .bands [
  ⟨7, 0, 1, 0x10, 0x0, 1⟩
]

def cancel315 : Expr := .bands [
  ⟨3, 0, 1, 0x40, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x40, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def p315 : Fraction := ⟨num315, den315⟩
theorem h315 : Reduced f315 p315 := .add h291 h314 ⟨cancel315, by decide +kernel, by decide +kernel⟩

def f316 : Formula := .mul f13 f292
def num316 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x1, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den316 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel316 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p316 : Fraction := ⟨num316, den316⟩
theorem h316 : Reduced f316 p316 := .mul h13 h292 ⟨cancel316, by decide +kernel, by decide +kernel⟩

def f317 : Formula := .mul f316 f288
def num317 : Expr := .bands [
  ⟨1, 2, 1, 0x1, 0x0, 1⟩,
  ⟨2, 2, 1, 0x0, 0x1, 1⟩
]

def den317 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel317 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p317 : Fraction := ⟨num317, den317⟩
theorem h317 : Reduced f317 p317 := .mul h316 h288 ⟨cancel317, by decide +kernel, by decide +kernel⟩

def f318 : Formula := .mul f292 f310
def num318 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000020000000000000000000000000006, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000002, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x1, 1⟩,
  ⟨5, 2, 1, 0x1, 0x0, 1⟩
]

def den318 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel318 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p318 : Fraction := ⟨num318, den318⟩
theorem h318 : Reduced f318 p318 := .mul h292 h310 ⟨cancel318, by decide +kernel, by decide +kernel⟩

def f319 : Formula := .neg f318
def p319 : Fraction := p318.neg
theorem h319 : Reduced f319 p319 := .neg h318

def f320 : Formula := .add f317 f319
def num320 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x300000000000000000000000000030000000000000000000000000002, 0x0, 1⟩,
  ⟨3, 0, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x2, 0x0, 1⟩,
  ⟨5, 2, 1, 0x0, 0x2, 1⟩
]

def den320 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel320 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p320 : Fraction := ⟨num320, den320⟩
theorem h320 : Reduced f320 p320 := .add h317 h319 ⟨cancel320, by decide +kernel, by decide +kernel⟩

def f321 : Formula := .mul f258 f320
def num321 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x20000000000000000000000000002000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000003000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den321 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel321 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p321 : Fraction := ⟨num321, den321⟩
theorem h321 : Reduced f321 p321 := .mul h258 h320 ⟨cancel321, by decide +kernel, by decide +kernel⟩

def f322 : Formula := .div f321 f106
def num322 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x20000000000000000000000000002000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000003000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den322 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def cancel322 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p322 : Fraction := ⟨num322, den322⟩
theorem h322 : Reduced f322 p322 := .div h321 h106 [.radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel322, by decide +kernel, by decide +kernel⟩

def f323 : Formula := .add f315 f322
def num323 : Expr := .bands [
  ⟨0, 0, 5, 0x20000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 7, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x1800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 5, 0x70000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x500000000000000000000000000000000000000000000000000000000, 1⟩
]

def den323 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel323 : Expr := .bands [
  ⟨8, 0, 1, 0x4, 0x0, 1⟩
]

def p323 : Fraction := ⟨num323, den323⟩
theorem h323 : Reduced f323 p323 := .add h315 h322 ⟨cancel323, by decide +kernel, by decide +kernel⟩

def f324 : Formula := .mul f271 f288
def num324 : Expr := .bands [
  ⟨2, 1, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 1, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 1, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den324 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel324 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p324 : Fraction := ⟨num324, den324⟩
theorem h324 : Reduced f324 p324 := .mul h271 h288 ⟨cancel324, by decide +kernel, by decide +kernel⟩

def f325 : Formula := .mul f324 f299
def num325 : Expr := .bands [
  ⟨3, 2, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den325 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel325 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p325 : Fraction := ⟨num325, den325⟩
theorem h325 : Reduced f325 p325 := .mul h324 h299 ⟨cancel325, by decide +kernel, by decide +kernel⟩

def f326 : Formula := .div f325 f254
def num326 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den326 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel326 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p326 : Fraction := ⟨num326, den326⟩
theorem h326 : Reduced f326 p326 := .div h325 h254 [.radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel326, by decide +kernel, by decide +kernel⟩

def f327 : Formula := .add f323 f326
def num327 : Expr := .bands [
  ⟨0, 0, 5, 0x20000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 7, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 5, 0x70000000000000000000000000006000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den327 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel327 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def p327 : Fraction := ⟨num327, den327⟩
theorem h327 : Reduced f327 p327 := .add h323 h326 ⟨cancel327, by decide +kernel, by decide +kernel⟩

def f328 : Formula := .mul f292 f292
def num328 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den328 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel328 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p328 : Fraction := ⟨num328, den328⟩
theorem h328 : Reduced f328 p328 := .mul h292 h292 ⟨cancel328, by decide +kernel, by decide +kernel⟩

def f329 : Formula := .mul f278 f328
def num329 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x600000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den329 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel329 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p329 : Fraction := ⟨num329, den329⟩
theorem h329 : Reduced f329 p329 := .mul h278 h328 ⟨cancel329, by decide +kernel, by decide +kernel⟩

def f330 : Formula := .div f329 f280
def num330 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x600000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den330 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel330 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p330 : Fraction := ⟨num330, den330⟩
theorem h330 : Reduced f330 p330 := .div h329 h280 [.integer (4), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel330, by decide +kernel, by decide +kernel⟩

def f331 : Formula := .neg f330
def p331 : Fraction := p330.neg
theorem h331 : Reduced f331 p331 := .neg h330

def f332 : Formula := .add f327 f331
def num332 : Expr := .bands [
  ⟨0, 0, 5, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 7, 0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 5, 0x70000000000000000000000000006000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den332 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel332 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def p332 : Fraction := ⟨num332, den332⟩
theorem h332 : Reduced f332 p332 := .add h327 h331 ⟨cancel332, by decide +kernel, by decide +kernel⟩

def f333 : Formula := .neg f283
def p333 : Fraction := p283.neg
theorem h333 : Reduced f333 p333 := .neg h283

def f334 : Formula := .add f332 f333
def num334 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den334 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel334 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def p334 : Fraction := ⟨num334, den334⟩
theorem h334 : Reduced f334 p334 := .add h332 h333 ⟨cancel334, by decide +kernel, by decide +kernel⟩

def f335 : Formula := .mul f77 f77
def num335 : Expr := .bands [

]

def den335 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel335 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p335 : Fraction := ⟨num335, den335⟩
theorem h335 : Reduced f335 p335 := .mul h77 h77 ⟨cancel335, by decide +kernel, by decide +kernel⟩

def f336 : Formula := .mul f251 f335
def num336 : Expr := .bands [

]

def den336 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel336 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p336 : Fraction := ⟨num336, den336⟩
theorem h336 : Reduced f336 p336 := .mul h251 h335 ⟨cancel336, by decide +kernel, by decide +kernel⟩

def f337 : Formula := .div f336 f256
def num337 : Expr := .bands [

]

def den337 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel337 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def p337 : Fraction := ⟨num337, den337⟩
theorem h337 : Reduced f337 p337 := .div h336 h256 [.integer (4), .radius, .radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel337, by decide +kernel, by decide +kernel⟩

def f338 : Formula := .mul f14 f52
def num338 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den338 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel338 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p338 : Fraction := ⟨num338, den338⟩
theorem h338 : Reduced f338 p338 := .mul h14 h52 ⟨cancel338, by decide +kernel, by decide +kernel⟩

def f339 : Formula := .mul f338 f298
def num339 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x1, 1⟩
]

def den339 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel339 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p339 : Fraction := ⟨num339, den339⟩
theorem h339 : Reduced f339 p339 := .mul h338 h298 ⟨cancel339, by decide +kernel, by decide +kernel⟩

def f340 : Formula := .mul f1 f52
def num340 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den340 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel340 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p340 : Fraction := ⟨num340, den340⟩
theorem h340 : Reduced f340 p340 := .mul h1 h52 ⟨cancel340, by decide +kernel, by decide +kernel⟩

def f341 : Formula := .mul f340 f306
def num341 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den341 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x2, 0x0, 1⟩
]

def cancel341 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p341 : Fraction := ⟨num341, den341⟩
theorem h341 : Reduced f341 p341 := .mul h340 h306 ⟨cancel341, by decide +kernel, by decide +kernel⟩

def f342 : Formula := .add f339 f341
def num342 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den342 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x4, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel342 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x18, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0xc, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def p342 : Fraction := ⟨num342, den342⟩
theorem h342 : Reduced f342 p342 := .add h339 h341 ⟨cancel342, by decide +kernel, by decide +kernel⟩

def f343 : Formula := .mul f193 f193
def num343 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den343 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel343 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p343 : Fraction := ⟨num343, den343⟩
theorem h343 : Reduced f343 p343 := .mul h193 h193 ⟨cancel343, by decide +kernel, by decide +kernel⟩

def f344 : Formula := .add f342 f343
def num344 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000002, 0x0, 1⟩
]

def den344 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x4, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel344 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p344 : Fraction := ⟨num344, den344⟩
theorem h344 : Reduced f344 p344 := .add h342 h343 ⟨cancel344, by decide +kernel, by decide +kernel⟩

def f345 : Formula := .mul f258 f344
def num345 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000001000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den345 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel345 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p345 : Fraction := ⟨num345, den345⟩
theorem h345 : Reduced f345 p345 := .mul h258 h344 ⟨cancel345, by decide +kernel, by decide +kernel⟩

def f346 : Formula := .div f345 f81
def num346 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000001000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den346 : Expr := .bands [
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel346 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p346 : Fraction := ⟨num346, den346⟩
theorem h346 : Reduced f346 p346 := .div h345 h81 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel346, by decide +kernel, by decide +kernel⟩

def f347 : Formula := .add f337 f346
def num347 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000001000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den347 : Expr := .bands [
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel347 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p347 : Fraction := ⟨num347, den347⟩
theorem h347 : Reduced f347 p347 := .add h337 h346 ⟨cancel347, by decide +kernel, by decide +kernel⟩

def f348 : Formula := .mul f13 f52
def num348 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den348 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel348 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p348 : Fraction := ⟨num348, den348⟩
theorem h348 : Reduced f348 p348 := .mul h13 h52 ⟨cancel348, by decide +kernel, by decide +kernel⟩

def f349 : Formula := .mul f348 f77
def num349 : Expr := .bands [

]

def den349 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel349 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p349 : Fraction := ⟨num349, den349⟩
theorem h349 : Reduced f349 p349 := .mul h348 h77 ⟨cancel349, by decide +kernel, by decide +kernel⟩

def f350 : Formula := .mul f52 f193
def num350 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den350 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel350 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p350 : Fraction := ⟨num350, den350⟩
theorem h350 : Reduced f350 p350 := .mul h52 h193 ⟨cancel350, by decide +kernel, by decide +kernel⟩

def f351 : Formula := .neg f350
def p351 : Fraction := p350.neg
theorem h351 : Reduced f351 p351 := .neg h350

def f352 : Formula := .add f349 f351
def num352 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den352 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel352 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p352 : Fraction := ⟨num352, den352⟩
theorem h352 : Reduced f352 p352 := .add h349 h351 ⟨cancel352, by decide +kernel, by decide +kernel⟩

def f353 : Formula := .mul f258 f352
def num353 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den353 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel353 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p353 : Fraction := ⟨num353, den353⟩
theorem h353 : Reduced f353 p353 := .mul h258 h352 ⟨cancel353, by decide +kernel, by decide +kernel⟩

def f354 : Formula := .div f353 f106
def num354 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den354 : Expr := .bands [
  ⟨7, 0, 1, 0x2, 0x0, 1⟩
]

def cancel354 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p354 : Fraction := ⟨num354, den354⟩
theorem h354 : Reduced f354 p354 := .div h353 h106 [.radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel354, by decide +kernel, by decide +kernel⟩

def f355 : Formula := .add f347 f354
def num355 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den355 : Expr := .bands [
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel355 : Expr := .bands [
  ⟨8, 0, 1, 0x2, 0x0, 1⟩
]

def p355 : Fraction := ⟨num355, den355⟩
theorem h355 : Reduced f355 p355 := .add h347 h354 ⟨cancel355, by decide +kernel, by decide +kernel⟩

def f356 : Formula := .mul f271 f77
def num356 : Expr := .bands [

]

def den356 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel356 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p356 : Fraction := ⟨num356, den356⟩
theorem h356 : Reduced f356 p356 := .mul h271 h77 ⟨cancel356, by decide +kernel, by decide +kernel⟩

def f357 : Formula := .mul f356 f298
def num357 : Expr := .bands [

]

def den357 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel357 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p357 : Fraction := ⟨num357, den357⟩
theorem h357 : Reduced f357 p357 := .mul h356 h298 ⟨cancel357, by decide +kernel, by decide +kernel⟩

def f358 : Formula := .div f357 f254
def num358 : Expr := .bands [

]

def den358 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel358 : Expr := .bands [
  ⟨6, 0, 1, 0x1, 0x0, 1⟩
]

def p358 : Fraction := ⟨num358, den358⟩
theorem h358 : Reduced f358 p358 := .div h357 h254 [.radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel358, by decide +kernel, by decide +kernel⟩

def f359 : Formula := .add f355 f358
def num359 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den359 : Expr := .bands [
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel359 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p359 : Fraction := ⟨num359, den359⟩
theorem h359 : Reduced f359 p359 := .add h355 h358 ⟨cancel359, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
