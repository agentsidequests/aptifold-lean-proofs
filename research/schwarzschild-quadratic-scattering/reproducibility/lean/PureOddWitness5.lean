import PureOddWitness4

namespace SchwarzschildMixtures.PureOddWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f225 : Formula := .div f0 f41
def num225 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den225 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel225 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p225 : Fraction := ⟨num225, den225⟩
theorem h225 : Reduced f225 p225 := .div h0 h41 [.integer (2), .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel225, by decide +kernel, by decide +kernel⟩

def f226 : Formula := .neg f225
def p226 : Fraction := p225.neg
theorem h226 : Reduced f226 p226 := .neg h225

def f227 : Formula := .neg f20
def p227 : Fraction := p20.neg
theorem h227 : Reduced f227 p227 := .neg h20

def f228 : Formula := .mul f227 f115
def num228 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den228 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel228 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p228 : Fraction := ⟨num228, den228⟩
theorem h228 : Reduced f228 p228 := .mul h227 h115 ⟨cancel228, by decide +kernel, by decide +kernel⟩

def f229 : Formula := .mul f106 f54
def num229 : Expr := .bands [
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den229 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel229 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p229 : Fraction := ⟨num229, den229⟩
theorem h229 : Reduced f229 p229 := .mul h106 h54 ⟨cancel229, by decide +kernel, by decide +kernel⟩

def f230 : Formula := .mul f208 f53
def num230 : Expr := .bands [
  ⟨2, 0, 1, 0x5, 0x0, 1⟩
]

def den230 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel230 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p230 : Fraction := ⟨num230, den230⟩
theorem h230 : Reduced f230 p230 := .mul h208 h53 ⟨cancel230, by decide +kernel, by decide +kernel⟩

def f231 : Formula := .mul f230 f115
def num231 : Expr := .bands [
  ⟨2, 0, 3, 0x500000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den231 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel231 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p231 : Fraction := ⟨num231, den231⟩
theorem h231 : Reduced f231 p231 := .mul h230 h115 ⟨cancel231, by decide +kernel, by decide +kernel⟩

def f232 : Formula := .neg f231
def p232 : Fraction := p231.neg
theorem h232 : Reduced f232 p232 := .neg h231

def f233 : Formula := .add f229 f232
def num233 : Expr := .bands [
  ⟨2, 0, 3, 0x0, 0x500000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den233 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel233 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p233 : Fraction := ⟨num233, den233⟩
theorem h233 : Reduced f233 p233 := .add h229 h232 ⟨cancel233, by decide +kernel, by decide +kernel⟩

def f234 : Formula := .mul f222 f2
def num234 : Expr := .bands [
  ⟨2, 0, 2, 0x40000000000000000000000000000, 0x0, 1⟩
]

def den234 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel234 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p234 : Fraction := ⟨num234, den234⟩
theorem h234 : Reduced f234 p234 := .mul h222 h2 ⟨cancel234, by decide +kernel, by decide +kernel⟩

def f235 : Formula := .neg f234
def p235 : Fraction := p234.neg
theorem h235 : Reduced f235 p235 := .neg h234

def f236 : Formula := .add f233 f235
def num236 : Expr := .bands [
  ⟨2, 0, 3, 0x0, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den236 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel236 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p236 : Fraction := ⟨num236, den236⟩
theorem h236 : Reduced f236 p236 := .add h233 h235 ⟨cancel236, by decide +kernel, by decide +kernel⟩

def f237 : Formula := .add f236 f53
def num237 : Expr := .bands [
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den237 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel237 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p237 : Fraction := ⟨num237, den237⟩
theorem h237 : Reduced f237 p237 := .add h236 h53 ⟨cancel237, by decide +kernel, by decide +kernel⟩

def f238 : Formula := .integer (10)
def p238 : Fraction := .polynomial (.constant (10))
theorem h238 : Reduced f238 p238 := .integer (10)

def f239 : Formula := .mul f238 f18
def num239 : Expr := .bands [
  ⟨1, 0, 1, 0xa, 0x0, 1⟩
]

def den239 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel239 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p239 : Fraction := ⟨num239, den239⟩
theorem h239 : Reduced f239 p239 := .mul h238 h18 ⟨cancel239, by decide +kernel, by decide +kernel⟩

def f240 : Formula := .mul f239 f115
def num240 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den240 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel240 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p240 : Fraction := ⟨num240, den240⟩
theorem h240 : Reduced f240 p240 := .mul h239 h115 ⟨cancel240, by decide +kernel, by decide +kernel⟩

def f241 : Formula := .add f237 f240
def num241 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den241 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel241 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p241 : Fraction := ⟨num241, den241⟩
theorem h241 : Reduced f241 p241 := .add h237 h240 ⟨cancel241, by decide +kernel, by decide +kernel⟩

def f242 : Formula := .mul f28 f18
def num242 : Expr := .bands [
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def den242 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel242 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p242 : Fraction := ⟨num242, den242⟩
theorem h242 : Reduced f242 p242 := .mul h28 h18 ⟨cancel242, by decide +kernel, by decide +kernel⟩

def f243 : Formula := .mul f242 f2
def num243 : Expr := .bands [
  ⟨1, 0, 2, 0x80000000000000000000000000000, 0x0, 1⟩
]

def den243 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel243 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p243 : Fraction := ⟨num243, den243⟩
theorem h243 : Reduced f243 p243 := .mul h242 h2 ⟨cancel243, by decide +kernel, by decide +kernel⟩

def f244 : Formula := .add f241 f243
def num244 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den244 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel244 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p244 : Fraction := ⟨num244, den244⟩
theorem h244 : Reduced f244 p244 := .add h241 h243 ⟨cancel244, by decide +kernel, by decide +kernel⟩

def f245 : Formula := .integer (26)
def p245 : Fraction := .polynomial (.constant (26))
theorem h245 : Reduced f245 p245 := .integer (26)

def f246 : Formula := .mul f245 f18
def num246 : Expr := .bands [
  ⟨1, 0, 1, 0x1a, 0x0, 1⟩
]

def den246 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel246 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p246 : Fraction := ⟨num246, den246⟩
theorem h246 : Reduced f246 p246 := .mul h245 h18 ⟨cancel246, by decide +kernel, by decide +kernel⟩

def f247 : Formula := .neg f246
def p247 : Fraction := p246.neg
theorem h247 : Reduced f247 p247 := .neg h246

def f248 : Formula := .add f244 f247
def num248 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x1a, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den248 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel248 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p248 : Fraction := ⟨num248, den248⟩
theorem h248 : Reduced f248 p248 := .add h244 h247 ⟨cancel248, by decide +kernel, by decide +kernel⟩

def f249 : Formula := .integer (48)
def p249 : Fraction := .polynomial (.constant (48))
theorem h249 : Reduced f249 p249 := .integer (48)

def f250 : Formula := .add f248 f249
def num250 : Expr := .bands [
  ⟨0, 0, 1, 0x30, 0x0, 1⟩,
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x1a, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den250 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel250 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p250 : Fraction := ⟨num250, den250⟩
theorem h250 : Reduced f250 p250 := .add h248 h249 ⟨cancel250, by decide +kernel, by decide +kernel⟩

def f251 : Formula := .mul f228 f250
def num251 : Expr := .bands [
  ⟨0, 0, 3, 0x6000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x140000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x1c00000000000000000000000000000000000000000000000000000000, 0x140000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den251 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel251 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p251 : Fraction := ⟨num251, den251⟩
theorem h251 : Reduced f251 p251 := .mul h228 h250 ⟨cancel251, by decide +kernel, by decide +kernel⟩

def f252 : Formula := .mul f251 f104
def num252 : Expr := .bands [
  ⟨4, 2, 3, 0x0, 0x3000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 5, 0x1a00000000000000000000000000000000000000000000000000000000, 0xa0000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨6, 2, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨8, 4, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den252 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel252 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p252 : Fraction := ⟨num252, den252⟩
theorem h252 : Reduced f252 p252 := .mul h251 h104 ⟨cancel252, by decide +kernel, by decide +kernel⟩

def f253 : Formula := .mul f106 f18
def num253 : Expr := .bands [
  ⟨5, 0, 1, 0x1, 0x0, 1⟩
]

def den253 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel253 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p253 : Fraction := ⟨num253, den253⟩
theorem h253 : Reduced f253 p253 := .mul h106 h18 ⟨cancel253, by decide +kernel, by decide +kernel⟩

def f254 : Formula := .mul f253 f18
def num254 : Expr := .bands [
  ⟨6, 0, 1, 0x1, 0x0, 1⟩
]

def den254 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel254 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p254 : Fraction := ⟨num254, den254⟩
theorem h254 : Reduced f254 p254 := .mul h253 h18 ⟨cancel254, by decide +kernel, by decide +kernel⟩

def f255 : Formula := .mul f254 f18
def num255 : Expr := .bands [
  ⟨7, 0, 1, 0x1, 0x0, 1⟩
]

def den255 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel255 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p255 : Fraction := ⟨num255, den255⟩
theorem h255 : Reduced f255 p255 := .mul h254 h18 ⟨cancel255, by decide +kernel, by decide +kernel⟩

def f256 : Formula := .mul f67 f255
def num256 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def den256 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel256 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p256 : Fraction := ⟨num256, den256⟩
theorem h256 : Reduced f256 p256 := .mul h67 h255 ⟨cancel256, by decide +kernel, by decide +kernel⟩

def f257 : Formula := .div f252 f256
def num257 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x3000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 5, 0x1a00000000000000000000000000000000000000000000000000000000, 0xa0000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 2, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 4, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den257 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel257 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p257 : Fraction := ⟨num257, den257⟩
theorem h257 : Reduced f257 p257 := .div h252 h256 [.integer (4), .radius, .radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel257, by decide +kernel, by decide +kernel⟩

def f258 : Formula := .mul f20 f115
def num258 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den258 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel258 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p258 : Fraction := ⟨num258, den258⟩
theorem h258 : Reduced f258 p258 := .mul h20 h115 ⟨cancel258, by decide +kernel, by decide +kernel⟩

def f259 : Formula := .add f179 f196
def num259 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x2, 0x0, 1⟩
]

def den259 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel259 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p259 : Fraction := ⟨num259, den259⟩
theorem h259 : Reduced f259 p259 := .add h179 h196 ⟨cancel259, by decide +kernel, by decide +kernel⟩

def f260 : Formula := .add f259 f132
def num260 : Expr := .bands [
  ⟨0, 0, 1, 0x80, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x30000000000000000000000000003000000000000000000000000000a0, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000003c00000000000000000000000000380000000000000000000000000040, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000001800000000000000000000000000140000000000000000000000000008, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000300000000000000000000000000020000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x20, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000018, 1⟩,
  ⟨6, 2, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨8, 4, 1, 0x1, 0x0, 1⟩
]

def den260 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel260 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p260 : Fraction := ⟨num260, den260⟩
theorem h260 : Reduced f260 p260 := .add h259 h132 ⟨cancel260, by decide +kernel, by decide +kernel⟩

def f261 : Formula := .mul f258 f260
def num261 : Expr := .bands [
  ⟨0, 0, 3, 0x8000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x30000000000000000000000000003000000000000000000000000000a000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x40000000000000000000000000008000000000000000000000000003c0000000000000000000000000038000000000000000000000000004000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 7, 0x0, 0x4000000000000000000000000000800000000000000000000000000180000000000000000000000000014000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 0, 7, 0x1000000000000000000000000000200000000000000000000000000030000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x2000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x0, 0x40000000000000000000000000004000000000000000000000000001800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨6, 2, 5, 0x20000000000000000000000000002000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den261 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel261 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p261 : Fraction := ⟨num261, den261⟩
theorem h261 : Reduced f261 p261 := .mul h258 h260 ⟨cancel261, by decide +kernel, by decide +kernel⟩

def f262 : Formula := .div f261 f81
def num262 : Expr := .bands [
  ⟨0, 0, 3, 0x8000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x30000000000000000000000000003000000000000000000000000000a000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x40000000000000000000000000008000000000000000000000000003c0000000000000000000000000038000000000000000000000000004000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 7, 0x0, 0x4000000000000000000000000000800000000000000000000000000180000000000000000000000000014000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 0, 7, 0x1000000000000000000000000000200000000000000000000000000030000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x2000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x0, 0x40000000000000000000000000004000000000000000000000000001800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨6, 2, 5, 0x20000000000000000000000000002000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den262 : Expr := .bands [
  ⟨7, 0, 1, 0x0, 0x20, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel262 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p262 : Fraction := ⟨num262, den262⟩
theorem h262 : Reduced f262 p262 := .div h261 h81 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel262, by decide +kernel, by decide +kernel⟩

def f263 : Formula := .add f257 f262
def num263 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x4000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x180000000000000000000000000018000000000000000000000000003000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 7, 0x0, 0x2000000000000000000000000000400000000000000000000000000120000000000000000000000000010000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000200000000000000000000000000030000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x70000000000000000000000000006000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den263 : Expr := .bands [
  ⟨7, 0, 1, 0x10, 0x0, 1⟩
]

def cancel263 : Expr := .bands [
  ⟨3, 0, 1, 0x40, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x40, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def p263 : Fraction := ⟨num263, den263⟩
theorem h263 : Reduced f263 p263 := .add h257 h262 ⟨cancel263, by decide +kernel, by decide +kernel⟩

def f264 : Formula := .neg f138
def p264 : Fraction := p138.neg
theorem h264 : Reduced f264 p264 := .neg h138

def f265 : Formula := .add f137 f264
def num265 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x0, 0x2, 1⟩
]

def den265 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel265 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p265 : Fraction := ⟨num265, den265⟩
theorem h265 : Reduced f265 p265 := .add h137 h264 ⟨cancel265, by decide +kernel, by decide +kernel⟩

def f266 : Formula := .mul f258 f265
def num266 : Expr := .bands [
  ⟨0, 0, 3, 0x1000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x40000000000000000000000000004000000000000000000000000001000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000004000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den266 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel266 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p266 : Fraction := ⟨num266, den266⟩
theorem h266 : Reduced f266 p266 := .mul h258 h265 ⟨cancel266, by decide +kernel, by decide +kernel⟩

def f267 : Formula := .div f266 f106
def num267 : Expr := .bands [
  ⟨0, 0, 3, 0x1000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x40000000000000000000000000004000000000000000000000000001000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000004000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den267 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def cancel267 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p267 : Fraction := ⟨num267, den267⟩
theorem h267 : Reduced f267 p267 := .div h266 h106 [.radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel267, by decide +kernel, by decide +kernel⟩

def f268 : Formula := .add f263 f267
def num268 : Expr := .bands [
  ⟨0, 0, 5, 0x80000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 7, 0x800000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000400000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x1800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 5, 0x70000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x500000000000000000000000000000000000000000000000000000000, 1⟩
]

def den268 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel268 : Expr := .bands [
  ⟨8, 0, 1, 0x4, 0x0, 1⟩
]

def p268 : Fraction := ⟨num268, den268⟩
theorem h268 : Reduced f268 p268 := .add h263 h267 ⟨cancel268, by decide +kernel, by decide +kernel⟩

def f269 : Formula := .mul f1 f115
def num269 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den269 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel269 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p269 : Fraction := ⟨num269, den269⟩
theorem h269 : Reduced f269 p269 := .mul h1 h115 ⟨cancel269, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.PureOddWitness
