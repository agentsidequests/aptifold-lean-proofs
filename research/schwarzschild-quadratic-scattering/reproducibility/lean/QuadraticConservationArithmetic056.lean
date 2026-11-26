import QuadraticConservationArithmetic055

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2240 : Formula := .neg f2239
def p2240 : Fraction := p2239.neg
theorem h2240 : Reduced f2240 p2240 := .neg h2239

def f2241 : Formula := .add f2236 f2240
def num2241 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000020000000000000000000000000001, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x1, 1⟩
]

def den2241 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2241 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2241 : Fraction := ⟨num2241, den2241⟩
theorem h2241 : Reduced f2241 p2241 := .add h2236 h2240 ⟨cancel2241, by decide +kernel, by decide +kernel⟩

def f2242 : Formula := .mul f2232 f2241
def num2242 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000020000000000000000000000000001, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x1, 1⟩
]

def den2242 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x4, 1⟩,
  ⟨6, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2242 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2242 : Fraction := ⟨num2242, den2242⟩
theorem h2242 : Reduced f2242 p2242 := .mul h2232 h2241 ⟨cancel2242, by decide +kernel, by decide +kernel⟩

def f2243 : Formula := .mul f2242 f491
def num2243 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000020000000000000000000000000001, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x1, 1⟩
]

def den2243 : Expr := .bands [
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2243 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2243 : Fraction := ⟨num2243, den2243⟩
theorem h2243 : Reduced f2243 p2243 := .mul h2242 h491 ⟨cancel2243, by decide +kernel, by decide +kernel⟩

def f2244 : Formula := .mul f2243 f2166
def num2244 : Expr := .bands [
  ⟨0, 1, 1, 0x8, 0x0, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000040000000000000000000000000000, 0x2, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000020000000000000000000000000001, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den2244 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2244 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2244 : Fraction := ⟨num2244, den2244⟩
theorem h2244 : Reduced f2244 p2244 := .mul h2243 h2166 ⟨cancel2244, by decide +kernel, by decide +kernel⟩

def f2245 : Formula := .mul f273 f5
def num2245 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2245 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2245 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2245 : Fraction := ⟨num2245, den2245⟩
theorem h2245 : Reduced f2245 p2245 := .mul h273 h5 ⟨cancel2245, by decide +kernel, by decide +kernel⟩

def f2246 : Formula := .mul f2245 f2229
def num2246 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2246 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2246 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2246 : Fraction := ⟨num2246, den2246⟩
theorem h2246 : Reduced f2246 p2246 := .mul h2245 h2229 ⟨cancel2246, by decide +kernel, by decide +kernel⟩

def f2247 : Formula := .mul f2193 f2166
def num2247 : Expr := .bands [
  ⟨0, 1, 1, 0x10, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000010, 1⟩,
  ⟨2, 1, 3, 0x400000000000000000000000000040000000000000000000000000004, 0x0, 1⟩,
  ⟨3, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x8, 0x0, 1⟩,
  ⟨5, 3, 1, 0x0, 0x3, 1⟩
]

def den2247 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x30, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x18, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2247 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2247 : Fraction := ⟨num2247, den2247⟩
theorem h2247 : Reduced f2247 p2247 := .mul h2193 h2166 ⟨cancel2247, by decide +kernel, by decide +kernel⟩

def f2248 : Formula := .mul f1 f2166
def num2248 : Expr := .bands [
  ⟨2, 2, 1, 0x0, 0x1, 1⟩
]

def den2248 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2248 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2248 : Fraction := ⟨num2248, den2248⟩
theorem h2248 : Reduced f2248 p2248 := .mul h1 h2166 ⟨cancel2248, by decide +kernel, by decide +kernel⟩

def f2249 : Formula := .mul f2248 f2178
def num2249 : Expr := .bands [
  ⟨3, 3, 1, 0x0, 0x4, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den2249 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x30, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x18, 1⟩,
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2249 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2249 : Fraction := ⟨num2249, den2249⟩
theorem h2249 : Reduced f2249 p2249 := .mul h2248 h2178 ⟨cancel2249, by decide +kernel, by decide +kernel⟩

def f2250 : Formula := .add f2247 f2249
def num2250 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x8, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x2, 1⟩
]

def den2250 : Expr := .bands [
  ⟨1, 0, 1, 0x10, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x10, 1⟩,
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2250 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x80, 1⟩,
  ⟨2, 0, 1, 0x60, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p2250 : Fraction := ⟨num2250, den2250⟩
theorem h2250 : Reduced f2250 p2250 := .add h2247 h2249 ⟨cancel2250, by decide +kernel, by decide +kernel⟩

def f2251 : Formula := .mul f2246 f2250
def num2251 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x8, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x2, 1⟩
]

def den2251 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2251 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2251 : Fraction := ⟨num2251, den2251⟩
theorem h2251 : Reduced f2251 p2251 := .mul h2246 h2250 ⟨cancel2251, by decide +kernel, by decide +kernel⟩

def f2252 : Formula := .add f2244 f2251
def num2252 : Expr := .bands [
  ⟨0, 1, 3, 0x400000000000000000000000000060000000000000000000000000002, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000030000000000000000000000000001, 1⟩,
  ⟨3, 3, 1, 0x0, 0x1, 1⟩
]

def den2252 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2252 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2252 : Fraction := ⟨num2252, den2252⟩
theorem h2252 : Reduced f2252 p2252 := .add h2244 h2251 ⟨cancel2252, by decide +kernel, by decide +kernel⟩

def f2253 : Formula := .mul f5 f1
def num2253 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2253 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2253 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2253 : Fraction := ⟨num2253, den2253⟩
theorem h2253 : Reduced f2253 p2253 := .mul h5 h1 ⟨cancel2253, by decide +kernel, by decide +kernel⟩

def f2254 : Formula := .mul f2253 f2228
def num2254 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2254 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2254 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2254 : Fraction := ⟨num2254, den2254⟩
theorem h2254 : Reduced f2254 p2254 := .mul h2253 h2228 ⟨cancel2254, by decide +kernel, by decide +kernel⟩

def f2255 : Formula := .mul f2254 f2228
def num2255 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2255 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2255 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2255 : Fraction := ⟨num2255, den2255⟩
theorem h2255 : Reduced f2255 p2255 := .mul h2254 h2228 ⟨cancel2255, by decide +kernel, by decide +kernel⟩

def f2256 : Formula := .mul f2255 f2166
def num2256 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x1, 1⟩
]

def den2256 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2256 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2256 : Fraction := ⟨num2256, den2256⟩
theorem h2256 : Reduced f2256 p2256 := .mul h2255 h2166 ⟨cancel2256, by decide +kernel, by decide +kernel⟩

def f2257 : Formula := .mul f2256 f2166
def num2257 : Expr := .bands [
  ⟨0, 3, 1, 0x1, 0x0, 1⟩
]

def den2257 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2257 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2257 : Fraction := ⟨num2257, den2257⟩
theorem h2257 : Reduced f2257 p2257 := .mul h2256 h2166 ⟨cancel2257, by decide +kernel, by decide +kernel⟩

def f2258 : Formula := .neg f2257
def p2258 : Fraction := p2257.neg
theorem h2258 : Reduced f2258 p2258 := .neg h2257

def f2259 : Formula := .add f2252 f2258
def num2259 : Expr := .bands [
  ⟨0, 1, 3, 0x400000000000000000000000000060000000000000000000000000002, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000030000000000000000000000000001, 1⟩,
  ⟨3, 3, 1, 0x0, 0x3, 1⟩
]

def den2259 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2259 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p2259 : Fraction := ⟨num2259, den2259⟩
theorem h2259 : Reduced f2259 p2259 := .add h2252 h2258 ⟨cancel2259, by decide +kernel, by decide +kernel⟩

def f2260 : Formula := .mul f1 f2228
def num2260 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2260 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2260 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2260 : Fraction := ⟨num2260, den2260⟩
theorem h2260 : Reduced f2260 p2260 := .mul h1 h2228 ⟨cancel2260, by decide +kernel, by decide +kernel⟩

def f2261 : Formula := .mul f2260 f36
def num2261 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2261 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2261 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2261 : Fraction := ⟨num2261, den2261⟩
theorem h2261 : Reduced f2261 p2261 := .mul h2260 h36 ⟨cancel2261, by decide +kernel, by decide +kernel⟩

def f2262 : Formula := .mul f2261 f491
def num2262 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2262 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2262 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2262 : Fraction := ⟨num2262, den2262⟩
theorem h2262 : Reduced f2262 p2262 := .mul h2261 h491 ⟨cancel2262, by decide +kernel, by decide +kernel⟩

def f2263 : Formula := .mul f2262 f491
def num2263 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2263 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2263 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2263 : Fraction := ⟨num2263, den2263⟩
theorem h2263 : Reduced f2263 p2263 := .mul h2262 h491 ⟨cancel2263, by decide +kernel, by decide +kernel⟩

def f2264 : Formula := .add f2259 f2263
def num2264 : Expr := .bands [
  ⟨0, 1, 1, 0x8, 0x0, 1⟩,
  ⟨1, 1, 3, 0x400000000000000000000000000060000000000000000000000000000, 0x6, 1⟩,
  ⟨2, 1, 3, 0x1, 0x200000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x3, 1⟩
]

def den2264 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2264 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def p2264 : Fraction := ⟨num2264, den2264⟩
theorem h2264 : Reduced f2264 p2264 := .add h2259 h2263 ⟨cancel2264, by decide +kernel, by decide +kernel⟩

def f2265 : Formula := .mul f273 f1
def num2265 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2265 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2265 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2265 : Fraction := ⟨num2265, den2265⟩
theorem h2265 : Reduced f2265 p2265 := .mul h273 h1 ⟨cancel2265, by decide +kernel, by decide +kernel⟩

def f2266 : Formula := .mul f2265 f32
def num2266 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2266 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2266 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2266 : Fraction := ⟨num2266, den2266⟩
theorem h2266 : Reduced f2266 p2266 := .mul h2265 h32 ⟨cancel2266, by decide +kernel, by decide +kernel⟩

def f2267 : Formula := .mul f2266 f36
def num2267 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2267 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2267 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2267 : Fraction := ⟨num2267, den2267⟩
theorem h2267 : Reduced f2267 p2267 := .mul h2266 h36 ⟨cancel2267, by decide +kernel, by decide +kernel⟩

def f2268 : Formula := .mul f2267 f491
def num2268 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2268 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2268 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2268 : Fraction := ⟨num2268, den2268⟩
theorem h2268 : Reduced f2268 p2268 := .mul h2267 h491 ⟨cancel2268, by decide +kernel, by decide +kernel⟩

def f2269 : Formula := .mul f2268 f2185
def num2269 : Expr := .bands [
  ⟨0, 1, 1, 0x8, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den2269 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2269 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2269 : Fraction := ⟨num2269, den2269⟩
theorem h2269 : Reduced f2269 p2269 := .mul h2268 h2185 ⟨cancel2269, by decide +kernel, by decide +kernel⟩

def f2270 : Formula := .neg f2269
def p2270 : Fraction := p2269.neg
theorem h2270 : Reduced f2270 p2270 := .neg h2269

def f2271 : Formula := .add f2264 f2270
def num2271 : Expr := .bands [
  ⟨0, 1, 3, 0x600000000000000000000000000080000000000000000000000000000, 0x2, 1⟩,
  ⟨1, 1, 3, 0x1, 0x300000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 3, 1, 0x0, 0x4, 1⟩
]

def den2271 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2271 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2271 : Fraction := ⟨num2271, den2271⟩
theorem h2271 : Reduced f2271 p2271 := .add h2264 h2270 ⟨cancel2271, by decide +kernel, by decide +kernel⟩

def f2272 : Formula := .mul f2138 f2271
def num2272 : Expr := .bands [
  ⟨0, 1, 5, 0x60000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2272 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2272 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2272 : Fraction := ⟨num2272, den2272⟩
theorem h2272 : Reduced f2272 p2272 := .mul h2138 h2271 ⟨cancel2272, by decide +kernel, by decide +kernel⟩

def f2273 : Formula := .dr f2272
def num2273 : Expr := .bands [
  ⟨0, 1, 5, 0x240000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xc00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0xc00000000000000000000000000000000000000000000000000000000, 0x240000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 1, 5, 0x9000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2273 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2273 : Expr := .bands [
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def p2273 : Fraction := ⟨num2273, den2273⟩
theorem h2273 : Reduced f2273 p2273 := .dr h2272 ⟨cancel2273, by decide +kernel, by decide +kernel⟩

def f2274 : Formula := .add f491 f2183
def num2274 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2274 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2274 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2274 : Fraction := ⟨num2274, den2274⟩
theorem h2274 : Reduced f2274 p2274 := .add h491 h2183 ⟨cancel2274, by decide +kernel, by decide +kernel⟩

def f2275 : Formula := .mul f2242 f2274
def num2275 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000040000000000000000000000000000, 0xa, 1⟩,
  ⟨2, 0, 3, 0x1, 0x300000000000000000000000000060000000000000000000000000000, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000020000000000000000000000000001, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩,
  ⟨5, 2, 1, 0x0, 0x1, 1⟩
]

def den2275 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x8, 1⟩,
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2275 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2275 : Fraction := ⟨num2275, den2275⟩
theorem h2275 : Reduced f2275 p2275 := .mul h2242 h2274 ⟨cancel2275, by decide +kernel, by decide +kernel⟩

def f2276 : Formula := .add f2166 f28
def num2276 : Expr := .bands [
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den2276 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2276 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2276 : Fraction := ⟨num2276, den2276⟩
theorem h2276 : Reduced f2276 p2276 := .add h2166 h28 ⟨cancel2276, by decide +kernel, by decide +kernel⟩

def f2277 : Formula := .mul f2275 f2276
def num2277 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x8, 1⟩,
  ⟨1, 1, 3, 0xa, 0x200000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 1, 3, 0x300000000000000000000000000060000000000000000000000000000, 0x1, 1⟩,
  ⟨3, 1, 3, 0x0, 0x100000000000000000000000000020000000000000000000000000001, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩,
  ⟨5, 3, 1, 0x1, 0x0, 1⟩
]

def den2277 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2277 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2277 : Fraction := ⟨num2277, den2277⟩
theorem h2277 : Reduced f2277 p2277 := .mul h2275 h2276 ⟨cancel2277, by decide +kernel, by decide +kernel⟩

def f2278 : Formula := .dr f2191
def num2278 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩
]

def den2278 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2278 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2278 : Fraction := ⟨num2278, den2278⟩
theorem h2278 : Reduced f2278 p2278 := .dr h2191 ⟨cancel2278, by decide +kernel, by decide +kernel⟩

def f2279 : Formula := .mul f2185 f101
def num2279 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2279 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2279 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2279 : Fraction := ⟨num2279, den2279⟩
theorem h2279 : Reduced f2279 p2279 := .mul h2185 h101 ⟨cancel2279, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
