import QuadraticConservationArithmetic057

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2320 : Formula := .mul f2319 f28
def num2320 : Expr := .bands [

]

def den2320 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2320 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2320 : Fraction := ⟨num2320, den2320⟩
theorem h2320 : Reduced f2320 p2320 := .mul h2319 h28 ⟨cancel2320, by decide +kernel, by decide +kernel⟩

def f2321 : Formula := .neg f2320
def p2321 : Fraction := p2320.neg
theorem h2321 : Reduced f2321 p2321 := .neg h2320

def f2322 : Formula := .add f2318 f2321
def num2322 : Expr := .bands [

]

def den2322 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2322 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2322 : Fraction := ⟨num2322, den2322⟩
theorem h2322 : Reduced f2322 p2322 := .add h2318 h2321 ⟨cancel2322, by decide +kernel, by decide +kernel⟩

def f2323 : Formula := .mul f2261 f2183
def num2323 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2323 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x4, 1⟩,
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2323 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2323 : Fraction := ⟨num2323, den2323⟩
theorem h2323 : Reduced f2323 p2323 := .mul h2261 h2183 ⟨cancel2323, by decide +kernel, by decide +kernel⟩

def f2324 : Formula := .mul f2323 f2183
def num2324 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2324 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2324 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2324 : Fraction := ⟨num2324, den2324⟩
theorem h2324 : Reduced f2324 p2324 := .mul h2323 h2183 ⟨cancel2324, by decide +kernel, by decide +kernel⟩

def f2325 : Formula := .add f2322 f2324
def num2325 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2325 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2325 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2325 : Fraction := ⟨num2325, den2325⟩
theorem h2325 : Reduced f2325 p2325 := .add h2322 h2324 ⟨cancel2325, by decide +kernel, by decide +kernel⟩

def f2326 : Formula := .mul f2267 f2183
def num2326 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2326 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x8, 1⟩,
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2326 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2326 : Fraction := ⟨num2326, den2326⟩
theorem h2326 : Reduced f2326 p2326 := .mul h2267 h2183 ⟨cancel2326, by decide +kernel, by decide +kernel⟩

def f2327 : Formula := .mul f2326 f2191
def num2327 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2327 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2327 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2327 : Fraction := ⟨num2327, den2327⟩
theorem h2327 : Reduced f2327 p2327 := .mul h2326 h2191 ⟨cancel2327, by decide +kernel, by decide +kernel⟩

def f2328 : Formula := .neg f2327
def p2328 : Fraction := p2327.neg
theorem h2328 : Reduced f2328 p2328 := .neg h2327

def f2329 : Formula := .add f2325 f2328
def num2329 : Expr := .bands [

]

def den2329 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2329 : Expr := .bands [
  ⟨8, 0, 1, 0x40, 0x0, 1⟩,
  ⟨9, 0, 1, 0x0, 0x40, 1⟩,
  ⟨10, 0, 1, 0x10, 0x0, 1⟩
]

def p2329 : Fraction := ⟨num2329, den2329⟩
theorem h2329 : Reduced f2329 p2329 := .add h2325 h2328 ⟨cancel2329, by decide +kernel, by decide +kernel⟩

def f2330 : Formula := .mul f2138 f2329
def num2330 : Expr := .bands [

]

def den2330 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2330 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2330 : Fraction := ⟨num2330, den2330⟩
theorem h2330 : Reduced f2330 p2330 := .mul h2138 h2329 ⟨cancel2330, by decide +kernel, by decide +kernel⟩

def f2331 : Formula := .neg f2330
def p2331 : Fraction := p2330.neg
theorem h2331 : Reduced f2331 p2331 := .neg h2330

def f2332 : Formula := .add f2310 f2331
def num2332 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2332 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2332 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2332 : Fraction := ⟨num2332, den2332⟩
theorem h2332 : Reduced f2332 p2332 := .add h2310 h2331 ⟨cancel2332, by decide +kernel, by decide +kernel⟩

def f2333 : Formula := .mul f2332 f82
def num2333 : Expr := .bands [
  ⟨0, 1, 5, 0xc00000000000000000000000000000000000000000000000000000000, 0x240000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 7, 0x6000000000000000000000000000e00000000000000000000000000180000000000000000000000000016000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 1, 7, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3000000000000000000000000000700000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 3, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2333 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2333 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2333 : Fraction := ⟨num2333, den2333⟩
theorem h2333 : Reduced f2333 p2333 := .mul h2332 h82 ⟨cancel2333, by decide +kernel, by decide +kernel⟩

def f2334 : Formula := .add f2273 f2333
def num2334 : Expr := .bands [
  ⟨0, 1, 7, 0x6000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 0xc000000000000000000000000001a000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 7, 0x6000000000000000000000000000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 5, 0x500000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2334 : Expr := .bands [
  ⟨3, 0, 1, 0x20, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2334 : Expr := .bands [
  ⟨5, 0, 1, 0x20, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x20, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def p2334 : Fraction := ⟨num2334, den2334⟩
theorem h2334 : Reduced f2334 p2334 := .add h2273 h2333 ⟨cancel2334, by decide +kernel, by decide +kernel⟩

def f2335 : Formula := .mul f6 f2334
def num2335 : Expr := .bands [
  ⟨0, 1, 7, 0x6000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 0xc000000000000000000000000001a000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 7, 0x6000000000000000000000000000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 5, 0x500000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2335 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2335 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2335 : Fraction := ⟨num2335, den2335⟩
theorem h2335 : Reduced f2335 p2335 := .mul h6 h2334 ⟨cancel2335, by decide +kernel, by decide +kernel⟩

def f2336 : Formula := .mul f1168 f2272
def num2336 : Expr := .bands [
  ⟨0, 1, 5, 0x200000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x9000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2336 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2336 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2336 : Fraction := ⟨num2336, den2336⟩
theorem h2336 : Reduced f2336 p2336 := .mul h1168 h2272 ⟨cancel2336, by decide +kernel, by decide +kernel⟩

def f2337 : Formula := .add f3 f158
def num2337 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x3, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2337 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2337 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2337 : Fraction := ⟨num2337, den2337⟩
theorem h2337 : Reduced f2337 p2337 := .add h3 h158 ⟨cancel2337, by decide +kernel, by decide +kernel⟩

def f2338 : Formula := .mul f273 f2337
def num2338 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x3, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2338 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2338 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2338 : Fraction := ⟨num2338, den2338⟩
theorem h2338 : Reduced f2338 p2338 := .mul h273 h2337 ⟨cancel2338, by decide +kernel, by decide +kernel⟩

def f2339 : Formula := .mul f2338 f43
def num2339 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2339 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2339 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2339 : Fraction := ⟨num2339, den2339⟩
theorem h2339 : Reduced f2339 p2339 := .mul h2338 h43 ⟨cancel2339, by decide +kernel, by decide +kernel⟩

def f2340 : Formula := .mul f2339 f2229
def num2340 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2340 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2340 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2340 : Fraction := ⟨num2340, den2340⟩
theorem h2340 : Reduced f2340 p2340 := .mul h2339 h2229 ⟨cancel2340, by decide +kernel, by decide +kernel⟩

def f2341 : Formula := .mul f2340 f32
def num2341 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2341 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2341 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2341 : Fraction := ⟨num2341, den2341⟩
theorem h2341 : Reduced f2341 p2341 := .mul h2340 h32 ⟨cancel2341, by decide +kernel, by decide +kernel⟩

def f2342 : Formula := .mul f2341 f491
def num2342 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x500000000000000000000000000050000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2342 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2342 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2342 : Fraction := ⟨num2342, den2342⟩
theorem h2342 : Reduced f2342 p2342 := .mul h2341 h491 ⟨cancel2342, by decide +kernel, by decide +kernel⟩

def f2343 : Formula := .mul f2342 f2166
def num2343 : Expr := .bands [
  ⟨0, 1, 3, 0x300000000000000000000000000030000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2343 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2343 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2343 : Fraction := ⟨num2343, den2343⟩
theorem h2343 : Reduced f2343 p2343 := .mul h2342 h2166 ⟨cancel2343, by decide +kernel, by decide +kernel⟩

def f2344 : Formula := .neg f2343
def p2344 : Fraction := p2343.neg
theorem h2344 : Reduced f2344 p2344 := .neg h2343

def f2345 : Formula := .mul f11 f5
def num2345 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2345 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2345 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2345 : Fraction := ⟨num2345, den2345⟩
theorem h2345 : Reduced f2345 p2345 := .mul h11 h5 ⟨cancel2345, by decide +kernel, by decide +kernel⟩

def f2346 : Formula := .mul f2345 f43
def num2346 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2346 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2346 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2346 : Fraction := ⟨num2346, den2346⟩
theorem h2346 : Reduced f2346 p2346 := .mul h2345 h43 ⟨cancel2346, by decide +kernel, by decide +kernel⟩

def f2347 : Formula := .mul f2346 f2229
def num2347 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2347 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2347 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2347 : Fraction := ⟨num2347, den2347⟩
theorem h2347 : Reduced f2347 p2347 := .mul h2346 h2229 ⟨cancel2347, by decide +kernel, by decide +kernel⟩

def f2348 : Formula := .mul f2185 f2166
def num2348 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x8, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩
]

def den2348 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2348 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2348 : Fraction := ⟨num2348, den2348⟩
theorem h2348 : Reduced f2348 p2348 := .mul h2185 h2166 ⟨cancel2348, by decide +kernel, by decide +kernel⟩

def f2349 : Formula := .mul f491 f2178
def num2349 : Expr := .bands [
  ⟨0, 1, 1, 0x4, 0x0, 1⟩,
  ⟨1, 1, 1, 0x0, 0x1, 1⟩
]

def den2349 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2349 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2349 : Fraction := ⟨num2349, den2349⟩
theorem h2349 : Reduced f2349 p2349 := .mul h491 h2178 ⟨cancel2349, by decide +kernel, by decide +kernel⟩

def f2350 : Formula := .add f2348 f2349
def num2350 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x10, 1⟩,
  ⟨1, 1, 3, 0x20000000000000000000000000002000000000000000000000000000a, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000001, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩
]

def den2350 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2350 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p2350 : Fraction := ⟨num2350, den2350⟩
theorem h2350 : Reduced f2350 p2350 := .add h2348 h2349 ⟨cancel2350, by decide +kernel, by decide +kernel⟩

def f2351 : Formula := .mul f2347 f2350
def num2351 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x1000000000000000000000000000100000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x20000000000000000000000000004000000000000000000000000000c000000000000000000000000000a0000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 1, 5, 0x0, 0x10000000000000000000000000002000000000000000000000000000200000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2351 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2351 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2351 : Fraction := ⟨num2351, den2351⟩
theorem h2351 : Reduced f2351 p2351 := .mul h2347 h2350 ⟨cancel2351, by decide +kernel, by decide +kernel⟩

def f2352 : Formula := .add f2344 f2351
def num2352 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x20000000000000000000000000004000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 1, 5, 0x10000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2352 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2352 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩
]

def p2352 : Fraction := ⟨num2352, den2352⟩
theorem h2352 : Reduced f2352 p2352 := .add h2344 h2351 ⟨cancel2352, by decide +kernel, by decide +kernel⟩

def f2353 : Formula := .mul f2345 f1
def num2353 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2353 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2353 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2353 : Fraction := ⟨num2353, den2353⟩
theorem h2353 : Reduced f2353 p2353 := .mul h2345 h1 ⟨cancel2353, by decide +kernel, by decide +kernel⟩

def f2354 : Formula := .mul f2353 f16
def num2354 : Expr := .bands [
  ⟨0, 1, 2, 0x0, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 1, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2354 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2354 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2354 : Fraction := ⟨num2354, den2354⟩
theorem h2354 : Reduced f2354 p2354 := .mul h2353 h16 ⟨cancel2354, by decide +kernel, by decide +kernel⟩

def f2355 : Formula := .mul f56 f16
def num2355 : Expr := .bands [
  ⟨0, 0, 2, 0x30000000000000000000000000000, 0x0, 1⟩
]

def den2355 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2355 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2355 : Fraction := ⟨num2355, den2355⟩
theorem h2355 : Reduced f2355 p2355 := .mul h56 h16 ⟨cancel2355, by decide +kernel, by decide +kernel⟩

def f2356 : Formula := .add f2355 f8
def num2356 : Expr := .bands [
  ⟨0, 0, 2, 0x30000000000000000000000000001, 0x0, 1⟩
]

def den2356 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2356 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2356 : Fraction := ⟨num2356, den2356⟩
theorem h2356 : Reduced f2356 p2356 := .add h2355 h8 ⟨cancel2356, by decide +kernel, by decide +kernel⟩

def f2357 : Formula := .mul f2354 f2356
def num2357 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x600000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 1, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2357 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2357 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2357 : Fraction := ⟨num2357, den2357⟩
theorem h2357 : Reduced f2357 p2357 := .mul h2354 h2356 ⟨cancel2357, by decide +kernel, by decide +kernel⟩

def f2358 : Formula := .mul f2357 f2229
def num2358 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x600000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 1, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2358 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2358 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2358 : Fraction := ⟨num2358, den2358⟩
theorem h2358 : Reduced f2358 p2358 := .mul h2357 h2229 ⟨cancel2358, by decide +kernel, by decide +kernel⟩

def f2359 : Formula := .mul f2358 f2166
def num2359 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x300000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2359 : Expr := .bands [
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2359 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2359 : Fraction := ⟨num2359, den2359⟩
theorem h2359 : Reduced f2359 p2359 := .mul h2358 h2166 ⟨cancel2359, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
