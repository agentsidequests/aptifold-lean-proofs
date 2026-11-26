import QuadraticConservationArithmetic059

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2400 : Formula := .mul f2274 f2274
def num2400 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den2400 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2400 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2400 : Fraction := ⟨num2400, den2400⟩
theorem h2400 : Reduced f2400 p2400 := .mul h2274 h2274 ⟨cancel2400, by decide +kernel, by decide +kernel⟩

def f2401 : Formula := .mul f2220 f2400
def num2401 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x600000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2401 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2401 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2401 : Fraction := ⟨num2401, den2401⟩
theorem h2401 : Reduced f2401 p2401 := .mul h2220 h2400 ⟨cancel2401, by decide +kernel, by decide +kernel⟩

def f2402 : Formula := .div f2401 f2223
def num2402 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x600000000000000000000000000000000000000000000000000000000, 0x60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2402 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2402 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2402 : Fraction := ⟨num2402, den2402⟩
theorem h2402 : Reduced f2402 p2402 := .div h2401 h2223 [.integer (4), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2402, by decide +kernel, by decide +kernel⟩

def f2403 : Formula := .neg f2402
def p2403 : Fraction := p2402.neg
theorem h2403 : Reduced f2403 p2403 := .neg h2402

def f2404 : Formula := .add f2399 f2403
def num2404 : Expr := .bands [
  ⟨0, 0, 5, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 7, 0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 7, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 5, 0x70000000000000000000000000006000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2404 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2404 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def p2404 : Fraction := ⟨num2404, den2404⟩
theorem h2404 : Reduced f2404 p2404 := .add h2399 h2403 ⟨cancel2404, by decide +kernel, by decide +kernel⟩

def f2405 : Formula := .neg f2226
def p2405 : Fraction := p2226.neg
theorem h2405 : Reduced f2405 p2405 := .neg h2226

def f2406 : Formula := .add f2404 f2405
def num2406 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x6000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2406 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2406 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def p2406 : Fraction := ⟨num2406, den2406⟩
theorem h2406 : Reduced f2406 p2406 := .add h2404 h2405 ⟨cancel2406, by decide +kernel, by decide +kernel⟩

def f2407 : Formula := .mul f28 f28
def num2407 : Expr := .bands [

]

def den2407 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2407 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2407 : Fraction := ⟨num2407, den2407⟩
theorem h2407 : Reduced f2407 p2407 := .mul h28 h28 ⟨cancel2407, by decide +kernel, by decide +kernel⟩

def f2408 : Formula := .mul f2165 f2407
def num2408 : Expr := .bands [

]

def den2408 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2408 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2408 : Fraction := ⟨num2408, den2408⟩
theorem h2408 : Reduced f2408 p2408 := .mul h2165 h2407 ⟨cancel2408, by decide +kernel, by decide +kernel⟩

def f2409 : Formula := .div f2408 f2172
def num2409 : Expr := .bands [

]

def den2409 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2409 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def p2409 : Fraction := ⟨num2409, den2409⟩
theorem h2409 : Reduced f2409 p2409 := .div h2408 h2172 [.integer (4), .radius, .radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2409, by decide +kernel, by decide +kernel⟩

def f2410 : Formula := .mul f2 f2183
def num2410 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2410 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2410 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2410 : Fraction := ⟨num2410, den2410⟩
theorem h2410 : Reduced f2410 p2410 := .mul h2 h2183 ⟨cancel2410, by decide +kernel, by decide +kernel⟩

def f2411 : Formula := .mul f2410 f2290
def num2411 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x1, 1⟩
]

def den2411 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2411 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2411 : Fraction := ⟨num2411, den2411⟩
theorem h2411 : Reduced f2411 p2411 := .mul h2410 h2290 ⟨cancel2411, by decide +kernel, by decide +kernel⟩

def f2412 : Formula := .mul f0 f2183
def num2412 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2412 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2412 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2412 : Fraction := ⟨num2412, den2412⟩
theorem h2412 : Reduced f2412 p2412 := .mul h0 h2183 ⟨cancel2412, by decide +kernel, by decide +kernel⟩

def f2413 : Formula := .mul f2412 f2282
def num2413 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2413 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2413 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2413 : Fraction := ⟨num2413, den2413⟩
theorem h2413 : Reduced f2413 p2413 := .mul h2412 h2282 ⟨cancel2413, by decide +kernel, by decide +kernel⟩

def f2414 : Formula := .add f2411 f2413
def num2414 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2414 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x4, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2414 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 1, 0x18, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0xc, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def p2414 : Fraction := ⟨num2414, den2414⟩
theorem h2414 : Reduced f2414 p2414 := .add h2411 h2413 ⟨cancel2414, by decide +kernel, by decide +kernel⟩

def f2415 : Formula := .mul f2191 f2191
def num2415 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2415 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2415 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2415 : Fraction := ⟨num2415, den2415⟩
theorem h2415 : Reduced f2415 p2415 := .mul h2191 h2191 ⟨cancel2415, by decide +kernel, by decide +kernel⟩

def f2416 : Formula := .add f2414 f2415
def num2416 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000002, 0x0, 1⟩
]

def den2416 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x4, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2416 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2416 : Fraction := ⟨num2416, den2416⟩
theorem h2416 : Reduced f2416 p2416 := .add h2414 h2415 ⟨cancel2416, by decide +kernel, by decide +kernel⟩

def f2417 : Formula := .mul f2174 f2416
def num2417 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000001000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2417 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2417 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2417 : Fraction := ⟨num2417, den2417⟩
theorem h2417 : Reduced f2417 p2417 := .mul h2174 h2416 ⟨cancel2417, by decide +kernel, by decide +kernel⟩

def f2418 : Formula := .div f2417 f2199
def num2418 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000001000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2418 : Expr := .bands [
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2418 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2418 : Fraction := ⟨num2418, den2418⟩
theorem h2418 : Reduced f2418 p2418 := .div h2417 h2199 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2418, by decide +kernel, by decide +kernel⟩

def f2419 : Formula := .add f2409 f2418
def num2419 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x10000000000000000000000000001000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2419 : Expr := .bands [
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2419 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2419 : Fraction := ⟨num2419, den2419⟩
theorem h2419 : Reduced f2419 p2419 := .add h2409 h2418 ⟨cancel2419, by decide +kernel, by decide +kernel⟩

def f2420 : Formula := .mul f1 f2183
def num2420 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩
]

def den2420 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2420 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2420 : Fraction := ⟨num2420, den2420⟩
theorem h2420 : Reduced f2420 p2420 := .mul h1 h2183 ⟨cancel2420, by decide +kernel, by decide +kernel⟩

def f2421 : Formula := .mul f2420 f28
def num2421 : Expr := .bands [

]

def den2421 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2421 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2421 : Fraction := ⟨num2421, den2421⟩
theorem h2421 : Reduced f2421 p2421 := .mul h2420 h28 ⟨cancel2421, by decide +kernel, by decide +kernel⟩

def f2422 : Formula := .mul f2183 f2191
def num2422 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2422 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2422 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2422 : Fraction := ⟨num2422, den2422⟩
theorem h2422 : Reduced f2422 p2422 := .mul h2183 h2191 ⟨cancel2422, by decide +kernel, by decide +kernel⟩

def f2423 : Formula := .neg f2422
def p2423 : Fraction := p2422.neg
theorem h2423 : Reduced f2423 p2423 := .neg h2422

def f2424 : Formula := .add f2421 f2423
def num2424 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den2424 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2424 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2424 : Fraction := ⟨num2424, den2424⟩
theorem h2424 : Reduced f2424 p2424 := .add h2421 h2423 ⟨cancel2424, by decide +kernel, by decide +kernel⟩

def f2425 : Formula := .mul f2174 f2424
def num2425 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2425 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2425 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2425 : Fraction := ⟨num2425, den2425⟩
theorem h2425 : Reduced f2425 p2425 := .mul h2174 h2424 ⟨cancel2425, by decide +kernel, by decide +kernel⟩

def f2426 : Formula := .div f2425 f2140
def num2426 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2426 : Expr := .bands [
  ⟨7, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2426 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2426 : Fraction := ⟨num2426, den2426⟩
theorem h2426 : Reduced f2426 p2426 := .div h2425 h2140 [.radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2426, by decide +kernel, by decide +kernel⟩

def f2427 : Formula := .add f2419 f2426
def num2427 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2427 : Expr := .bands [
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2427 : Expr := .bands [
  ⟨8, 0, 1, 0x2, 0x0, 1⟩
]

def p2427 : Fraction := ⟨num2427, den2427⟩
theorem h2427 : Reduced f2427 p2427 := .add h2419 h2426 ⟨cancel2427, by decide +kernel, by decide +kernel⟩

def f2428 : Formula := .mul f2213 f28
def num2428 : Expr := .bands [

]

def den2428 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2428 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2428 : Fraction := ⟨num2428, den2428⟩
theorem h2428 : Reduced f2428 p2428 := .mul h2213 h28 ⟨cancel2428, by decide +kernel, by decide +kernel⟩

def f2429 : Formula := .mul f2428 f2290
def num2429 : Expr := .bands [

]

def den2429 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2429 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2429 : Fraction := ⟨num2429, den2429⟩
theorem h2429 : Reduced f2429 p2429 := .mul h2428 h2290 ⟨cancel2429, by decide +kernel, by decide +kernel⟩

def f2430 : Formula := .div f2429 f2170
def num2430 : Expr := .bands [

]

def den2430 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2430 : Expr := .bands [
  ⟨6, 0, 1, 0x1, 0x0, 1⟩
]

def p2430 : Fraction := ⟨num2430, den2430⟩
theorem h2430 : Reduced f2430 p2430 := .div h2429 h2170 [.radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2430, by decide +kernel, by decide +kernel⟩

def f2431 : Formula := .add f2427 f2430
def num2431 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2431 : Expr := .bands [
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2431 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2431 : Fraction := ⟨num2431, den2431⟩
theorem h2431 : Reduced f2431 p2431 := .add h2427 h2430 ⟨cancel2431, by decide +kernel, by decide +kernel⟩

def f2432 : Formula := .mul f2183 f2183
def num2432 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2432 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2432 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2432 : Fraction := ⟨num2432, den2432⟩
theorem h2432 : Reduced f2432 p2432 := .mul h2183 h2183 ⟨cancel2432, by decide +kernel, by decide +kernel⟩

def f2433 : Formula := .mul f2220 f2432
def num2433 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2433 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2433 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2433 : Fraction := ⟨num2433, den2433⟩
theorem h2433 : Reduced f2433 p2433 := .mul h2220 h2432 ⟨cancel2433, by decide +kernel, by decide +kernel⟩

def f2434 : Formula := .div f2433 f2223
def num2434 : Expr := .bands [
  ⟨0, 0, 5, 0x30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2434 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2434 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2434 : Fraction := ⟨num2434, den2434⟩
theorem h2434 : Reduced f2434 p2434 := .div h2433 h2223 [.integer (4), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2434, by decide +kernel, by decide +kernel⟩

def f2435 : Formula := .neg f2434
def p2435 : Fraction := p2434.neg
theorem h2435 : Reduced f2435 p2435 := .neg h2434

def f2436 : Formula := .add f2431 f2435
def num2436 : Expr := .bands [
  ⟨0, 0, 5, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2436 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2436 : Expr := .bands [
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2436 : Fraction := ⟨num2436, den2436⟩
theorem h2436 : Reduced f2436 p2436 := .add h2431 h2435 ⟨cancel2436, by decide +kernel, by decide +kernel⟩

def f2437 : Formula := .neg f2436
def p2437 : Fraction := p2436.neg
theorem h2437 : Reduced f2437 p2437 := .neg h2436

def f2438 : Formula := .add f2406 f2437
def num2438 : Expr := .bands [
  ⟨0, 0, 5, 0x20000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2438 : Expr := .bands [
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2438 : Expr := .bands [
  ⟨6, 0, 1, 0x20, 0x0, 1⟩
]

def p2438 : Fraction := ⟨num2438, den2438⟩
theorem h2438 : Reduced f2438 p2438 := .add h2406 h2437 ⟨cancel2438, by decide +kernel, by decide +kernel⟩

def f2439 : Formula := .mul f7 f2438
def num2439 : Expr := .bands [
  ⟨0, 1, 5, 0x20000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2439 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2439 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2439 : Fraction := ⟨num2439, den2439⟩
theorem h2439 : Reduced f2439 p2439 := .mul h7 h2438 ⟨cancel2439, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
