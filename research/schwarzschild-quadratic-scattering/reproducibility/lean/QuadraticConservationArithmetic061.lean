import QuadraticConservationArithmetic060

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2440 : Formula := .dr f2332
def num2440 : Expr := .bands [
  ⟨0, 1, 5, 0x300000000000000000000000000000000000000000000000000000000, 0x9000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x60000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2440 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2440 : Expr := .bands [
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def p2440 : Fraction := ⟨num2440, den2440⟩
theorem h2440 : Reduced f2440 p2440 := .dr h2332 ⟨cancel2440, by decide +kernel, by decide +kernel⟩

def f2441 : Formula := .mul f0 f2272
def num2441 : Expr := .bands [
  ⟨0, 1, 5, 0x60000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2441 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2441 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2441 : Fraction := ⟨num2441, den2441⟩
theorem h2441 : Reduced f2441 p2441 := .mul h0 h2272 ⟨cancel2441, by decide +kernel, by decide +kernel⟩

def f2442 : Formula := .mul f2441 f101
def num2442 : Expr := .bands [
  ⟨0, 1, 5, 0x60000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2442 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2442 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2442 : Fraction := ⟨num2442, den2442⟩
theorem h2442 : Reduced f2442 p2442 := .mul h2441 h101 ⟨cancel2442, by decide +kernel, by decide +kernel⟩

def f2443 : Formula := .add f2440 f2442
def num2443 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2443 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2443 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def p2443 : Fraction := ⟨num2443, den2443⟩
theorem h2443 : Reduced f2443 p2443 := .add h2440 h2442 ⟨cancel2443, by decide +kernel, by decide +kernel⟩

def f2444 : Formula := .mul f2332 f104
def num2444 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2444 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2444 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2444 : Fraction := ⟨num2444, den2444⟩
theorem h2444 : Reduced f2444 p2444 := .mul h2332 h104 ⟨cancel2444, by decide +kernel, by decide +kernel⟩

def f2445 : Formula := .add f2443 f2444
def num2445 : Expr := .bands [
  ⟨0, 1, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2445 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2445 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p2445 : Fraction := ⟨num2445, den2445⟩
theorem h2445 : Reduced f2445 p2445 := .add h2443 h2444 ⟨cancel2445, by decide +kernel, by decide +kernel⟩

def f2446 : Formula := .mul f0 f2330
def num2446 : Expr := .bands [

]

def den2446 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2446 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2446 : Fraction := ⟨num2446, den2446⟩
theorem h2446 : Reduced f2446 p2446 := .mul h0 h2330 ⟨cancel2446, by decide +kernel, by decide +kernel⟩

def f2447 : Formula := .mul f2446 f82
def num2447 : Expr := .bands [

]

def den2447 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2447 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2447 : Fraction := ⟨num2447, den2447⟩
theorem h2447 : Reduced f2447 p2447 := .mul h2446 h82 ⟨cancel2447, by decide +kernel, by decide +kernel⟩

def f2448 : Formula := .add f2445 f2447
def num2448 : Expr := .bands [
  ⟨0, 1, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2448 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2448 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2448 : Fraction := ⟨num2448, den2448⟩
theorem h2448 : Reduced f2448 p2448 := .add h2445 h2447 ⟨cancel2448, by decide +kernel, by decide +kernel⟩

def f2449 : Formula := .mul f6 f2448
def num2449 : Expr := .bands [
  ⟨0, 1, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2449 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2449 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2449 : Fraction := ⟨num2449, den2449⟩
theorem h2449 : Reduced f2449 p2449 := .mul h6 h2448 ⟨cancel2449, by decide +kernel, by decide +kernel⟩

def f2450 : Formula := .mul f1168 f2332
def num2450 : Expr := .bands [
  ⟨0, 1, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2450 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2450 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2450 : Fraction := ⟨num2450, den2450⟩
theorem h2450 : Reduced f2450 p2450 := .mul h1168 h2332 ⟨cancel2450, by decide +kernel, by decide +kernel⟩

def f2451 : Formula := .mul f2341 f2274
def num2451 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000030000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2451 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2451 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2451 : Fraction := ⟨num2451, den2451⟩
theorem h2451 : Reduced f2451 p2451 := .mul h2341 h2274 ⟨cancel2451, by decide +kernel, by decide +kernel⟩

def f2452 : Formula := .mul f2451 f2276
def num2452 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨1, 1, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2452 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2452 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2452 : Fraction := ⟨num2452, den2452⟩
theorem h2452 : Reduced f2452 p2452 := .mul h2451 h2276 ⟨cancel2452, by decide +kernel, by decide +kernel⟩

def f2453 : Formula := .neg f2452
def p2453 : Fraction := p2452.neg
theorem h2453 : Reduced f2453 p2453 := .neg h2452

def f2454 : Formula := .mul f2304 f2276
def num2454 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x4, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000020000000000000000000000000002, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩
]

def den2454 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2454 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2454 : Fraction := ⟨num2454, den2454⟩
theorem h2454 : Reduced f2454 p2454 := .mul h2304 h2276 ⟨cancel2454, by decide +kernel, by decide +kernel⟩

def f2455 : Formula := .mul f2274 f2291
def num2455 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x3, 1⟩,
  ⟨1, 1, 1, 0x4, 0x0, 1⟩,
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den2455 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2455 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2455 : Fraction := ⟨num2455, den2455⟩
theorem h2455 : Reduced f2455 p2455 := .mul h2274 h2291 ⟨cancel2455, by decide +kernel, by decide +kernel⟩

def f2456 : Formula := .add f2454 f2455
def num2456 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x7, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000020000000000000000000000000006, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000001, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩
]

def den2456 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2456 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def p2456 : Fraction := ⟨num2456, den2456⟩
theorem h2456 : Reduced f2456 p2456 := .add h2454 h2455 ⟨cancel2456, by decide +kernel, by decide +kernel⟩

def f2457 : Formula := .mul f2347 f2456
def num2457 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x700000000000000000000000000070000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x20000000000000000000000000004000000000000000000000000000800000000000000000000000000060000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 1, 5, 0x0, 0x10000000000000000000000000002000000000000000000000000000200000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2457 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2457 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2457 : Fraction := ⟨num2457, den2457⟩
theorem h2457 : Reduced f2457 p2457 := .mul h2347 h2456 ⟨cancel2457, by decide +kernel, by decide +kernel⟩

def f2458 : Formula := .add f2453 f2457
def num2458 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩,
  ⟨2, 1, 5, 0x10000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2458 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2458 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def p2458 : Fraction := ⟨num2458, den2458⟩
theorem h2458 : Reduced f2458 p2458 := .add h2453 h2457 ⟨cancel2458, by decide +kernel, by decide +kernel⟩

def f2459 : Formula := .mul f2358 f2276
def num2459 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x300000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2459 : Expr := .bands [
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2459 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2459 : Fraction := ⟨num2459, den2459⟩
theorem h2459 : Reduced f2459 p2459 := .mul h2358 h2276 ⟨cancel2459, by decide +kernel, by decide +kernel⟩

def f2460 : Formula := .mul f2459 f2276
def num2460 : Expr := .bands [
  ⟨1, 3, 3, 0x300000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2460 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2460 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2460 : Fraction := ⟨num2460, den2460⟩
theorem h2460 : Reduced f2460 p2460 := .mul h2459 h2276 ⟨cancel2460, by decide +kernel, by decide +kernel⟩

def f2461 : Formula := .add f2458 f2460
def num2461 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩,
  ⟨2, 1, 5, 0x10000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2461 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2461 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x10, 0x0, 1⟩
]

def p2461 : Fraction := ⟨num2461, den2461⟩
theorem h2461 : Reduced f2461 p2461 := .add h2458 h2460 ⟨cancel2461, by decide +kernel, by decide +kernel⟩

def f2462 : Formula := .mul f2366 f2274
def num2462 : Expr := .bands [
  ⟨0, 1, 3, 0x10000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2462 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x10, 1⟩,
  ⟨3, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2462 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2462 : Fraction := ⟨num2462, den2462⟩
theorem h2462 : Reduced f2462 p2462 := .mul h2366 h2274 ⟨cancel2462, by decide +kernel, by decide +kernel⟩

def f2463 : Formula := .mul f2462 f2274
def num2463 : Expr := .bands [
  ⟨0, 1, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩,
  ⟨1, 1, 3, 0x20000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 1, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2463 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2463 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2463 : Fraction := ⟨num2463, den2463⟩
theorem h2463 : Reduced f2463 p2463 := .mul h2462 h2274 ⟨cancel2463, by decide +kernel, by decide +kernel⟩

def f2464 : Formula := .neg f2463
def p2464 : Fraction := p2463.neg
theorem h2464 : Reduced f2464 p2464 := .neg h2463

def f2465 : Formula := .add f2461 f2464
def num2465 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x20000000000000000000000000004000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000000, 1⟩,
  ⟨2, 1, 5, 0x20000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 3, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2465 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2465 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def p2465 : Fraction := ⟨num2465, den2465⟩
theorem h2465 : Reduced f2465 p2465 := .add h2461 h2464 ⟨cancel2465, by decide +kernel, by decide +kernel⟩

def f2466 : Formula := .neg f2370
def p2466 : Fraction := p2370.neg
theorem h2466 : Reduced f2466 p2466 := .neg h2370

def f2467 : Formula := .add f2465 f2466
def num2467 : Expr := .bands [
  ⟨0, 1, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2467 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2467 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x40, 1⟩,
  ⟨4, 0, 1, 0x20, 0x0, 1⟩
]

def p2467 : Fraction := ⟨num2467, den2467⟩
theorem h2467 : Reduced f2467 p2467 := .add h2465 h2466 ⟨cancel2467, by decide +kernel, by decide +kernel⟩

def f2468 : Formula := .mul f2341 f2183
def num2468 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2468 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2468 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2468 : Fraction := ⟨num2468, den2468⟩
theorem h2468 : Reduced f2468 p2468 := .mul h2341 h2183 ⟨cancel2468, by decide +kernel, by decide +kernel⟩

def f2469 : Formula := .mul f2468 f28
def num2469 : Expr := .bands [

]

def den2469 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2469 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p2469 : Fraction := ⟨num2469, den2469⟩
theorem h2469 : Reduced f2469 p2469 := .mul h2468 h28 ⟨cancel2469, by decide +kernel, by decide +kernel⟩

def f2470 : Formula := .neg f2469
def p2470 : Fraction := p2469.neg
theorem h2470 : Reduced f2470 p2470 := .neg h2469

def f2471 : Formula := .mul f2191 f28
def num2471 : Expr := .bands [

]

def den2471 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2471 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2471 : Fraction := ⟨num2471, den2471⟩
theorem h2471 : Reduced f2471 p2471 := .mul h2191 h28 ⟨cancel2471, by decide +kernel, by decide +kernel⟩

def f2472 : Formula := .mul f2183 f2290
def num2472 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x1, 1⟩
]

def den2472 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2472 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2472 : Fraction := ⟨num2472, den2472⟩
theorem h2472 : Reduced f2472 p2472 := .mul h2183 h2290 ⟨cancel2472, by decide +kernel, by decide +kernel⟩

def f2473 : Formula := .add f2471 f2472
def num2473 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x1, 1⟩
]

def den2473 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2473 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2473 : Fraction := ⟨num2473, den2473⟩
theorem h2473 : Reduced f2473 p2473 := .add h2471 h2472 ⟨cancel2473, by decide +kernel, by decide +kernel⟩

def f2474 : Formula := .mul f2347 f2473
def num2474 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2474 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2474 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2474 : Fraction := ⟨num2474, den2474⟩
theorem h2474 : Reduced f2474 p2474 := .mul h2347 h2473 ⟨cancel2474, by decide +kernel, by decide +kernel⟩

def f2475 : Formula := .add f2470 f2474
def num2475 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2475 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2475 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2475 : Fraction := ⟨num2475, den2475⟩
theorem h2475 : Reduced f2475 p2475 := .add h2470 h2474 ⟨cancel2475, by decide +kernel, by decide +kernel⟩

def f2476 : Formula := .mul f2358 f28
def num2476 : Expr := .bands [

]

def den2476 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2476 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def p2476 : Fraction := ⟨num2476, den2476⟩
theorem h2476 : Reduced f2476 p2476 := .mul h2358 h28 ⟨cancel2476, by decide +kernel, by decide +kernel⟩

def f2477 : Formula := .mul f2476 f28
def num2477 : Expr := .bands [

]

def den2477 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2477 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2477 : Fraction := ⟨num2477, den2477⟩
theorem h2477 : Reduced f2477 p2477 := .mul h2476 h28 ⟨cancel2477, by decide +kernel, by decide +kernel⟩

def f2478 : Formula := .add f2475 f2477
def num2478 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩
]

def den2478 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2478 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2478 : Fraction := ⟨num2478, den2478⟩
theorem h2478 : Reduced f2478 p2478 := .add h2475 h2477 ⟨cancel2478, by decide +kernel, by decide +kernel⟩

def f2479 : Formula := .mul f2366 f2183
def num2479 : Expr := .bands [
  ⟨0, 1, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2479 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x10, 1⟩,
  ⟨3, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2479 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2479 : Fraction := ⟨num2479, den2479⟩
theorem h2479 : Reduced f2479 p2479 := .mul h2366 h2183 ⟨cancel2479, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
