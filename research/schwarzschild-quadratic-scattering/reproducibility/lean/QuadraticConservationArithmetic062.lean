import QuadraticConservationArithmetic061

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2480 : Formula := .mul f2479 f2183
def num2480 : Expr := .bands [
  ⟨0, 1, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2480 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2480 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2480 : Fraction := ⟨num2480, den2480⟩
theorem h2480 : Reduced f2480 p2480 := .mul h2479 h2183 ⟨cancel2480, by decide +kernel, by decide +kernel⟩

def f2481 : Formula := .neg f2480
def p2481 : Fraction := p2480.neg
theorem h2481 : Reduced f2481 p2481 := .neg h2480

def f2482 : Formula := .add f2478 f2481
def num2482 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2482 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2482 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x40, 1⟩,
  ⟨4, 0, 1, 0x20, 0x0, 1⟩
]

def p2482 : Fraction := ⟨num2482, den2482⟩
theorem h2482 : Reduced f2482 p2482 := .add h2478 h2481 ⟨cancel2482, by decide +kernel, by decide +kernel⟩

def f2483 : Formula := .neg f2482
def p2483 : Fraction := p2482.neg
theorem h2483 : Reduced f2483 p2483 := .neg h2482

def f2484 : Formula := .add f2467 f2483
def num2484 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2484 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2484 : Expr := .bands [
  ⟨3, 0, 1, 0x40, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x40, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def p2484 : Fraction := ⟨num2484, den2484⟩
theorem h2484 : Reduced f2484 p2484 := .add h2467 h2483 ⟨cancel2484, by decide +kernel, by decide +kernel⟩

def f2485 : Formula := .mul f1174 f2484
def num2485 : Expr := .bands [
  ⟨0, 1, 5, 0x20000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2485 : Expr := .bands [
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2485 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2485 : Fraction := ⟨num2485, den2485⟩
theorem h2485 : Reduced f2485 p2485 := .mul h1174 h2484 ⟨cancel2485, by decide +kernel, by decide +kernel⟩

def f2486 : Formula := .add f2450 f2485
def num2486 : Expr := .bands [
  ⟨0, 1, 5, 0x0, 0x50000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2486 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2486 : Expr := .bands [
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def p2486 : Fraction := ⟨num2486, den2486⟩
theorem h2486 : Reduced f2486 p2486 := .add h2450 h2485 ⟨cancel2486, by decide +kernel, by decide +kernel⟩

def f2487 : Formula := .add f2449 f2486
def num2487 : Expr := .bands [
  ⟨0, 1, 5, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2487 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2487 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def p2487 : Fraction := ⟨num2487, den2487⟩
theorem h2487 : Reduced f2487 p2487 := .add h2449 h2486 ⟨cancel2487, by decide +kernel, by decide +kernel⟩

def f2488 : Formula := .add f2439 f2487
def num2488 : Expr := .bands [

]

def den2488 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2488 : Expr := .bands [
  ⟨10, 0, 1, 0x40, 0x0, 1⟩,
  ⟨11, 0, 1, 0x0, 0x40, 1⟩,
  ⟨12, 0, 1, 0x10, 0x0, 1⟩
]

def p2488 : Fraction := ⟨num2488, den2488⟩
theorem h2488 : Reduced f2488 p2488 := .add h2439 h2487 ⟨cancel2488, by decide +kernel, by decide +kernel⟩

def f2489 : Formula := .mul f7 f2436
def num2489 : Expr := .bands [
  ⟨0, 1, 5, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2489 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2489 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2489 : Fraction := ⟨num2489, den2489⟩
theorem h2489 : Reduced f2489 p2489 := .mul h7 h2436 ⟨cancel2489, by decide +kernel, by decide +kernel⟩

def f2490 : Formula := .dr f2330
def num2490 : Expr := .bands [

]

def den2490 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2490 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2490 : Fraction := ⟨num2490, den2490⟩
theorem h2490 : Reduced f2490 p2490 := .dr h2330 ⟨cancel2490, by decide +kernel, by decide +kernel⟩

def f2491 : Formula := .mul f2332 f101
def num2491 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2491 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2491 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2491 : Fraction := ⟨num2491, den2491⟩
theorem h2491 : Reduced f2491 p2491 := .mul h2332 h101 ⟨cancel2491, by decide +kernel, by decide +kernel⟩

def f2492 : Formula := .add f2490 f2491
def num2492 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2492 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2492 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2492 : Fraction := ⟨num2492, den2492⟩
theorem h2492 : Reduced f2492 p2492 := .add h2490 h2491 ⟨cancel2492, by decide +kernel, by decide +kernel⟩

def f2493 : Formula := .mul f2446 f104
def num2493 : Expr := .bands [

]

def den2493 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2493 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2493 : Fraction := ⟨num2493, den2493⟩
theorem h2493 : Reduced f2493 p2493 := .mul h2446 h104 ⟨cancel2493, by decide +kernel, by decide +kernel⟩

def f2494 : Formula := .add f2492 f2493
def num2494 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2494 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2494 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2494 : Fraction := ⟨num2494, den2494⟩
theorem h2494 : Reduced f2494 p2494 := .add h2492 h2493 ⟨cancel2494, by decide +kernel, by decide +kernel⟩

def f2495 : Formula := .mul f6 f2494
def num2495 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2495 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2495 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2495 : Fraction := ⟨num2495, den2495⟩
theorem h2495 : Reduced f2495 p2495 := .mul h6 h2494 ⟨cancel2495, by decide +kernel, by decide +kernel⟩

def f2496 : Formula := .mul f1168 f2330
def num2496 : Expr := .bands [

]

def den2496 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2496 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2496 : Fraction := ⟨num2496, den2496⟩
theorem h2496 : Reduced f2496 p2496 := .mul h1168 h2330 ⟨cancel2496, by decide +kernel, by decide +kernel⟩

def f2497 : Formula := .mul f1174 f2482
def num2497 : Expr := .bands [
  ⟨0, 1, 5, 0x20000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2497 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2497 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2497 : Fraction := ⟨num2497, den2497⟩
theorem h2497 : Reduced f2497 p2497 := .mul h1174 h2482 ⟨cancel2497, by decide +kernel, by decide +kernel⟩

def f2498 : Formula := .add f2496 f2497
def num2498 : Expr := .bands [
  ⟨0, 1, 5, 0x20000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2498 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2498 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2498 : Fraction := ⟨num2498, den2498⟩
theorem h2498 : Reduced f2498 p2498 := .add h2496 h2497 ⟨cancel2498, by decide +kernel, by decide +kernel⟩

def f2499 : Formula := .add f2495 f2498
def num2499 : Expr := .bands [
  ⟨0, 1, 5, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2499 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2499 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x8, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def p2499 : Fraction := ⟨num2499, den2499⟩
theorem h2499 : Reduced f2499 p2499 := .add h2495 h2498 ⟨cancel2499, by decide +kernel, by decide +kernel⟩

def f2500 : Formula := .add f2489 f2499
def num2500 : Expr := .bands [

]

def den2500 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2500 : Expr := .bands [
  ⟨10, 0, 1, 0x100, 0x0, 1⟩,
  ⟨11, 0, 1, 0x0, 0x100, 1⟩,
  ⟨12, 0, 1, 0x40, 0x0, 1⟩
]

def p2500 : Fraction := ⟨num2500, den2500⟩
theorem h2500 : Reduced f2500 p2500 := .add h2489 h2499 ⟨cancel2500, by decide +kernel, by decide +kernel⟩

def f2501 : Formula := .mul f56 f75
def num2501 : Expr := .bands [
  ⟨3, 0, 1, 0x3, 0x0, 1⟩
]

def den2501 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2501 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2501 : Fraction := ⟨num2501, den2501⟩
theorem h2501 : Reduced f2501 p2501 := .mul h56 h75 ⟨cancel2501, by decide +kernel, by decide +kernel⟩

def f2502 : Formula := .mul f2501 f73
def num2502 : Expr := .bands [
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2502 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2502 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2502 : Fraction := ⟨num2502, den2502⟩
theorem h2502 : Reduced f2502 p2502 := .mul h2501 h73 ⟨cancel2502, by decide +kernel, by decide +kernel⟩

def f2503 : Formula := .mul f56 f3
def num2503 : Expr := .bands [
  ⟨1, 0, 1, 0x3, 0x0, 1⟩
]

def den2503 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2503 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2503 : Fraction := ⟨num2503, den2503⟩
theorem h2503 : Reduced f2503 p2503 := .mul h56 h3 ⟨cancel2503, by decide +kernel, by decide +kernel⟩

def f2504 : Formula := .mul f2503 f2138
def num2504 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2504 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2504 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2504 : Fraction := ⟨num2504, den2504⟩
theorem h2504 : Reduced f2504 p2504 := .mul h2503 h2138 ⟨cancel2504, by decide +kernel, by decide +kernel⟩

def f2505 : Formula := .add f2502 f2504
def num2505 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2505 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2505 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2505 : Fraction := ⟨num2505, den2505⟩
theorem h2505 : Reduced f2505 p2505 := .add h2502 h2504 ⟨cancel2505, by decide +kernel, by decide +kernel⟩

def f2506 : Formula := .add f2505 f3
def num2506 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2506 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2506 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2506 : Fraction := ⟨num2506, den2506⟩
theorem h2506 : Reduced f2506 p2506 := .add h2505 h3 ⟨cancel2506, by decide +kernel, by decide +kernel⟩

def f2507 : Formula := .mul f47 f2138
def num2507 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2507 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2507 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2507 : Fraction := ⟨num2507, den2507⟩
theorem h2507 : Reduced f2507 p2507 := .mul h47 h2138 ⟨cancel2507, by decide +kernel, by decide +kernel⟩

def f2508 : Formula := .neg f2507
def p2508 : Fraction := p2507.neg
theorem h2508 : Reduced f2508 p2508 := .neg h2507

def f2509 : Formula := .add f2506 f2508
def num2509 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2509 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2509 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2509 : Fraction := ⟨num2509, den2509⟩
theorem h2509 : Reduced f2509 p2509 := .add h2506 h2508 ⟨cancel2509, by decide +kernel, by decide +kernel⟩

def f2510 : Formula := .add f2509 f4
def num2510 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000002, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2510 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2510 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2510 : Fraction := ⟨num2510, den2510⟩
theorem h2510 : Reduced f2510 p2510 := .add h2509 h4 ⟨cancel2510, by decide +kernel, by decide +kernel⟩

def f2511 : Formula := .neg f2510
def p2511 : Fraction := p2510.neg
theorem h2511 : Reduced f2511 p2511 := .neg h2510

def f2512 : Formula := .mul f2511 f2138
def num2512 : Expr := .bands [
  ⟨0, 0, 5, 0x60000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x30000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2512 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2512 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2512 : Fraction := ⟨num2512, den2512⟩
theorem h2512 : Reduced f2512 p2512 := .mul h2511 h2138 ⟨cancel2512, by decide +kernel, by decide +kernel⟩

def f2513 : Formula := .mul f2512 f2167
def num2513 : Expr := .bands [
  ⟨4, 2, 5, 0x60000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x0, 0x30000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨7, 4, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2513 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2513 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2513 : Fraction := ⟨num2513, den2513⟩
theorem h2513 : Reduced f2513 p2513 := .mul h2512 h2167 ⟨cancel2513, by decide +kernel, by decide +kernel⟩

def f2514 : Formula := .mul f10 f5
def num2514 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def den2514 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2514 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2514 : Fraction := ⟨num2514, den2514⟩
theorem h2514 : Reduced f2514 p2514 := .mul h10 h5 ⟨cancel2514, by decide +kernel, by decide +kernel⟩

def f2515 : Formula := .mul f2514 f2140
def num2515 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def den2515 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2515 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2515 : Fraction := ⟨num2515, den2515⟩
theorem h2515 : Reduced f2515 p2515 := .mul h2514 h2140 ⟨cancel2515, by decide +kernel, by decide +kernel⟩

def f2516 : Formula := .div f2513 f2515
def num2516 : Expr := .bands [
  ⟨0, 2, 5, 0x60000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 2, 5, 0x0, 0x30000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 4, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2516 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x80, 1⟩,
  ⟨1, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x60, 1⟩,
  ⟨3, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2516 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2516 : Fraction := ⟨num2516, den2516⟩
theorem h2516 : Reduced f2516 p2516 := .div h2513 h2515 [.integer (4), .radius, .radius, .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2516, by decide +kernel, by decide +kernel⟩

def f2517 : Formula := .mul f10 f1
def num2517 : Expr := .bands [
  ⟨0, 1, 1, 0x4, 0x0, 1⟩
]

def den2517 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2517 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2517 : Fraction := ⟨num2517, den2517⟩
theorem h2517 : Reduced f2517 p2517 := .mul h10 h1 ⟨cancel2517, by decide +kernel, by decide +kernel⟩

def f2518 : Formula := .mul f2517 f2185
def num2518 : Expr := .bands [
  ⟨0, 1, 1, 0x10, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000008, 1⟩,
  ⟨2, 1, 3, 0x200000000000000000000000000020000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x2, 0x0, 1⟩
]

def den2518 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2518 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2518 : Fraction := ⟨num2518, den2518⟩
theorem h2518 : Reduced f2518 p2518 := .mul h2517 h2185 ⟨cancel2518, by decide +kernel, by decide +kernel⟩

def f2519 : Formula := .mul f2518 f2166
def num2519 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x8, 1⟩,
  ⟨1, 2, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x0, 0x1, 1⟩
]

def den2519 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2519 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2519 : Fraction := ⟨num2519, den2519⟩
theorem h2519 : Reduced f2519 p2519 := .mul h2518 h2166 ⟨cancel2519, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
