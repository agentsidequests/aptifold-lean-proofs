import MetricWitness061

namespace SchwarzschildMixtures.MetricWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2480 : Formula := .div f2479 f2095
def num2480 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2480 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2480 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2480 : Fraction := ⟨num2480, den2480⟩
theorem h2480 : Reduced f2480 p2480 := .div h2479 h2095 [.integer (2), .radius, .radius, .horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2480, by decide +kernel, by decide +kernel⟩

def f2481 : Formula := .neg f2480
def p2481 : Fraction := p2480.neg
theorem h2481 : Reduced f2481 p2481 := .neg h2480

def f2482 : Formula := .add f2478 f2481
def num2482 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2482 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2482 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def p2482 : Fraction := ⟨num2482, den2482⟩
theorem h2482 : Reduced f2482 p2482 := .add h2478 h2481 ⟨cancel2482, by decide +kernel, by decide +kernel⟩

def f2483 : Formula := .mul f2103 f2293
def num2483 : Expr := .bands [

]

def den2483 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2483 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2483 : Fraction := ⟨num2483, den2483⟩
theorem h2483 : Reduced f2483 p2483 := .mul h2103 h2293 ⟨cancel2483, by decide +kernel, by decide +kernel⟩

def f2484 : Formula := .div f2483 f2107
def num2484 : Expr := .bands [

]

def den2484 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2484 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p2484 : Fraction := ⟨num2484, den2484⟩
theorem h2484 : Reduced f2484 p2484 := .div h2483 h2107 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2484, by decide +kernel, by decide +kernel⟩

def f2485 : Formula := .add f2482 f2484
def num2485 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2485 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2485 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2485 : Fraction := ⟨num2485, den2485⟩
theorem h2485 : Reduced f2485 p2485 := .add h2482 h2484 ⟨cancel2485, by decide +kernel, by decide +kernel⟩

def f2486 : Formula := .neg f2485
def p2486 : Fraction := p2485.neg
theorem h2486 : Reduced f2486 p2486 := .neg h2485

def f2487 : Formula := .add f2466 f2486
def num2487 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2487 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2487 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x40, 1⟩,
  ⟨5, 0, 1, 0x60, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x30, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def p2487 : Fraction := ⟨num2487, den2487⟩
theorem h2487 : Reduced f2487 p2487 := .add h2466 h2486 ⟨cancel2487, by decide +kernel, by decide +kernel⟩

def f2488 : Formula := .mul f33 f2487
def num2488 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2488 : Expr := .bands [
  ⟨4, 0, 1, 0xc, 0x0, 1⟩,
  ⟨5, 0, 3, 0x800000000000000000000000000040000000000000000000000000000, 0x4, 1⟩
]

def cancel2488 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p2488 : Fraction := ⟨num2488, den2488⟩
theorem h2488 : Reduced f2488 p2488 := .mul h33 h2487 ⟨cancel2488, by decide +kernel, by decide +kernel⟩

def f2489 : Formula := .mul f2124 f2261
def num2489 : Expr := .bands [
  ⟨4, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨7, 4, 1, 0x1, 0x0, 1⟩
]

def den2489 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2489 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2489 : Fraction := ⟨num2489, den2489⟩
theorem h2489 : Reduced f2489 p2489 := .mul h2124 h2261 ⟨cancel2489, by decide +kernel, by decide +kernel⟩

def f2490 : Formula := .div f2489 f2081
def num2490 : Expr := .bands [
  ⟨1, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨2, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x1, 0x0, 1⟩
]

def den2490 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2490 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2490 : Fraction := ⟨num2490, den2490⟩
theorem h2490 : Reduced f2490 p2490 := .div h2489 h2081 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2490, by decide +kernel, by decide +kernel⟩

def f2491 : Formula := .mul f14 f1862
def num2491 : Expr := .bands [
  ⟨0, 1, 1, 0x4, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000002, 1⟩,
  ⟨2, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den2491 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2491 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2491 : Fraction := ⟨num2491, den2491⟩
theorem h2491 : Reduced f2491 p2491 := .mul h14 h1862 ⟨cancel2491, by decide +kernel, by decide +kernel⟩

def f2492 : Formula := .mul f2491 f1863
def num2492 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x4, 1⟩,
  ⟨1, 2, 3, 0x200000000000000000000000000020000000000000000000000000002, 0x0, 1⟩,
  ⟨2, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x0, 0x1, 1⟩
]

def den2492 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2492 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2492 : Fraction := ⟨num2492, den2492⟩
theorem h2492 : Reduced f2492 p2492 := .mul h2491 h1863 ⟨cancel2492, by decide +kernel, by decide +kernel⟩

def f2493 : Formula := .add f2492 f2269
def num2493 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x1000000000000000000000000000100000000000000000000000000010, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000001400000000000000000000000000100000000000000000000000000004, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000800000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den2493 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2493 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2493 : Fraction := ⟨num2493, den2493⟩
theorem h2493 : Reduced f2493 p2493 := .add h2492 h2269 ⟨cancel2493, by decide +kernel, by decide +kernel⟩

def f2494 : Formula := .div f2493 f61
def num2494 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x1000000000000000000000000000100000000000000000000000000010, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000001400000000000000000000000000100000000000000000000000000004, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000800000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den2494 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2494 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2494 : Fraction := ⟨num2494, den2494⟩
theorem h2494 : Reduced f2494 p2494 := .div h2493 h61 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel2494, by decide +kernel, by decide +kernel⟩

def f2495 : Formula := .add f2490 f2494
def num2495 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x800000000000000000000000000080000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x20000000000000000000000000004000000000000000000000000000600000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2495 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2495 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x80, 1⟩,
  ⟨1, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x60, 1⟩,
  ⟨3, 0, 1, 0x10, 0x0, 1⟩
]

def p2495 : Fraction := ⟨num2495, den2495⟩
theorem h2495 : Reduced f2495 p2495 := .add h2490 h2494 ⟨cancel2495, by decide +kernel, by decide +kernel⟩

def f2496 : Formula := .div f2338 f18
def num2496 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000002, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2496 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2496 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2496 : Fraction := ⟨num2496, den2496⟩
theorem h2496 : Reduced f2496 p2496 := .div h2338 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel2496, by decide +kernel, by decide +kernel⟩

def f2497 : Formula := .neg f2496
def p2497 : Fraction := p2496.neg
theorem h2497 : Reduced f2497 p2497 := .neg h2496

def f2498 : Formula := .add f2495 f2497
def num2498 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x14, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000008, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2498 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2498 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p2498 : Fraction := ⟨num2498, den2498⟩
theorem h2498 : Reduced f2498 p2498 := .add h2495 h2497 ⟨cancel2498, by decide +kernel, by decide +kernel⟩

def f2499 : Formula := .mul f2143 f2286
def num2499 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000009, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2499 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2499 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2499 : Fraction := ⟨num2499, den2499⟩
theorem h2499 : Reduced f2499 p2499 := .mul h2143 h2286 ⟨cancel2499, by decide +kernel, by decide +kernel⟩

def f2500 : Formula := .div f2499 f2146
def num2500 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000009, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2500 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2500 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2500 : Fraction := ⟨num2500, den2500⟩
theorem h2500 : Reduced f2500 p2500 := .div h2499 h2146 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2500, by decide +kernel, by decide +kernel⟩

def f2501 : Formula := .add f2498 f2500
def num2501 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000020000000000000000000000000000, 0x2, 1⟩,
  ⟨1, 0, 5, 0x200000000000000000000000000040000000000000000000000000000, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000004, 1⟩,
  ⟨2, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000002, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2501 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2501 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2501 : Fraction := ⟨num2501, den2501⟩
theorem h2501 : Reduced f2501 p2501 := .add h2498 h2500 ⟨cancel2501, by decide +kernel, by decide +kernel⟩

def f2502 : Formula := .mul f2111 f2501
def num2502 : Expr := .bands [
  ⟨0, 0, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 6, 0x2000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x200000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 6, 0x100000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 4, 0x20000000000000000000000000000, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2502 : Expr := .bands [
  ⟨3, 0, 2, 0x20, 0x400000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x200000000000000000000000000000, 0x10, 1⟩
]

def cancel2502 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2502 : Fraction := ⟨num2502, den2502⟩
theorem h2502 : Reduced f2502 p2502 := .mul h2111 h2501 ⟨cancel2502, by decide +kernel, by decide +kernel⟩

def f2503 : Formula := .neg f2149
def p2503 : Fraction := p2149.neg
theorem h2503 : Reduced f2503 p2503 := .neg h2149

def f2504 : Formula := .add f2502 f2503
def num2504 : Expr := .bands [
  ⟨0, 0, 4, 0x30000000000000000000000000000, 0x3000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2504 : Expr := .bands [
  ⟨3, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel2504 : Expr := .bands [
  ⟨3, 0, 2, 0x40, 0x800000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x400000000000000000000000000000, 0x20, 1⟩
]

def p2504 : Fraction := ⟨num2504, den2504⟩
theorem h2504 : Reduced f2504 p2504 := .add h2502 h2503 ⟨cancel2504, by decide +kernel, by decide +kernel⟩

def f2505 : Formula := .mul f2124 f2293
def num2505 : Expr := .bands [

]

def den2505 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2505 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2505 : Fraction := ⟨num2505, den2505⟩
theorem h2505 : Reduced f2505 p2505 := .mul h2124 h2293 ⟨cancel2505, by decide +kernel, by decide +kernel⟩

def f2506 : Formula := .div f2505 f2081
def num2506 : Expr := .bands [

]

def den2506 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2506 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def p2506 : Fraction := ⟨num2506, den2506⟩
theorem h2506 : Reduced f2506 p2506 := .div h2505 h2081 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2506, by decide +kernel, by decide +kernel⟩

def f2507 : Formula := .mul f14 f1786
def num2507 : Expr := .bands [
  ⟨0, 1, 1, 0x2, 0x0, 1⟩
]

def den2507 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2507 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2507 : Fraction := ⟨num2507, den2507⟩
theorem h2507 : Reduced f2507 p2507 := .mul h14 h1786 ⟨cancel2507, by decide +kernel, by decide +kernel⟩

def f2508 : Formula := .mul f2507 f44
def num2508 : Expr := .bands [

]

def den2508 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2508 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2508 : Fraction := ⟨num2508, den2508⟩
theorem h2508 : Reduced f2508 p2508 := .mul h2507 h44 ⟨cancel2508, by decide +kernel, by decide +kernel⟩

def f2509 : Formula := .add f2508 f2301
def num2509 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2509 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2509 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2509 : Fraction := ⟨num2509, den2509⟩
theorem h2509 : Reduced f2509 p2509 := .add h2508 h2301 ⟨cancel2509, by decide +kernel, by decide +kernel⟩

def f2510 : Formula := .div f2509 f61
def num2510 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2510 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2510 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2510 : Fraction := ⟨num2510, den2510⟩
theorem h2510 : Reduced f2510 p2510 := .div h2509 h61 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel2510, by decide +kernel, by decide +kernel⟩

def f2511 : Formula := .add f2506 f2510
def num2511 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2511 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2511 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2511 : Fraction := ⟨num2511, den2511⟩
theorem h2511 : Reduced f2511 p2511 := .add h2506 h2510 ⟨cancel2511, by decide +kernel, by decide +kernel⟩

def f2512 : Formula := .div f2360 f18
def num2512 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2512 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2512 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2512 : Fraction := ⟨num2512, den2512⟩
theorem h2512 : Reduced f2512 p2512 := .div h2360 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel2512, by decide +kernel, by decide +kernel⟩

def f2513 : Formula := .neg f2512
def p2513 : Fraction := p2512.neg
theorem h2513 : Reduced f2513 p2513 := .neg h2512

def f2514 : Formula := .add f2511 f2513
def num2514 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den2514 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2514 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p2514 : Fraction := ⟨num2514, den2514⟩
theorem h2514 : Reduced f2514 p2514 := .add h2511 h2513 ⟨cancel2514, by decide +kernel, by decide +kernel⟩

def f2515 : Formula := .mul f2143 f2318
def num2515 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2515 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2515 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2515 : Fraction := ⟨num2515, den2515⟩
theorem h2515 : Reduced f2515 p2515 := .mul h2143 h2318 ⟨cancel2515, by decide +kernel, by decide +kernel⟩

def f2516 : Formula := .div f2515 f2146
def num2516 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2516 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2516 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2516 : Fraction := ⟨num2516, den2516⟩
theorem h2516 : Reduced f2516 p2516 := .div h2515 h2146 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2516, by decide +kernel, by decide +kernel⟩

def f2517 : Formula := .add f2514 f2516
def num2517 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den2517 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2517 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p2517 : Fraction := ⟨num2517, den2517⟩
theorem h2517 : Reduced f2517 p2517 := .add h2514 h2516 ⟨cancel2517, by decide +kernel, by decide +kernel⟩

def f2518 : Formula := .mul f2111 f2517
def num2518 : Expr := .bands [
  ⟨0, 0, 4, 0x1000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2518 : Expr := .bands [
  ⟨3, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel2518 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2518 : Fraction := ⟨num2518, den2518⟩
theorem h2518 : Reduced f2518 p2518 := .mul h2111 h2517 ⟨cancel2518, by decide +kernel, by decide +kernel⟩

def f2519 : Formula := .neg f2518
def p2519 : Fraction := p2518.neg
theorem h2519 : Reduced f2519 p2519 := .neg h2518

end SchwarzschildMixtures.MetricWitness
