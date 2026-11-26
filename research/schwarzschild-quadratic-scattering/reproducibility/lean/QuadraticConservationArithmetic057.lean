import QuadraticConservationArithmetic056

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2280 : Formula := .add f2278 f2279
def num2280 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0xc, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x4, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2280 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2280 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2280 : Fraction := ⟨num2280, den2280⟩
theorem h2280 : Reduced f2280 p2280 := .add h2278 h2279 ⟨cancel2280, by decide +kernel, by decide +kernel⟩

def f2281 : Formula := .mul f2191 f104
def num2281 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def den2281 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2281 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2281 : Fraction := ⟨num2281, den2281⟩
theorem h2281 : Reduced f2281 p2281 := .mul h2191 h104 ⟨cancel2281, by decide +kernel, by decide +kernel⟩

def f2282 : Formula := .add f2280 f2281
def num2282 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2282 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2282 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2282 : Fraction := ⟨num2282, den2282⟩
theorem h2282 : Reduced f2282 p2282 := .add h2280 h2281 ⟨cancel2282, by decide +kernel, by decide +kernel⟩

def f2283 : Formula := .add f2193 f2282
def num2283 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x20000000000000000000000000002000000000000000000000000000c, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000004, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x7, 1⟩,
  ⟨5, 2, 1, 0x3, 0x0, 1⟩
]

def den2283 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2283 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def p2283 : Fraction := ⟨num2283, den2283⟩
theorem h2283 : Reduced f2283 p2283 := .add h2193 h2282 ⟨cancel2283, by decide +kernel, by decide +kernel⟩

def f2284 : Formula := .mul f2283 f2276
def num2284 : Expr := .bands [
  ⟨0, 1, 1, 0x8, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x20000000000000000000000000002000000000000000000000000000c, 1⟩,
  ⟨2, 1, 3, 0x300000000000000000000000000030000000000000000000000000004, 0x0, 1⟩,
  ⟨3, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x7, 0x0, 1⟩,
  ⟨5, 3, 1, 0x0, 0x3, 1⟩
]

def den2284 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x30, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x18, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2284 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2284 : Fraction := ⟨num2284, den2284⟩
theorem h2284 : Reduced f2284 p2284 := .mul h2283 h2276 ⟨cancel2284, by decide +kernel, by decide +kernel⟩

def f2285 : Formula := .mul f1 f2276
def num2285 : Expr := .bands [
  ⟨2, 2, 1, 0x0, 0x1, 1⟩
]

def den2285 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2285 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2285 : Fraction := ⟨num2285, den2285⟩
theorem h2285 : Reduced f2285 p2285 := .mul h1 h2276 ⟨cancel2285, by decide +kernel, by decide +kernel⟩

def f2286 : Formula := .dr f28
def num2286 : Expr := .bands [

]

def den2286 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2286 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2286 : Fraction := ⟨num2286, den2286⟩
theorem h2286 : Reduced f2286 p2286 := .dr h28 ⟨cancel2286, by decide +kernel, by decide +kernel⟩

def f2287 : Formula := .mul f2166 f101
def num2287 : Expr := .bands [
  ⟨1, 1, 1, 0x0, 0x1, 1⟩
]

def den2287 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2287 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2287 : Fraction := ⟨num2287, den2287⟩
theorem h2287 : Reduced f2287 p2287 := .mul h2166 h101 ⟨cancel2287, by decide +kernel, by decide +kernel⟩

def f2288 : Formula := .add f2286 f2287
def num2288 : Expr := .bands [
  ⟨1, 1, 1, 0x0, 0x1, 1⟩
]

def den2288 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2288 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2288 : Fraction := ⟨num2288, den2288⟩
theorem h2288 : Reduced f2288 p2288 := .add h2286 h2287 ⟨cancel2288, by decide +kernel, by decide +kernel⟩

def f2289 : Formula := .mul f28 f104
def num2289 : Expr := .bands [

]

def den2289 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2289 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2289 : Fraction := ⟨num2289, den2289⟩
theorem h2289 : Reduced f2289 p2289 := .mul h28 h104 ⟨cancel2289, by decide +kernel, by decide +kernel⟩

def f2290 : Formula := .add f2288 f2289
def num2290 : Expr := .bands [
  ⟨1, 1, 1, 0x0, 0x1, 1⟩
]

def den2290 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2290 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2290 : Fraction := ⟨num2290, den2290⟩
theorem h2290 : Reduced f2290 p2290 := .add h2288 h2289 ⟨cancel2290, by decide +kernel, by decide +kernel⟩

def f2291 : Formula := .add f2178 f2290
def num2291 : Expr := .bands [
  ⟨1, 1, 1, 0x3, 0x0, 1⟩,
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den2291 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2291 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2291 : Fraction := ⟨num2291, den2291⟩
theorem h2291 : Reduced f2291 p2291 := .add h2178 h2290 ⟨cancel2291, by decide +kernel, by decide +kernel⟩

def f2292 : Formula := .mul f2285 f2291
def num2292 : Expr := .bands [
  ⟨3, 3, 1, 0x0, 0x3, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den2292 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x30, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x18, 1⟩,
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2292 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2292 : Fraction := ⟨num2292, den2292⟩
theorem h2292 : Reduced f2292 p2292 := .mul h2285 h2291 ⟨cancel2292, by decide +kernel, by decide +kernel⟩

def f2293 : Formula := .add f2284 f2292
def num2293 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x4, 1⟩,
  ⟨1, 1, 3, 0x100000000000000000000000000010000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x2, 1⟩
]

def den2293 : Expr := .bands [
  ⟨1, 0, 1, 0x10, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x10, 1⟩,
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2293 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x80, 1⟩,
  ⟨2, 0, 1, 0x60, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p2293 : Fraction := ⟨num2293, den2293⟩
theorem h2293 : Reduced f2293 p2293 := .add h2284 h2292 ⟨cancel2293, by decide +kernel, by decide +kernel⟩

def f2294 : Formula := .mul f2246 f2293
def num2294 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x4, 1⟩,
  ⟨1, 1, 3, 0x100000000000000000000000000010000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x0, 0x2, 1⟩
]

def den2294 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2294 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2294 : Fraction := ⟨num2294, den2294⟩
theorem h2294 : Reduced f2294 p2294 := .mul h2246 h2293 ⟨cancel2294, by decide +kernel, by decide +kernel⟩

def f2295 : Formula := .add f2277 f2294
def num2295 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x400000000000000000000000000060000000000000000000000000002, 1⟩,
  ⟨1, 1, 3, 0x600000000000000000000000000090000000000000000000000000003, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x200000000000000000000000000030000000000000000000000000001, 1⟩,
  ⟨3, 3, 1, 0x3, 0x0, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩
]

def den2295 : Expr := .bands [
  ⟨3, 0, 1, 0x20, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2295 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2295 : Fraction := ⟨num2295, den2295⟩
theorem h2295 : Reduced f2295 p2295 := .add h2277 h2294 ⟨cancel2295, by decide +kernel, by decide +kernel⟩

def f2296 : Formula := .mul f2255 f2276
def num2296 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x1, 1⟩
]

def den2296 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2296 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2296 : Fraction := ⟨num2296, den2296⟩
theorem h2296 : Reduced f2296 p2296 := .mul h2255 h2276 ⟨cancel2296, by decide +kernel, by decide +kernel⟩

def f2297 : Formula := .mul f2296 f2276
def num2297 : Expr := .bands [
  ⟨0, 3, 1, 0x1, 0x0, 1⟩
]

def den2297 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2297 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2297 : Fraction := ⟨num2297, den2297⟩
theorem h2297 : Reduced f2297 p2297 := .mul h2296 h2276 ⟨cancel2297, by decide +kernel, by decide +kernel⟩

def f2298 : Formula := .neg f2297
def p2298 : Fraction := p2297.neg
theorem h2298 : Reduced f2298 p2298 := .neg h2297

def f2299 : Formula := .add f2295 f2298
def num2299 : Expr := .bands [
  ⟨0, 1, 3, 0x0, 0x400000000000000000000000000060000000000000000000000000002, 1⟩,
  ⟨1, 1, 3, 0x600000000000000000000000000090000000000000000000000000003, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x200000000000000000000000000030000000000000000000000000001, 1⟩,
  ⟨3, 3, 1, 0x7, 0x0, 1⟩,
  ⟨4, 3, 1, 0x0, 0x3, 1⟩
]

def den2299 : Expr := .bands [
  ⟨3, 0, 1, 0x20, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2299 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p2299 : Fraction := ⟨num2299, den2299⟩
theorem h2299 : Reduced f2299 p2299 := .add h2295 h2298 ⟨cancel2299, by decide +kernel, by decide +kernel⟩

def f2300 : Formula := .mul f2261 f2274
def num2300 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x1, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2300 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x4, 1⟩,
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2300 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2300 : Fraction := ⟨num2300, den2300⟩
theorem h2300 : Reduced f2300 p2300 := .mul h2261 h2274 ⟨cancel2300, by decide +kernel, by decide +kernel⟩

def f2301 : Formula := .mul f2300 f2274
def num2301 : Expr := .bands [
  ⟨0, 1, 1, 0x1, 0x0, 1⟩,
  ⟨1, 1, 1, 0x0, 0x2, 1⟩,
  ⟨2, 1, 1, 0x1, 0x0, 1⟩
]

def den2301 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2301 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2301 : Fraction := ⟨num2301, den2301⟩
theorem h2301 : Reduced f2301 p2301 := .mul h2300 h2274 ⟨cancel2301, by decide +kernel, by decide +kernel⟩

def f2302 : Formula := .add f2299 f2301
def num2302 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x4, 1⟩,
  ⟨1, 1, 3, 0x8, 0x400000000000000000000000000060000000000000000000000000000, 1⟩,
  ⟨2, 1, 3, 0x600000000000000000000000000090000000000000000000000000000, 0x5, 1⟩,
  ⟨3, 1, 3, 0x1, 0x200000000000000000000000000030000000000000000000000000000, 1⟩,
  ⟨4, 3, 1, 0x7, 0x0, 1⟩,
  ⟨5, 3, 1, 0x0, 0x3, 1⟩
]

def den2302 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2302 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p2302 : Fraction := ⟨num2302, den2302⟩
theorem h2302 : Reduced f2302 p2302 := .add h2299 h2301 ⟨cancel2302, by decide +kernel, by decide +kernel⟩

def f2303 : Formula := .mul f2267 f2274
def num2303 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x1, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2303 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x8, 1⟩,
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2303 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2303 : Fraction := ⟨num2303, den2303⟩
theorem h2303 : Reduced f2303 p2303 := .mul h2267 h2274 ⟨cancel2303, by decide +kernel, by decide +kernel⟩

def f2304 : Formula := .add f2185 f2191
def num2304 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000002, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2304 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2304 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2304 : Fraction := ⟨num2304, den2304⟩
theorem h2304 : Reduced f2304 p2304 := .add h2185 h2191 ⟨cancel2304, by decide +kernel, by decide +kernel⟩

def f2305 : Formula := .mul f2303 f2304
def num2305 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x4, 1⟩,
  ⟨1, 1, 3, 0x200000000000000000000000000020000000000000000000000000006, 0x0, 1⟩,
  ⟨2, 1, 3, 0x0, 0x300000000000000000000000000030000000000000000000000000002, 1⟩,
  ⟨3, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x0, 0x1, 1⟩,
  ⟨5, 3, 1, 0x1, 0x0, 1⟩
]

def den2305 : Expr := .bands [
  ⟨4, 0, 1, 0x20, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x20, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2305 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2305 : Fraction := ⟨num2305, den2305⟩
theorem h2305 : Reduced f2305 p2305 := .mul h2303 h2304 ⟨cancel2305, by decide +kernel, by decide +kernel⟩

def f2306 : Formula := .neg f2305
def p2306 : Fraction := p2305.neg
theorem h2306 : Reduced f2306 p2306 := .neg h2305

def f2307 : Formula := .add f2302 f2306
def num2307 : Expr := .bands [
  ⟨0, 1, 3, 0x300000000000000000000000000040000000000000000000000000000, 0x1, 1⟩,
  ⟨1, 1, 3, 0x1, 0x300000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 3, 1, 0x0, 0x4, 1⟩
]

def den2307 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2307 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x60, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x30, 1⟩,
  ⟨8, 0, 1, 0x8, 0x0, 1⟩
]

def p2307 : Fraction := ⟨num2307, den2307⟩
theorem h2307 : Reduced f2307 p2307 := .add h2302 h2306 ⟨cancel2307, by decide +kernel, by decide +kernel⟩

def f2308 : Formula := .mul f2138 f2307
def num2308 : Expr := .bands [
  ⟨0, 1, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 3, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2308 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2308 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2308 : Fraction := ⟨num2308, den2308⟩
theorem h2308 : Reduced f2308 p2308 := .mul h2138 h2307 ⟨cancel2308, by decide +kernel, by decide +kernel⟩

def f2309 : Formula := .neg f2272
def p2309 : Fraction := p2272.neg
theorem h2309 : Reduced f2309 p2309 := .neg h2272

def f2310 : Formula := .add f2308 f2309
def num2310 : Expr := .bands [
  ⟨0, 1, 5, 0x100000000000000000000000000000000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2310 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2310 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def p2310 : Fraction := ⟨num2310, den2310⟩
theorem h2310 : Reduced f2310 p2310 := .add h2308 h2309 ⟨cancel2310, by decide +kernel, by decide +kernel⟩

def f2311 : Formula := .mul f2242 f2183
def num2311 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000020000000000000000000000000001, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x1, 1⟩
]

def den2311 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x8, 1⟩,
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2311 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2311 : Fraction := ⟨num2311, den2311⟩
theorem h2311 : Reduced f2311 p2311 := .mul h2242 h2183 ⟨cancel2311, by decide +kernel, by decide +kernel⟩

def f2312 : Formula := .mul f2311 f28
def num2312 : Expr := .bands [

]

def den2312 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2312 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x8, 1⟩,
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def p2312 : Fraction := ⟨num2312, den2312⟩
theorem h2312 : Reduced f2312 p2312 := .mul h2311 h28 ⟨cancel2312, by decide +kernel, by decide +kernel⟩

def f2313 : Formula := .mul f2282 f28
def num2313 : Expr := .bands [

]

def den2313 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2313 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def p2313 : Fraction := ⟨num2313, den2313⟩
theorem h2313 : Reduced f2313 p2313 := .mul h2282 h28 ⟨cancel2313, by decide +kernel, by decide +kernel⟩

def f2314 : Formula := .mul f1 f28
def num2314 : Expr := .bands [

]

def den2314 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2314 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2314 : Fraction := ⟨num2314, den2314⟩
theorem h2314 : Reduced f2314 p2314 := .mul h1 h28 ⟨cancel2314, by decide +kernel, by decide +kernel⟩

def f2315 : Formula := .mul f2314 f2290
def num2315 : Expr := .bands [

]

def den2315 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2315 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2315 : Fraction := ⟨num2315, den2315⟩
theorem h2315 : Reduced f2315 p2315 := .mul h2314 h2290 ⟨cancel2315, by decide +kernel, by decide +kernel⟩

def f2316 : Formula := .add f2313 f2315
def num2316 : Expr := .bands [

]

def den2316 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2316 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2316 : Fraction := ⟨num2316, den2316⟩
theorem h2316 : Reduced f2316 p2316 := .add h2313 h2315 ⟨cancel2316, by decide +kernel, by decide +kernel⟩

def f2317 : Formula := .mul f2246 f2316
def num2317 : Expr := .bands [

]

def den2317 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2317 : Expr := .bands [
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def p2317 : Fraction := ⟨num2317, den2317⟩
theorem h2317 : Reduced f2317 p2317 := .mul h2246 h2316 ⟨cancel2317, by decide +kernel, by decide +kernel⟩

def f2318 : Formula := .add f2312 f2317
def num2318 : Expr := .bands [

]

def den2318 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2318 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2318 : Fraction := ⟨num2318, den2318⟩
theorem h2318 : Reduced f2318 p2318 := .add h2312 h2317 ⟨cancel2318, by decide +kernel, by decide +kernel⟩

def f2319 : Formula := .mul f2255 f28
def num2319 : Expr := .bands [

]

def den2319 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2319 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2319 : Fraction := ⟨num2319, den2319⟩
theorem h2319 : Reduced f2319 p2319 := .mul h2255 h28 ⟨cancel2319, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
