import MetricWitness054

namespace SchwarzschildMixtures.MetricWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2200 : Formula := .neg f20
def p2200 : Fraction := p20.neg
theorem h2200 : Reduced f2200 p2200 := .neg h20

def f2201 : Formula := .mul f2200 f2113
def num2201 : Expr := .bands [
  ⟨0, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2201 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2201 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2201 : Fraction := ⟨num2201, den2201⟩
theorem h2201 : Reduced f2201 p2201 := .mul h2200 h2113 ⟨cancel2201, by decide +kernel, by decide +kernel⟩

def f2202 : Formula := .mul f2106 f82
def num2202 : Expr := .bands [
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2202 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2202 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2202 : Fraction := ⟨num2202, den2202⟩
theorem h2202 : Reduced f2202 p2202 := .mul h2106 h82 ⟨cancel2202, by decide +kernel, by decide +kernel⟩

def f2203 : Formula := .mul f2186 f79
def num2203 : Expr := .bands [
  ⟨2, 0, 1, 0x5, 0x0, 1⟩
]

def den2203 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2203 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2203 : Fraction := ⟨num2203, den2203⟩
theorem h2203 : Reduced f2203 p2203 := .mul h2186 h79 ⟨cancel2203, by decide +kernel, by decide +kernel⟩

def f2204 : Formula := .mul f2203 f2113
def num2204 : Expr := .bands [
  ⟨2, 0, 3, 0x500000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2204 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2204 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2204 : Fraction := ⟨num2204, den2204⟩
theorem h2204 : Reduced f2204 p2204 := .mul h2203 h2113 ⟨cancel2204, by decide +kernel, by decide +kernel⟩

def f2205 : Formula := .neg f2204
def p2205 : Fraction := p2204.neg
theorem h2205 : Reduced f2205 p2205 := .neg h2204

def f2206 : Formula := .add f2202 f2205
def num2206 : Expr := .bands [
  ⟨2, 0, 3, 0x0, 0x500000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2206 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2206 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2206 : Fraction := ⟨num2206, den2206⟩
theorem h2206 : Reduced f2206 p2206 := .add h2202 h2205 ⟨cancel2206, by decide +kernel, by decide +kernel⟩

def f2207 : Formula := .mul f1100 f2
def num2207 : Expr := .bands [
  ⟨2, 0, 2, 0x40000000000000000000000000000, 0x0, 1⟩
]

def den2207 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2207 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2207 : Fraction := ⟨num2207, den2207⟩
theorem h2207 : Reduced f2207 p2207 := .mul h1100 h2 ⟨cancel2207, by decide +kernel, by decide +kernel⟩

def f2208 : Formula := .neg f2207
def p2208 : Fraction := p2207.neg
theorem h2208 : Reduced f2208 p2208 := .neg h2207

def f2209 : Formula := .add f2206 f2208
def num2209 : Expr := .bands [
  ⟨2, 0, 3, 0x0, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2209 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2209 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2209 : Fraction := ⟨num2209, den2209⟩
theorem h2209 : Reduced f2209 p2209 := .add h2206 h2208 ⟨cancel2209, by decide +kernel, by decide +kernel⟩

def f2210 : Formula := .add f2209 f79
def num2210 : Expr := .bands [
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2210 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2210 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2210 : Fraction := ⟨num2210, den2210⟩
theorem h2210 : Reduced f2210 p2210 := .add h2209 h79 ⟨cancel2210, by decide +kernel, by decide +kernel⟩

def f2211 : Formula := .integer (10)
def p2211 : Fraction := .polynomial (.constant (10))
theorem h2211 : Reduced f2211 p2211 := .integer (10)

def f2212 : Formula := .mul f2211 f18
def num2212 : Expr := .bands [
  ⟨1, 0, 1, 0xa, 0x0, 1⟩
]

def den2212 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2212 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2212 : Fraction := ⟨num2212, den2212⟩
theorem h2212 : Reduced f2212 p2212 := .mul h2211 h18 ⟨cancel2212, by decide +kernel, by decide +kernel⟩

def f2213 : Formula := .mul f2212 f2113
def num2213 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2213 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2213 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2213 : Fraction := ⟨num2213, den2213⟩
theorem h2213 : Reduced f2213 p2213 := .mul h2212 h2113 ⟨cancel2213, by decide +kernel, by decide +kernel⟩

def f2214 : Formula := .add f2210 f2213
def num2214 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2214 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2214 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2214 : Fraction := ⟨num2214, den2214⟩
theorem h2214 : Reduced f2214 p2214 := .add h2210 h2213 ⟨cancel2214, by decide +kernel, by decide +kernel⟩

def f2215 : Formula := .mul f28 f18
def num2215 : Expr := .bands [
  ⟨1, 0, 1, 0x8, 0x0, 1⟩
]

def den2215 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2215 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2215 : Fraction := ⟨num2215, den2215⟩
theorem h2215 : Reduced f2215 p2215 := .mul h28 h18 ⟨cancel2215, by decide +kernel, by decide +kernel⟩

def f2216 : Formula := .mul f2215 f2
def num2216 : Expr := .bands [
  ⟨1, 0, 2, 0x80000000000000000000000000000, 0x0, 1⟩
]

def den2216 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2216 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2216 : Fraction := ⟨num2216, den2216⟩
theorem h2216 : Reduced f2216 p2216 := .mul h2215 h2 ⟨cancel2216, by decide +kernel, by decide +kernel⟩

def f2217 : Formula := .add f2214 f2216
def num2217 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2217 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2217 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2217 : Fraction := ⟨num2217, den2217⟩
theorem h2217 : Reduced f2217 p2217 := .add h2214 h2216 ⟨cancel2217, by decide +kernel, by decide +kernel⟩

def f2218 : Formula := .integer (26)
def p2218 : Fraction := .polynomial (.constant (26))
theorem h2218 : Reduced f2218 p2218 := .integer (26)

def f2219 : Formula := .mul f2218 f18
def num2219 : Expr := .bands [
  ⟨1, 0, 1, 0x1a, 0x0, 1⟩
]

def den2219 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2219 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2219 : Fraction := ⟨num2219, den2219⟩
theorem h2219 : Reduced f2219 p2219 := .mul h2218 h18 ⟨cancel2219, by decide +kernel, by decide +kernel⟩

def f2220 : Formula := .neg f2219
def p2220 : Fraction := p2219.neg
theorem h2220 : Reduced f2220 p2220 := .neg h2219

def f2221 : Formula := .add f2217 f2220
def num2221 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x1a, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2221 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2221 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2221 : Fraction := ⟨num2221, den2221⟩
theorem h2221 : Reduced f2221 p2221 := .add h2217 h2220 ⟨cancel2221, by decide +kernel, by decide +kernel⟩

def f2222 : Formula := .integer (48)
def p2222 : Fraction := .polynomial (.constant (48))
theorem h2222 : Reduced f2222 p2222 := .integer (48)

def f2223 : Formula := .add f2221 f2222
def num2223 : Expr := .bands [
  ⟨0, 0, 1, 0x30, 0x0, 1⟩,
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x1a, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2223 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2223 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2223 : Fraction := ⟨num2223, den2223⟩
theorem h2223 : Reduced f2223 p2223 := .add h2221 h2222 ⟨cancel2223, by decide +kernel, by decide +kernel⟩

def f2224 : Formula := .mul f2201 f2223
def num2224 : Expr := .bands [
  ⟨0, 0, 3, 0x6000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x140000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x1c00000000000000000000000000000000000000000000000000000000, 0x140000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2224 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2224 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2224 : Fraction := ⟨num2224, den2224⟩
theorem h2224 : Reduced f2224 p2224 := .mul h2201 h2223 ⟨cancel2224, by decide +kernel, by decide +kernel⟩

def f2225 : Formula := .mul f2224 f2104
def num2225 : Expr := .bands [
  ⟨4, 2, 3, 0x0, 0x3000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 5, 0x1a00000000000000000000000000000000000000000000000000000000, 0xa0000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨6, 2, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨8, 4, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2225 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2225 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2225 : Fraction := ⟨num2225, den2225⟩
theorem h2225 : Reduced f2225 p2225 := .mul h2224 h2104 ⟨cancel2225, by decide +kernel, by decide +kernel⟩

def f2226 : Formula := .mul f2106 f18
def num2226 : Expr := .bands [
  ⟨5, 0, 1, 0x1, 0x0, 1⟩
]

def den2226 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2226 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2226 : Fraction := ⟨num2226, den2226⟩
theorem h2226 : Reduced f2226 p2226 := .mul h2106 h18 ⟨cancel2226, by decide +kernel, by decide +kernel⟩

def f2227 : Formula := .mul f2226 f18
def num2227 : Expr := .bands [
  ⟨6, 0, 1, 0x1, 0x0, 1⟩
]

def den2227 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2227 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2227 : Fraction := ⟨num2227, den2227⟩
theorem h2227 : Reduced f2227 p2227 := .mul h2226 h18 ⟨cancel2227, by decide +kernel, by decide +kernel⟩

def f2228 : Formula := .mul f2227 f18
def num2228 : Expr := .bands [
  ⟨7, 0, 1, 0x1, 0x0, 1⟩
]

def den2228 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2228 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2228 : Fraction := ⟨num2228, den2228⟩
theorem h2228 : Reduced f2228 p2228 := .mul h2227 h18 ⟨cancel2228, by decide +kernel, by decide +kernel⟩

def f2229 : Formula := .mul f61 f2228
def num2229 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def den2229 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2229 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2229 : Fraction := ⟨num2229, den2229⟩
theorem h2229 : Reduced f2229 p2229 := .mul h61 h2228 ⟨cancel2229, by decide +kernel, by decide +kernel⟩

def f2230 : Formula := .div f2225 f2229
def num2230 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x3000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 5, 0x1a00000000000000000000000000000000000000000000000000000000, 0xa0000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 2, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 4, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2230 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2230 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2230 : Fraction := ⟨num2230, den2230⟩
theorem h2230 : Reduced f2230 p2230 := .div h2225 h2229 [.integer (4), .radius, .radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2230, by decide +kernel, by decide +kernel⟩

def f2231 : Formula := .mul f20 f2113
def num2231 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2231 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2231 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2231 : Fraction := ⟨num2231, den2231⟩
theorem h2231 : Reduced f2231 p2231 := .mul h20 h2113 ⟨cancel2231, by decide +kernel, by decide +kernel⟩

def f2232 : Formula := .add f2168 f2174
def num2232 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x2, 0x0, 1⟩
]

def den2232 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2232 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2232 : Fraction := ⟨num2232, den2232⟩
theorem h2232 : Reduced f2232 p2232 := .add h2168 h2174 ⟨cancel2232, by decide +kernel, by decide +kernel⟩

def f2233 : Formula := .add f2232 f2129
def num2233 : Expr := .bands [
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

def den2233 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2233 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p2233 : Fraction := ⟨num2233, den2233⟩
theorem h2233 : Reduced f2233 p2233 := .add h2232 h2129 ⟨cancel2233, by decide +kernel, by decide +kernel⟩

def f2234 : Formula := .mul f2231 f2233
def num2234 : Expr := .bands [
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

def den2234 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2234 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2234 : Fraction := ⟨num2234, den2234⟩
theorem h2234 : Reduced f2234 p2234 := .mul h2231 h2233 ⟨cancel2234, by decide +kernel, by decide +kernel⟩

def f2235 : Formula := .div f2234 f2081
def num2235 : Expr := .bands [
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

def den2235 : Expr := .bands [
  ⟨7, 0, 1, 0x0, 0x20, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2235 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2235 : Fraction := ⟨num2235, den2235⟩
theorem h2235 : Reduced f2235 p2235 := .div h2234 h2081 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2235, by decide +kernel, by decide +kernel⟩

def f2236 : Formula := .add f2230 f2235
def num2236 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x4000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x180000000000000000000000000018000000000000000000000000003000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 7, 0x0, 0x2000000000000000000000000000400000000000000000000000000120000000000000000000000000010000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 7, 0x1000000000000000000000000000200000000000000000000000000030000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 5, 0x70000000000000000000000000006000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2236 : Expr := .bands [
  ⟨7, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2236 : Expr := .bands [
  ⟨3, 0, 1, 0x40, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x40, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def p2236 : Fraction := ⟨num2236, den2236⟩
theorem h2236 : Reduced f2236 p2236 := .add h2230 h2235 ⟨cancel2236, by decide +kernel, by decide +kernel⟩

def f2237 : Formula := .neg f2135
def p2237 : Fraction := p2135.neg
theorem h2237 : Reduced f2237 p2237 := .neg h2135

def f2238 : Formula := .add f2134 f2237
def num2238 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x0, 0x2, 1⟩
]

def den2238 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2238 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p2238 : Fraction := ⟨num2238, den2238⟩
theorem h2238 : Reduced f2238 p2238 := .add h2134 h2237 ⟨cancel2238, by decide +kernel, by decide +kernel⟩

def f2239 : Formula := .mul f2231 f2238
def num2239 : Expr := .bands [
  ⟨0, 0, 3, 0x1000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x0, 0x40000000000000000000000000004000000000000000000000000001000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000004000000000000000000000000000400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x10000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2239 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2239 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2239 : Fraction := ⟨num2239, den2239⟩
theorem h2239 : Reduced f2239 p2239 := .mul h2231 h2238 ⟨cancel2239, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.MetricWitness
