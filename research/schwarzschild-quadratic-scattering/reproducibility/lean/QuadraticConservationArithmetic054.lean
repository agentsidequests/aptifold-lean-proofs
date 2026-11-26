import QuadraticConservationArithmetic053

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2160 : Formula := .mul f2159 f3
def num2160 : Expr := .bands [
  ⟨1, 0, 1, 0x1a, 0x0, 1⟩
]

def den2160 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2160 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2160 : Fraction := ⟨num2160, den2160⟩
theorem h2160 : Reduced f2160 p2160 := .mul h2159 h3 ⟨cancel2160, by decide +kernel, by decide +kernel⟩

def f2161 : Formula := .neg f2160
def p2161 : Fraction := p2160.neg
theorem h2161 : Reduced f2161 p2161 := .neg h2160

def f2162 : Formula := .add f2158 f2161
def num2162 : Expr := .bands [
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x1a, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2162 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2162 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2162 : Fraction := ⟨num2162, den2162⟩
theorem h2162 : Reduced f2162 p2162 := .add h2158 h2161 ⟨cancel2162, by decide +kernel, by decide +kernel⟩

def f2163 : Formula := .integer (48)
def p2163 : Fraction := .polynomial (.constant (48))
theorem h2163 : Reduced f2163 p2163 := .integer (48)

def f2164 : Formula := .add f2162 f2163
def num2164 : Expr := .bands [
  ⟨0, 0, 1, 0x30, 0x0, 1⟩,
  ⟨1, 0, 3, 0xa00000000000000000000000000080000000000000000000000000000, 0x1a, 1⟩,
  ⟨2, 0, 3, 0x1, 0x500000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2164 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2164 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2164 : Fraction := ⟨num2164, den2164⟩
theorem h2164 : Reduced f2164 p2164 := .add h2162 h2163 ⟨cancel2164, by decide +kernel, by decide +kernel⟩

def f2165 : Formula := .mul f2139 f2164
def num2165 : Expr := .bands [
  ⟨0, 0, 3, 0x6000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x140000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x6400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x1c00000000000000000000000000000000000000000000000000000000, 0x140000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2165 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2165 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2165 : Fraction := ⟨num2165, den2165⟩
theorem h2165 : Reduced f2165 p2165 := .mul h2139 h2164 ⟨cancel2165, by decide +kernel, by decide +kernel⟩

def f2166 : Formula := .div f154 f1166
def num2166 : Expr := .bands [
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den2166 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2166 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2166 : Fraction := ⟨num2166, den2166⟩
theorem h2166 : Reduced f2166 p2166 := .div h154 h1166 [.integer (2), .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2166, by decide +kernel, by decide +kernel⟩

def f2167 : Formula := .mul f2166 f2166
def num2167 : Expr := .bands [
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2167 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2167 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2167 : Fraction := ⟨num2167, den2167⟩
theorem h2167 : Reduced f2167 p2167 := .mul h2166 h2166 ⟨cancel2167, by decide +kernel, by decide +kernel⟩

def f2168 : Formula := .mul f2165 f2167
def num2168 : Expr := .bands [
  ⟨4, 2, 3, 0x0, 0x3000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 5, 0x1a00000000000000000000000000000000000000000000000000000000, 0xa0000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨6, 2, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨8, 4, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2168 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2168 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2168 : Fraction := ⟨num2168, den2168⟩
theorem h2168 : Reduced f2168 p2168 := .mul h2165 h2167 ⟨cancel2168, by decide +kernel, by decide +kernel⟩

def f2169 : Formula := .mul f2140 f3
def num2169 : Expr := .bands [
  ⟨5, 0, 1, 0x1, 0x0, 1⟩
]

def den2169 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2169 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2169 : Fraction := ⟨num2169, den2169⟩
theorem h2169 : Reduced f2169 p2169 := .mul h2140 h3 ⟨cancel2169, by decide +kernel, by decide +kernel⟩

def f2170 : Formula := .mul f2169 f3
def num2170 : Expr := .bands [
  ⟨6, 0, 1, 0x1, 0x0, 1⟩
]

def den2170 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2170 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2170 : Fraction := ⟨num2170, den2170⟩
theorem h2170 : Reduced f2170 p2170 := .mul h2169 h3 ⟨cancel2170, by decide +kernel, by decide +kernel⟩

def f2171 : Formula := .mul f2170 f3
def num2171 : Expr := .bands [
  ⟨7, 0, 1, 0x1, 0x0, 1⟩
]

def den2171 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2171 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2171 : Fraction := ⟨num2171, den2171⟩
theorem h2171 : Reduced f2171 p2171 := .mul h2170 h3 ⟨cancel2171, by decide +kernel, by decide +kernel⟩

def f2172 : Formula := .mul f10 f2171
def num2172 : Expr := .bands [
  ⟨7, 0, 1, 0x4, 0x0, 1⟩
]

def den2172 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2172 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2172 : Fraction := ⟨num2172, den2172⟩
theorem h2172 : Reduced f2172 p2172 := .mul h10 h2171 ⟨cancel2172, by decide +kernel, by decide +kernel⟩

def f2173 : Formula := .div f2168 f2172
def num2173 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x3000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 5, 0x1a00000000000000000000000000000000000000000000000000000000, 0xa0000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 2, 5, 0x50000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 4, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2173 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2173 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2173 : Fraction := ⟨num2173, den2173⟩
theorem h2173 : Reduced f2173 p2173 := .div h2168 h2172 [.integer (4), .radius, .radius, .radius, .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2173, by decide +kernel, by decide +kernel⟩

def f2174 : Formula := .mul f5 f2138
def num2174 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2174 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2174 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2174 : Fraction := ⟨num2174, den2174⟩
theorem h2174 : Reduced f2174 p2174 := .mul h5 h2138 ⟨cancel2174, by decide +kernel, by decide +kernel⟩

def f2175 : Formula := .mul f2 f491
def num2175 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2175 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2175 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2175 : Fraction := ⟨num2175, den2175⟩
theorem h2175 : Reduced f2175 p2175 := .mul h2 h491 ⟨cancel2175, by decide +kernel, by decide +kernel⟩

def f2176 : Formula := .dr f2166
def num2176 : Expr := .bands [
  ⟨1, 1, 1, 0x4, 0x0, 1⟩,
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den2176 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2176 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2176 : Fraction := ⟨num2176, den2176⟩
theorem h2176 : Reduced f2176 p2176 := .dr h2166 ⟨cancel2176, by decide +kernel, by decide +kernel⟩

def f2177 : Formula := .mul f28 f82
def num2177 : Expr := .bands [

]

def den2177 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2177 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2177 : Fraction := ⟨num2177, den2177⟩
theorem h2177 : Reduced f2177 p2177 := .mul h28 h82 ⟨cancel2177, by decide +kernel, by decide +kernel⟩

def f2178 : Formula := .add f2176 f2177
def num2178 : Expr := .bands [
  ⟨1, 1, 1, 0x4, 0x0, 1⟩,
  ⟨2, 1, 1, 0x0, 0x1, 1⟩
]

def den2178 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2178 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2178 : Fraction := ⟨num2178, den2178⟩
theorem h2178 : Reduced f2178 p2178 := .add h2176 h2177 ⟨cancel2178, by decide +kernel, by decide +kernel⟩

def f2179 : Formula := .mul f2175 f2178
def num2179 : Expr := .bands [
  ⟨0, 2, 1, 0x4, 0x0, 1⟩,
  ⟨1, 2, 1, 0x0, 0x1, 1⟩
]

def den2179 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2179 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2179 : Fraction := ⟨num2179, den2179⟩
theorem h2179 : Reduced f2179 p2179 := .mul h2175 h2178 ⟨cancel2179, by decide +kernel, by decide +kernel⟩

def f2180 : Formula := .mul f0 f491
def num2180 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def den2180 : Expr := .bands [
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2180 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2180 : Fraction := ⟨num2180, den2180⟩
theorem h2180 : Reduced f2180 p2180 := .mul h0 h491 ⟨cancel2180, by decide +kernel, by decide +kernel⟩

def f2181 : Formula := .dr f491
def num2181 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2181 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2181 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p2181 : Fraction := ⟨num2181, den2181⟩
theorem h2181 : Reduced f2181 p2181 := .dr h491 ⟨cancel2181, by decide +kernel, by decide +kernel⟩

def f2182 : Formula := .mul f0 f3
def num2182 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den2182 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2182 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2182 : Fraction := ⟨num2182, den2182⟩
theorem h2182 : Reduced f2182 p2182 := .mul h0 h3 ⟨cancel2182, by decide +kernel, by decide +kernel⟩

def f2183 : Formula := .div f8 f2182
def num2183 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2183 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2183 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2183 : Fraction := ⟨num2183, den2183⟩
theorem h2183 : Reduced f2183 p2183 := .div h8 h2182 [.integer (2), .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2183, by decide +kernel, by decide +kernel⟩

def f2184 : Formula := .mul f2183 f82
def num2184 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2184 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2184 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2184 : Fraction := ⟨num2184, den2184⟩
theorem h2184 : Reduced f2184 p2184 := .mul h2183 h82 ⟨cancel2184, by decide +kernel, by decide +kernel⟩

def f2185 : Formula := .add f2181 f2184
def num2185 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2185 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2185 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2185 : Fraction := ⟨num2185, den2185⟩
theorem h2185 : Reduced f2185 p2185 := .add h2181 h2184 ⟨cancel2185, by decide +kernel, by decide +kernel⟩

def f2186 : Formula := .dr f2185
def num2186 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000020, 1⟩,
  ⟨2, 0, 3, 0x400000000000000000000000000040000000000000000000000000008, 0x0, 1⟩,
  ⟨3, 0, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 2, 1, 0x0, 0x4, 1⟩,
  ⟨5, 2, 1, 0x1, 0x0, 1⟩
]

def den2186 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2186 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2186 : Fraction := ⟨num2186, den2186⟩
theorem h2186 : Reduced f2186 p2186 := .dr h2185 ⟨cancel2186, by decide +kernel, by decide +kernel⟩

def f2187 : Formula := .dr f2183
def num2187 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den2187 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2187 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2187 : Fraction := ⟨num2187, den2187⟩
theorem h2187 : Reduced f2187 p2187 := .dr h2183 ⟨cancel2187, by decide +kernel, by decide +kernel⟩

def f2188 : Formula := .mul f491 f101
def num2188 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2188 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2188 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2188 : Fraction := ⟨num2188, den2188⟩
theorem h2188 : Reduced f2188 p2188 := .mul h491 h101 ⟨cancel2188, by decide +kernel, by decide +kernel⟩

def f2189 : Formula := .add f2187 f2188
def num2189 : Expr := .bands [

]

def den2189 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2189 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p2189 : Fraction := ⟨num2189, den2189⟩
theorem h2189 : Reduced f2189 p2189 := .add h2187 h2188 ⟨cancel2189, by decide +kernel, by decide +kernel⟩

def f2190 : Formula := .mul f2183 f104
def num2190 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2190 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2190 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2190 : Fraction := ⟨num2190, den2190⟩
theorem h2190 : Reduced f2190 p2190 := .mul h2183 h104 ⟨cancel2190, by decide +kernel, by decide +kernel⟩

def f2191 : Formula := .add f2189 f2190
def num2191 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2191 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2191 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2191 : Fraction := ⟨num2191, den2191⟩
theorem h2191 : Reduced f2191 p2191 := .add h2189 h2190 ⟨cancel2191, by decide +kernel, by decide +kernel⟩

def f2192 : Formula := .mul f2191 f82
def num2192 : Expr := .bands [
  ⟨0, 0, 1, 0xc, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2192 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x2, 1⟩,
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2192 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2192 : Fraction := ⟨num2192, den2192⟩
theorem h2192 : Reduced f2192 p2192 := .mul h2191 h82 ⟨cancel2192, by decide +kernel, by decide +kernel⟩

def f2193 : Formula := .add f2186 f2192
def num2193 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 3, 0x400000000000000000000000000040000000000000000000000000010, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000004, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x8, 1⟩,
  ⟨5, 2, 1, 0x3, 0x0, 1⟩
]

def den2193 : Expr := .bands [
  ⟨3, 0, 1, 0x8, 0x0, 1⟩,
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2193 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x2, 1⟩,
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2193 : Fraction := ⟨num2193, den2193⟩
theorem h2193 : Reduced f2193 p2193 := .add h2186 h2192 ⟨cancel2193, by decide +kernel, by decide +kernel⟩

def f2194 : Formula := .mul f2180 f2193
def num2194 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 3, 0x400000000000000000000000000040000000000000000000000000010, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000004, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x0, 0x8, 1⟩,
  ⟨5, 2, 1, 0x3, 0x0, 1⟩
]

def den2194 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x4, 1⟩,
  ⟨5, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2194 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2194 : Fraction := ⟨num2194, den2194⟩
theorem h2194 : Reduced f2194 p2194 := .mul h2180 h2193 ⟨cancel2194, by decide +kernel, by decide +kernel⟩

def f2195 : Formula := .add f2179 f2194
def num2195 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x2, 0x0, 1⟩
]

def den2195 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2195 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2195 : Fraction := ⟨num2195, den2195⟩
theorem h2195 : Reduced f2195 p2195 := .add h2179 h2194 ⟨cancel2195, by decide +kernel, by decide +kernel⟩

def f2196 : Formula := .mul f2185 f2185
def num2196 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x2000000000000000000000000000200000000000000000000000000040, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000002400000000000000000000000000200000000000000000000000000010, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000c00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x10, 0x0, 1⟩,
  ⟨5, 2, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000008, 1⟩,
  ⟨6, 2, 3, 0x200000000000000000000000000020000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x1, 0x0, 1⟩
]

def den2196 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2196 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2196 : Fraction := ⟨num2196, den2196⟩
theorem h2196 : Reduced f2196 p2196 := .mul h2185 h2185 ⟨cancel2196, by decide +kernel, by decide +kernel⟩

def f2197 : Formula := .add f2195 f2196
def num2197 : Expr := .bands [
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

def den2197 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2197 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p2197 : Fraction := ⟨num2197, den2197⟩
theorem h2197 : Reduced f2197 p2197 := .add h2195 h2196 ⟨cancel2197, by decide +kernel, by decide +kernel⟩

def f2198 : Formula := .mul f2174 f2197
def num2198 : Expr := .bands [
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

def den2198 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x8, 1⟩,
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2198 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2198 : Fraction := ⟨num2198, den2198⟩
theorem h2198 : Reduced f2198 p2198 := .mul h2174 h2197 ⟨cancel2198, by decide +kernel, by decide +kernel⟩

def f2199 : Formula := .mul f10 f75
def num2199 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def den2199 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2199 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2199 : Fraction := ⟨num2199, den2199⟩
theorem h2199 : Reduced f2199 p2199 := .mul h10 h75 ⟨cancel2199, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
