import MetricWitness051

namespace SchwarzschildMixtures.MetricWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2080 : Formula := .mul f2079 f1791
def num2080 : Expr := .bands [
  ⟨3, 2, 3, 0x40000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2080 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2080 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2080 : Fraction := ⟨num2080, den2080⟩
theorem h2080 : Reduced f2080 p2080 := .mul h2079 h1791 ⟨cancel2080, by decide +kernel, by decide +kernel⟩

def f2081 : Formula := .mul f61 f84
def num2081 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def den2081 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2081 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2081 : Fraction := ⟨num2081, den2081⟩
theorem h2081 : Reduced f2081 p2081 := .mul h61 h84 ⟨cancel2081, by decide +kernel, by decide +kernel⟩

def f2082 : Formula := .div f2080 f2081
def num2082 : Expr := .bands [
  ⟨0, 2, 3, 0x40000000000000000000000000000, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2082 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2082 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2082 : Fraction := ⟨num2082, den2082⟩
theorem h2082 : Reduced f2082 p2082 := .div h2080 h2081 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2082, by decide +kernel, by decide +kernel⟩

def f2083 : Formula := .neg f2082
def p2083 : Fraction := p2082.neg
theorem h2083 : Reduced f2083 p2083 := .neg h2082

def f2084 : Formula := .add f2077 f2083
def num2084 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x3000000000000000000000000000100000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000003400000000000000000000000000100000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0xc0000000000000000000000000010000000000000000000000000001000000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2084 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2084 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 1, 0x10, 0x0, 1⟩
]

def p2084 : Fraction := ⟨num2084, den2084⟩
theorem h2084 : Reduced f2084 p2084 := .add h2077 h2083 ⟨cancel2084, by decide +kernel, by decide +kernel⟩

def f2085 : Formula := .mul f1443 f2
def num2085 : Expr := .bands [
  ⟨1, 0, 2, 0x20000000000000000000000000000, 0x0, 1⟩
]

def den2085 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2085 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2085 : Fraction := ⟨num2085, den2085⟩
theorem h2085 : Reduced f2085 p2085 := .mul h1443 h2 ⟨cancel2085, by decide +kernel, by decide +kernel⟩

def f2086 : Formula := .add f2085 f18
def num2086 : Expr := .bands [
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den2086 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2086 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2086 : Fraction := ⟨num2086, den2086⟩
theorem h2086 : Reduced f2086 p2086 := .add h2085 h18 ⟨cancel2086, by decide +kernel, by decide +kernel⟩

def f2087 : Formula := .neg f2070
def p2087 : Fraction := p2070.neg
theorem h2087 : Reduced f2087 p2087 := .neg h2070

def f2088 : Formula := .add f2086 f2087
def num2088 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x30000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den2088 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2088 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2088 : Fraction := ⟨num2088, den2088⟩
theorem h2088 : Reduced f2088 p2088 := .add h2086 h2087 ⟨cancel2088, by decide +kernel, by decide +kernel⟩

def f2089 : Formula := .add f2088 f19
def num2089 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x30000000000000000000000000002, 1⟩,
  ⟨1, 0, 2, 0x20000000000000000000000000001, 0x0, 1⟩
]

def den2089 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2089 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2089 : Fraction := ⟨num2089, den2089⟩
theorem h2089 : Reduced f2089 p2089 := .add h2088 h19 ⟨cancel2089, by decide +kernel, by decide +kernel⟩

def f2090 : Formula := .mul f2 f2089
def num2090 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2090 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2090 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2090 : Fraction := ⟨num2090, den2090⟩
theorem h2090 : Reduced f2090 p2090 := .mul h2 h2089 ⟨cancel2090, by decide +kernel, by decide +kernel⟩

def f2091 : Formula := .mul f1105 f1105
def num2091 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den2091 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2091 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2091 : Fraction := ⟨num2091, den2091⟩
theorem h2091 : Reduced f2091 p2091 := .mul h1105 h1105 ⟨cancel2091, by decide +kernel, by decide +kernel⟩

def f2092 : Formula := .mul f2090 f2091
def num2092 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x14000000000000000000000000000c0000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0xb00000000000000000000000000060000000000000000000000000000, 1⟩,
  ⟨3, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2092 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2092 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2092 : Fraction := ⟨num2092, den2092⟩
theorem h2092 : Reduced f2092 p2092 := .mul h2090 h2091 ⟨cancel2092, by decide +kernel, by decide +kernel⟩

def f2093 : Formula := .mul f1 f79
def num2093 : Expr := .bands [
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def den2093 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2093 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2093 : Fraction := ⟨num2093, den2093⟩
theorem h2093 : Reduced f2093 p2093 := .mul h1 h79 ⟨cancel2093, by decide +kernel, by decide +kernel⟩

def f2094 : Formula := .mul f20 f20
def num2094 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def den2094 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2094 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2094 : Fraction := ⟨num2094, den2094⟩
theorem h2094 : Reduced f2094 p2094 := .mul h20 h20 ⟨cancel2094, by decide +kernel, by decide +kernel⟩

def f2095 : Formula := .mul f2093 f2094
def num2095 : Expr := .bands [
  ⟨2, 0, 1, 0x8, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x8, 1⟩,
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def den2095 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2095 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2095 : Fraction := ⟨num2095, den2095⟩
theorem h2095 : Reduced f2095 p2095 := .mul h2093 h2094 ⟨cancel2095, by decide +kernel, by decide +kernel⟩

def f2096 : Formula := .div f2092 f2095
def num2096 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x200000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2096 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2096 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x4, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2096 : Fraction := ⟨num2096, den2096⟩
theorem h2096 : Reduced f2096 p2096 := .div h2092 h2095 [.integer (2), .radius, .radius, .horizon, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2096, by decide +kernel, by decide +kernel⟩

def f2097 : Formula := .neg f2096
def p2097 : Fraction := p2096.neg
theorem h2097 : Reduced f2097 p2097 := .neg h2096

def f2098 : Formula := .add f2084 f2097
def num2098 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2098 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2098 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def p2098 : Fraction := ⟨num2098, den2098⟩
theorem h2098 : Reduced f2098 p2098 := .add h2084 h2097 ⟨cancel2098, by decide +kernel, by decide +kernel⟩

def f2099 : Formula := .mul f18 f2
def num2099 : Expr := .bands [
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2099 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2099 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2099 : Fraction := ⟨num2099, den2099⟩
theorem h2099 : Reduced f2099 p2099 := .mul h18 h2 ⟨cancel2099, by decide +kernel, by decide +kernel⟩

def f2100 : Formula := .neg f3
def p2100 : Fraction := p3.neg
theorem h2100 : Reduced f2100 p2100 := .neg h3

def f2101 : Formula := .add f2099 f2100
def num2101 : Expr := .bands [
  ⟨0, 0, 2, 0x0, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2101 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2101 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2101 : Fraction := ⟨num2101, den2101⟩
theorem h2101 : Reduced f2101 p2101 := .add h2099 h2100 ⟨cancel2101, by decide +kernel, by decide +kernel⟩

def f2102 : Formula := .add f2101 f0
def num2102 : Expr := .bands [
  ⟨0, 0, 2, 0x1, 0x20000000000000000000000000000, 1⟩,
  ⟨1, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2102 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2102 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2102 : Fraction := ⟨num2102, den2102⟩
theorem h2102 : Reduced f2102 p2102 := .add h2101 h0 ⟨cancel2102, by decide +kernel, by decide +kernel⟩

def f2103 : Formula := .mul f2 f2102
def num2103 : Expr := .bands [
  ⟨0, 0, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2103 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2103 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2103 : Fraction := ⟨num2103, den2103⟩
theorem h2103 : Reduced f2103 p2103 := .mul h2 h2102 ⟨cancel2103, by decide +kernel, by decide +kernel⟩

def f2104 : Formula := .mul f1769 f1769
def num2104 : Expr := .bands [
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2104 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2104 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2104 : Fraction := ⟨num2104, den2104⟩
theorem h2104 : Reduced f2104 p2104 := .mul h1769 h1769 ⟨cancel2104, by decide +kernel, by decide +kernel⟩

def f2105 : Formula := .mul f2103 f2104
def num2105 : Expr := .bands [
  ⟨4, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2105 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2105 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2105 : Fraction := ⟨num2105, den2105⟩
theorem h2105 : Reduced f2105 p2105 := .mul h2103 h2104 ⟨cancel2105, by decide +kernel, by decide +kernel⟩

def f2106 : Formula := .mul f84 f18
def num2106 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def den2106 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2106 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2106 : Fraction := ⟨num2106, den2106⟩
theorem h2106 : Reduced f2106 p2106 := .mul h84 h18 ⟨cancel2106, by decide +kernel, by decide +kernel⟩

def f2107 : Formula := .mul f1 f2106
def num2107 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def den2107 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2107 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2107 : Fraction := ⟨num2107, den2107⟩
theorem h2107 : Reduced f2107 p2107 := .mul h1 h2106 ⟨cancel2107, by decide +kernel, by decide +kernel⟩

def f2108 : Formula := .div f2105 f2107
def num2108 : Expr := .bands [
  ⟨0, 2, 3, 0x10000000000000000000000000000, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2108 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2108 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def p2108 : Fraction := ⟨num2108, den2108⟩
theorem h2108 : Reduced f2108 p2108 := .div h2105 h2107 [.integer (2), .radius, .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2108, by decide +kernel, by decide +kernel⟩

def f2109 : Formula := .add f2098 f2108
def num2109 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2109 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2109 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x20, 1⟩,
  ⟨2, 0, 1, 0x8, 0x0, 1⟩
]

def p2109 : Fraction := ⟨num2109, den2109⟩
theorem h2109 : Reduced f2109 p2109 := .add h2098 h2108 ⟨cancel2109, by decide +kernel, by decide +kernel⟩

def f2110 : Formula := .mul f33 f2109
def num2110 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc0000000000000000000000000010000000000000000000000000000c00000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000000, 0xc0000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2110 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x18, 1⟩,
  ⟨5, 0, 3, 0x14, 0x1000000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨6, 0, 3, 0x800000000000000000000000000040000000000000000000000000000, 0x4, 1⟩
]

def cancel2110 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x8, 1⟩,
  ⟨1, 0, 1, 0x4, 0x0, 1⟩
]

def p2110 : Fraction := ⟨num2110, den2110⟩
theorem h2110 : Reduced f2110 p2110 := .mul h33 h2109 ⟨cancel2110, by decide +kernel, by decide +kernel⟩

def f2111 : Formula := .div f2 f5
def num2111 : Expr := .bands [
  ⟨0, 0, 2, 0x10000000000000000000000000000, 0x0, 1⟩
]

def den2111 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000000, 0x1, 1⟩
]

def cancel2111 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2111 : Fraction := ⟨num2111, den2111⟩
theorem h2111 : Reduced f2111 p2111 := .div h2 h5 [.twiceMinus] (by decide +kernel) (by decide +kernel) ⟨cancel2111, by decide +kernel, by decide +kernel⟩

def f2112 : Formula := .mul f84 f82
def num2112 : Expr := .bands [
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2112 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2112 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2112 : Fraction := ⟨num2112, den2112⟩
theorem h2112 : Reduced f2112 p2112 := .mul h84 h82 ⟨cancel2112, by decide +kernel, by decide +kernel⟩

def f2113 : Formula := .mul f2 f2
def num2113 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2113 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2113 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2113 : Fraction := ⟨num2113, den2113⟩
theorem h2113 : Reduced f2113 p2113 := .mul h2 h2 ⟨cancel2113, by decide +kernel, by decide +kernel⟩

def f2114 : Formula := .mul f1443 f2113
def num2114 : Expr := .bands [
  ⟨1, 0, 3, 0x200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2114 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2114 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2114 : Fraction := ⟨num2114, den2114⟩
theorem h2114 : Reduced f2114 p2114 := .mul h1443 h2113 ⟨cancel2114, by decide +kernel, by decide +kernel⟩

def f2115 : Formula := .neg f2114
def p2115 : Fraction := p2114.neg
theorem h2115 : Reduced f2115 p2115 := .neg h2114

def f2116 : Formula := .add f2112 f2115
def num2116 : Expr := .bands [
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2116 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2116 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2116 : Fraction := ⟨num2116, den2116⟩
theorem h2116 : Reduced f2116 p2116 := .add h2112 h2115 ⟨cancel2116, by decide +kernel, by decide +kernel⟩

def f2117 : Formula := .neg f2085
def p2117 : Fraction := p2085.neg
theorem h2117 : Reduced f2117 p2117 := .neg h2085

def f2118 : Formula := .add f2116 f2117
def num2118 : Expr := .bands [
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2118 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2118 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2118 : Fraction := ⟨num2118, den2118⟩
theorem h2118 : Reduced f2118 p2118 := .add h2116 h2117 ⟨cancel2118, by decide +kernel, by decide +kernel⟩

def f2119 : Formula := .add f2118 f1443
def num2119 : Expr := .bands [
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2119 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2119 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2119 : Fraction := ⟨num2119, den2119⟩
theorem h2119 : Reduced f2119 p2119 := .add h2118 h1443 ⟨cancel2119, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.MetricWitness
