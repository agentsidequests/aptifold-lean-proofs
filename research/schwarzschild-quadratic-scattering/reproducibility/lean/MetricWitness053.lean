import MetricWitness052

namespace SchwarzschildMixtures.MetricWitness
open ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2120 : Formula := .mul f61 f2113
def num2120 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2120 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2120 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2120 : Fraction := ⟨num2120, den2120⟩
theorem h2120 : Reduced f2120 p2120 := .mul h61 h2113 ⟨cancel2120, by decide +kernel, by decide +kernel⟩

def f2121 : Formula := .add f2119 f2120
def num2121 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2121 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2121 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2121 : Fraction := ⟨num2121, den2121⟩
theorem h2121 : Reduced f2121 p2121 := .add h2119 h2120 ⟨cancel2121, by decide +kernel, by decide +kernel⟩

def f2122 : Formula := .mul f61 f2
def num2122 : Expr := .bands [
  ⟨0, 0, 2, 0x40000000000000000000000000000, 0x0, 1⟩
]

def den2122 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2122 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2122 : Fraction := ⟨num2122, den2122⟩
theorem h2122 : Reduced f2122 p2122 := .mul h61 h2 ⟨cancel2122, by decide +kernel, by decide +kernel⟩

def f2123 : Formula := .add f2121 f2122
def num2123 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2123 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2123 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2123 : Fraction := ⟨num2123, den2123⟩
theorem h2123 : Reduced f2123 p2123 := .add h2121 h2122 ⟨cancel2123, by decide +kernel, by decide +kernel⟩

def f2124 : Formula := .add f2123 f2011
def num2124 : Expr := .bands [
  ⟨0, 0, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨1, 0, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨3, 2, 1, 0x1, 0x0, 1⟩
]

def den2124 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2124 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2124 : Fraction := ⟨num2124, den2124⟩
theorem h2124 : Reduced f2124 p2124 := .add h2123 h2011 ⟨cancel2124, by decide +kernel, by decide +kernel⟩

def f2125 : Formula := .mul f2124 f2104
def num2125 : Expr := .bands [
  ⟨4, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨7, 4, 1, 0x1, 0x0, 1⟩
]

def den2125 : Expr := .bands [
  ⟨0, 0, 1, 0x10, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x10, 1⟩,
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2125 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2125 : Fraction := ⟨num2125, den2125⟩
theorem h2125 : Reduced f2125 p2125 := .mul h2124 h2104 ⟨cancel2125, by decide +kernel, by decide +kernel⟩

def f2126 : Formula := .div f2125 f2081
def num2126 : Expr := .bands [
  ⟨1, 2, 3, 0x400000000000000000000000000040000000000000000000000000000, 0x4, 1⟩,
  ⟨2, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x1, 0x0, 1⟩
]

def den2126 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x40, 1⟩,
  ⟨2, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2126 : Expr := .bands [
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def p2126 : Fraction := ⟨num2126, den2126⟩
theorem h2126 : Reduced f2126 p2126 := .div h2125 h2081 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2126, by decide +kernel, by decide +kernel⟩

def f2127 : Formula := .mul f14 f1768
def num2127 : Expr := .bands [
  ⟨0, 1, 1, 0x8, 0x0, 1⟩,
  ⟨1, 1, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 1, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 3, 1, 0x1, 0x0, 1⟩
]

def den2127 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x2, 1⟩,
  ⟨3, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2127 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2127 : Fraction := ⟨num2127, den2127⟩
theorem h2127 : Reduced f2127 p2127 := .mul h14 h1768 ⟨cancel2127, by decide +kernel, by decide +kernel⟩

def f2128 : Formula := .mul f2127 f1769
def num2128 : Expr := .bands [
  ⟨0, 2, 1, 0x0, 0x8, 1⟩,
  ⟨1, 2, 3, 0x200000000000000000000000000020000000000000000000000000004, 0x0, 1⟩,
  ⟨2, 2, 3, 0x0, 0x100000000000000000000000000010000000000000000000000000000, 1⟩,
  ⟨4, 4, 1, 0x0, 0x1, 1⟩
]

def den2128 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2128 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2128 : Fraction := ⟨num2128, den2128⟩
theorem h2128 : Reduced f2128 p2128 := .mul h2127 h1769 ⟨cancel2128, by decide +kernel, by decide +kernel⟩

def f2129 : Formula := .mul f1768 f1768
def num2129 : Expr := .bands [
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

def den2129 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2129 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2129 : Fraction := ⟨num2129, den2129⟩
theorem h2129 : Reduced f2129 p2129 := .mul h1768 h1768 ⟨cancel2129, by decide +kernel, by decide +kernel⟩

def f2130 : Formula := .add f2128 f2129
def num2130 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x2000000000000000000000000000200000000000000000000000000040, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000002400000000000000000000000000200000000000000000000000000010, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000c00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den2130 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2130 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x8, 1⟩,
  ⟨2, 0, 1, 0x2, 0x0, 1⟩
]

def p2130 : Fraction := ⟨num2130, den2130⟩
theorem h2130 : Reduced f2130 p2130 := .add h2128 h2129 ⟨cancel2130, by decide +kernel, by decide +kernel⟩

def f2131 : Formula := .div f2130 f61
def num2131 : Expr := .bands [
  ⟨0, 0, 1, 0x40, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x2000000000000000000000000000200000000000000000000000000040, 1⟩,
  ⟨2, 0, 5, 0x40000000000000000000000000008000000000000000000000000002400000000000000000000000000200000000000000000000000000010, 0x0, 1⟩,
  ⟨3, 0, 5, 0x0, 0x40000000000000000000000000008000000000000000000000000000c00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨4, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨8, 4, 1, 0x0, 0x1, 1⟩
]

def den2131 : Expr := .bands [
  ⟨4, 0, 1, 0x40, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2131 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2131 : Fraction := ⟨num2131, den2131⟩
theorem h2131 : Reduced f2131 p2131 := .div h2130 h61 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel2131, by decide +kernel, by decide +kernel⟩

def f2132 : Formula := .add f2126 f2131
def num2132 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x20, 1⟩,
  ⟨1, 0, 3, 0x1000000000000000000000000000100000000000000000000000000010, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x20000000000000000000000000004000000000000000000000000000a00000000000000000000000000080000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2132 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2132 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x80, 1⟩,
  ⟨1, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨2, 0, 1, 0x0, 0x60, 1⟩,
  ⟨3, 0, 1, 0x10, 0x0, 1⟩
]

def p2132 : Fraction := ⟨num2132, den2132⟩
theorem h2132 : Reduced f2132 p2132 := .add h2126 h2131 ⟨cancel2132, by decide +kernel, by decide +kernel⟩

def f2133 : Formula := .mul f13 f1105
def num2133 : Expr := .bands [
  ⟨0, 1, 1, 0x0, 0x2, 1⟩,
  ⟨1, 1, 1, 0x1, 0x0, 1⟩
]

def den2133 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2133 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2133 : Fraction := ⟨num2133, den2133⟩
theorem h2133 : Reduced f2133 p2133 := .mul h13 h1105 ⟨cancel2133, by decide +kernel, by decide +kernel⟩

def f2134 : Formula := .mul f2133 f1769
def num2134 : Expr := .bands [
  ⟨1, 2, 1, 0x0, 0x1, 1⟩
]

def den2134 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2134 : Expr := .bands [
  ⟨1, 0, 1, 0x0, 0x2, 1⟩,
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2134 : Fraction := ⟨num2134, den2134⟩
theorem h2134 : Reduced f2134 p2134 := .mul h2133 h1769 ⟨cancel2134, by decide +kernel, by decide +kernel⟩

def f2135 : Formula := .mul f1105 f1768
def num2135 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩,
  ⟨4, 2, 1, 0x1, 0x0, 1⟩
]

def den2135 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2135 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2135 : Fraction := ⟨num2135, den2135⟩
theorem h2135 : Reduced f2135 p2135 := .mul h1105 h1768 ⟨cancel2135, by decide +kernel, by decide +kernel⟩

def f2136 : Formula := .add f2134 f2135
def num2136 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2136 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2136 : Expr := .bands [
  ⟨0, 0, 1, 0x4, 0x0, 1⟩
]

def p2136 : Fraction := ⟨num2136, den2136⟩
theorem h2136 : Reduced f2136 p2136 := .add h2134 h2135 ⟨cancel2136, by decide +kernel, by decide +kernel⟩

def f2137 : Formula := .div f2136 f18
def num2137 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000004, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2137 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2137 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2137 : Fraction := ⟨num2137, den2137⟩
theorem h2137 : Reduced f2137 p2137 := .div h2136 h18 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel2137, by decide +kernel, by decide +kernel⟩

def f2138 : Formula := .neg f2137
def p2138 : Fraction := p2137.neg
theorem h2138 : Reduced f2138 p2138 := .neg h2137

def f2139 : Formula := .add f2132 f2138
def num2139 : Expr := .bands [
  ⟨0, 0, 1, 0x20, 0x0, 1⟩,
  ⟨1, 0, 1, 0x0, 0x30, 1⟩,
  ⟨2, 0, 5, 0x600000000000000000000000000080000000000000000000000000010, 0x20000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨3, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000040000000000000000000000000000, 1⟩,
  ⟨5, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2139 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x20, 1⟩,
  ⟨5, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2139 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def p2139 : Fraction := ⟨num2139, den2139⟩
theorem h2139 : Reduced f2139 p2139 := .add h2132 h2138 ⟨cancel2139, by decide +kernel, by decide +kernel⟩

def f2140 : Formula := .mul f18 f2113
def num2140 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2140 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2140 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2140 : Fraction := ⟨num2140, den2140⟩
theorem h2140 : Reduced f2140 p2140 := .mul h18 h2113 ⟨cancel2140, by decide +kernel, by decide +kernel⟩

def f2141 : Formula := .add f2140 f2099
def num2141 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x0, 1⟩
]

def den2141 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2141 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2141 : Fraction := ⟨num2141, den2141⟩
theorem h2141 : Reduced f2141 p2141 := .add h2140 h2099 ⟨cancel2141, by decide +kernel, by decide +kernel⟩

def f2142 : Formula := .add f2141 f18
def num2142 : Expr := .bands [
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2142 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2142 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2142 : Fraction := ⟨num2142, den2142⟩
theorem h2142 : Reduced f2142 p2142 := .add h2141 h18 ⟨cancel2142, by decide +kernel, by decide +kernel⟩

def f2143 : Formula := .add f2142 f2011
def num2143 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2143 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2143 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2143 : Fraction := ⟨num2143, den2143⟩
theorem h2143 : Reduced f2143 p2143 := .add h2142 h2011 ⟨cancel2143, by decide +kernel, by decide +kernel⟩

def f2144 : Formula := .mul f2143 f2091
def num2144 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x10, 1⟩,
  ⟨1, 0, 3, 0x400000000000000000000000000040000000000000000000000000014, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x400000000000000000000000000040000000000000000000000000008, 1⟩,
  ⟨3, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2144 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2144 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2144 : Fraction := ⟨num2144, den2144⟩
theorem h2144 : Reduced f2144 p2144 := .mul h2143 h2091 ⟨cancel2144, by decide +kernel, by decide +kernel⟩

def f2145 : Formula := .mul f1 f20
def num2145 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def den2145 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2145 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2145 : Fraction := ⟨num2145, den2145⟩
theorem h2145 : Reduced f2145 p2145 := .mul h1 h20 ⟨cancel2145, by decide +kernel, by decide +kernel⟩

def f2146 : Formula := .mul f2145 f79
def num2146 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def den2146 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2146 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2146 : Fraction := ⟨num2146, den2146⟩
theorem h2146 : Reduced f2146 p2146 := .mul h2145 h79 ⟨cancel2146, by decide +kernel, by decide +kernel⟩

def f2147 : Formula := .div f2144 f2146
def num2147 : Expr := .bands [
  ⟨0, 0, 1, 0x8, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x200000000000000000000000000020000000000000000000000000006, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2147 : Expr := .bands [
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2147 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2147 : Fraction := ⟨num2147, den2147⟩
theorem h2147 : Reduced f2147 p2147 := .div h2144 h2146 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2147, by decide +kernel, by decide +kernel⟩

def f2148 : Formula := .add f2139 f2147
def num2148 : Expr := .bands [
  ⟨0, 0, 3, 0x800000000000000000000000000080000000000000000000000000000, 0x8, 1⟩,
  ⟨1, 0, 5, 0x0, 0x20000000000000000000000000004000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000002, 0x100000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x2, 0x200000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2148 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x20, 1⟩,
  ⟨4, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2148 : Expr := .bands [
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def p2148 : Fraction := ⟨num2148, den2148⟩
theorem h2148 : Reduced f2148 p2148 := .add h2139 h2147 ⟨cancel2148, by decide +kernel, by decide +kernel⟩

def f2149 : Formula := .mul f2111 f2148
def num2149 : Expr := .bands [
  ⟨0, 0, 4, 0x8000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 0x80000000000000000000000000000, 1⟩,
  ⟨1, 0, 6, 0x0, 0x200000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 6, 0x100000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 4, 0x20000000000000000000000000000, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2149 : Expr := .bands [
  ⟨3, 0, 2, 0x20, 0x400000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x200000000000000000000000000000, 0x10, 1⟩
]

def cancel2149 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2149 : Fraction := ⟨num2149, den2149⟩
theorem h2149 : Reduced f2149 p2149 := .mul h2111 h2148 ⟨cancel2149, by decide +kernel, by decide +kernel⟩

def f2150 : Formula := .mul f301 f2149
def num2150 : Expr := .bands [
  ⟨0, 0, 4, 0x80000000000000000000000000000, 0x8000000000000000000000000000800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 6, 0x200000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 6, 0x1000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨4, 2, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2150 : Expr := .bands [
  ⟨4, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨5, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel2150 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2150 : Fraction := ⟨num2150, den2150⟩
theorem h2150 : Reduced f2150 p2150 := .mul h301 h2149 ⟨cancel2150, by decide +kernel, by decide +kernel⟩

def f2151 : Formula := .mul f11 f84
def num2151 : Expr := .bands [
  ⟨3, 0, 1, 0x3, 0x0, 1⟩
]

def den2151 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2151 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2151 : Fraction := ⟨num2151, den2151⟩
theorem h2151 : Reduced f2151 p2151 := .mul h11 h84 ⟨cancel2151, by decide +kernel, by decide +kernel⟩

def f2152 : Formula := .mul f2151 f82
def num2152 : Expr := .bands [
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2152 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2152 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2152 : Fraction := ⟨num2152, den2152⟩
theorem h2152 : Reduced f2152 p2152 := .mul h2151 h82 ⟨cancel2152, by decide +kernel, by decide +kernel⟩

def f2153 : Formula := .mul f11 f18
def num2153 : Expr := .bands [
  ⟨1, 0, 1, 0x3, 0x0, 1⟩
]

def den2153 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2153 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2153 : Fraction := ⟨num2153, den2153⟩
theorem h2153 : Reduced f2153 p2153 := .mul h11 h18 ⟨cancel2153, by decide +kernel, by decide +kernel⟩

def f2154 : Formula := .mul f2153 f2113
def num2154 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2154 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2154 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2154 : Fraction := ⟨num2154, den2154⟩
theorem h2154 : Reduced f2154 p2154 := .mul h2153 h2113 ⟨cancel2154, by decide +kernel, by decide +kernel⟩

def f2155 : Formula := .add f2152 f2154
def num2155 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2155 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2155 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2155 : Fraction := ⟨num2155, den2155⟩
theorem h2155 : Reduced f2155 p2155 := .add h2152 h2154 ⟨cancel2155, by decide +kernel, by decide +kernel⟩

def f2156 : Formula := .add f2155 f18
def num2156 : Expr := .bands [
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2156 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2156 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2156 : Fraction := ⟨num2156, den2156⟩
theorem h2156 : Reduced f2156 p2156 := .add h2155 h18 ⟨cancel2156, by decide +kernel, by decide +kernel⟩

def f2157 : Formula := .mul f30 f2113
def num2157 : Expr := .bands [
  ⟨0, 0, 3, 0x600000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2157 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2157 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2157 : Fraction := ⟨num2157, den2157⟩
theorem h2157 : Reduced f2157 p2157 := .mul h30 h2113 ⟨cancel2157, by decide +kernel, by decide +kernel⟩

def f2158 : Formula := .neg f2157
def p2158 : Fraction := p2157.neg
theorem h2158 : Reduced f2158 p2158 := .neg h2157

def f2159 : Formula := .add f2156 f2158
def num2159 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x600000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x300000000000000000000000000000000000000000000000000000001, 0x0, 1⟩,
  ⟨3, 2, 1, 0x3, 0x0, 1⟩
]

def den2159 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2159 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2159 : Fraction := ⟨num2159, den2159⟩
theorem h2159 : Reduced f2159 p2159 := .add h2156 h2158 ⟨cancel2159, by decide +kernel, by decide +kernel⟩

end SchwarzschildMixtures.MetricWitness
