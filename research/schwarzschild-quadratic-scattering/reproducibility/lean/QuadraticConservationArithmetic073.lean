import QuadraticConservationArithmetic072

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def f2920 : Formula := .neg f2887
def p2920 : Fraction := p2887.neg
theorem h2920 : Reduced f2920 p2920 := .neg h2887

def f2921 : Formula := .add f2919 f2920
def num2921 : Expr := .bands [
  ⟨0, 0, 4, 0x30000000000000000000000000000, 0x3000000000000000000000000000300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 4, 0x2000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000, 1⟩
]

def den2921 : Expr := .bands [
  ⟨3, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel2921 : Expr := .bands [
  ⟨3, 0, 2, 0x40, 0x800000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x400000000000000000000000000000, 0x20, 1⟩
]

def p2921 : Fraction := ⟨num2921, den2921⟩
theorem h2921 : Reduced f2921 p2921 := .add h2919 h2920 ⟨cancel2921, by decide +kernel, by decide +kernel⟩

def f2922 : Formula := .mul f2867 f2407
def num2922 : Expr := .bands [

]

def den2922 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2922 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2922 : Fraction := ⟨num2922, den2922⟩
theorem h2922 : Reduced f2922 p2922 := .mul h2867 h2407 ⟨cancel2922, by decide +kernel, by decide +kernel⟩

def f2923 : Formula := .div f2922 f2199
def num2923 : Expr := .bands [

]

def den2923 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2923 : Expr := .bands [
  ⟨3, 0, 1, 0x4, 0x0, 1⟩
]

def p2923 : Fraction := ⟨num2923, den2923⟩
theorem h2923 : Reduced f2923 p2923 := .div h2922 h2199 [.integer (4), .radius, .radius, .radius] (by decide +kernel) (by decide +kernel) ⟨cancel2923, by decide +kernel, by decide +kernel⟩

def f2924 : Formula := .mul f2 f2191
def num2924 : Expr := .bands [
  ⟨0, 1, 1, 0x2, 0x0, 1⟩
]

def den2924 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2924 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2924 : Fraction := ⟨num2924, den2924⟩
theorem h2924 : Reduced f2924 p2924 := .mul h2 h2191 ⟨cancel2924, by decide +kernel, by decide +kernel⟩

def f2925 : Formula := .mul f2924 f28
def num2925 : Expr := .bands [

]

def den2925 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2925 : Expr := .bands [
  ⟨2, 0, 1, 0x1, 0x0, 1⟩
]

def p2925 : Fraction := ⟨num2925, den2925⟩
theorem h2925 : Reduced f2925 p2925 := .mul h2924 h28 ⟨cancel2925, by decide +kernel, by decide +kernel⟩

def f2926 : Formula := .add f2925 f2415
def num2926 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2926 : Expr := .bands [
  ⟨4, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2926 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2926 : Fraction := ⟨num2926, den2926⟩
theorem h2926 : Reduced f2926 p2926 := .add h2925 h2415 ⟨cancel2926, by decide +kernel, by decide +kernel⟩

def f2927 : Formula := .div f2926 f10
def num2927 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2927 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2927 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2927 : Fraction := ⟨num2927, den2927⟩
theorem h2927 : Reduced f2927 p2927 := .div h2926 h10 [.integer (4)] (by decide +kernel) (by decide +kernel) ⟨cancel2927, by decide +kernel, by decide +kernel⟩

def f2928 : Formula := .add f2923 f2927
def num2928 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2928 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2928 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2928 : Fraction := ⟨num2928, den2928⟩
theorem h2928 : Reduced f2928 p2928 := .add h2923 h2927 ⟨cancel2928, by decide +kernel, by decide +kernel⟩

def f2929 : Formula := .div f2582 f3
def num2929 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def den2929 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2929 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2929 : Fraction := ⟨num2929, den2929⟩
theorem h2929 : Reduced f2929 p2929 := .div h2582 h3 [.radius] (by decide +kernel) (by decide +kernel) ⟨cancel2929, by decide +kernel, by decide +kernel⟩

def f2930 : Formula := .neg f2929
def p2930 : Fraction := p2929.neg
theorem h2930 : Reduced f2930 p2930 := .neg h2929

def f2931 : Formula := .add f2928 f2930
def num2931 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x1, 1⟩
]

def den2931 : Expr := .bands [
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2931 : Expr := .bands [
  ⟨4, 0, 1, 0x2, 0x0, 1⟩
]

def p2931 : Fraction := ⟨num2931, den2931⟩
theorem h2931 : Reduced f2931 p2931 := .add h2928 h2930 ⟨cancel2931, by decide +kernel, by decide +kernel⟩

def f2932 : Formula := .mul f2881 f2432
def num2932 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2932 : Expr := .bands [
  ⟨2, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2932 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2932 : Fraction := ⟨num2932, den2932⟩
theorem h2932 : Reduced f2932 p2932 := .mul h2881 h2432 ⟨cancel2932, by decide +kernel, by decide +kernel⟩

def f2933 : Formula := .div f2932 f2884
def num2933 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x4, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000010000000000000000000000000001, 0x0, 1⟩
]

def den2933 : Expr := .bands [
  ⟨4, 0, 1, 0x0, 0x10, 1⟩,
  ⟨5, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2933 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2933 : Fraction := ⟨num2933, den2933⟩
theorem h2933 : Reduced f2933 p2933 := .div h2932 h2884 [.integer (2), .radius, .radius, .horizon] (by decide +kernel) (by decide +kernel) ⟨cancel2933, by decide +kernel, by decide +kernel⟩

def f2934 : Formula := .add f2931 f2933
def num2934 : Expr := .bands [
  ⟨0, 0, 3, 0x100000000000000000000000000010000000000000000000000000000, 0x1, 1⟩
]

def den2934 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2934 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p2934 : Fraction := ⟨num2934, den2934⟩
theorem h2934 : Reduced f2934 p2934 := .add h2931 h2933 ⟨cancel2934, by decide +kernel, by decide +kernel⟩

def f2935 : Formula := .mul f2857 f2934
def num2935 : Expr := .bands [
  ⟨0, 0, 4, 0x1000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2935 : Expr := .bands [
  ⟨3, 0, 2, 0x10, 0x200000000000000000000000000000, 1⟩,
  ⟨4, 0, 2, 0x100000000000000000000000000000, 0x8, 1⟩
]

def cancel2935 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2935 : Fraction := ⟨num2935, den2935⟩
theorem h2935 : Reduced f2935 p2935 := .mul h2857 h2934 ⟨cancel2935, by decide +kernel, by decide +kernel⟩

def f2936 : Formula := .neg f2935
def p2936 : Fraction := p2935.neg
theorem h2936 : Reduced f2936 p2936 := .neg h2935

def f2937 : Formula := .add f2921 f2936
def num2937 : Expr := .bands [
  ⟨0, 0, 4, 0x1000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 0x10000000000000000000000000000, 1⟩
]

def den2937 : Expr := .bands [
  ⟨3, 0, 2, 0x80000000000000000000000000000, 0x4, 1⟩
]

def cancel2937 : Expr := .bands [
  ⟨3, 0, 2, 0x800000000000000000000000000000, 0x40, 1⟩,
  ⟨4, 0, 2, 0x40, 0x800000000000000000000000000000, 1⟩,
  ⟨5, 0, 2, 0x200000000000000000000000000000, 0x10, 1⟩
]

def p2937 : Fraction := ⟨num2937, den2937⟩
theorem h2937 : Reduced f2937 p2937 := .add h2921 h2936 ⟨cancel2937, by decide +kernel, by decide +kernel⟩

def f2938 : Formula := .mul f2090 f2937
def num2938 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2938 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2938 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000000, 0x1, 1⟩
]

def p2938 : Fraction := ⟨num2938, den2938⟩
theorem h2938 : Reduced f2938 p2938 := .mul h2090 h2937 ⟨cancel2938, by decide +kernel, by decide +kernel⟩

def f2939 : Formula := .add f2905 f2938
def num2939 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x2400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0xc000000000000000000000000000e000000000000000000000000000600000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x300000000000000000000000000020000000000000000000000000000, 0x50000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2939 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x10, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2939 : Expr := .bands [
  ⟨5, 0, 1, 0x4, 0x0, 1⟩
]

def p2939 : Fraction := ⟨num2939, den2939⟩
theorem h2939 : Reduced f2939 p2939 := .add h2905 h2938 ⟨cancel2939, by decide +kernel, by decide +kernel⟩

def f2940 : Formula := .add f2904 f2939
def num2940 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x9000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x500000000000000000000000000020000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x200000000000000000000000000000000000000000000000000000000, 0x20000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2940 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x10, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2940 : Expr := .bands [
  ⟨6, 0, 1, 0x0, 0x10, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def p2940 : Fraction := ⟨num2940, den2940⟩
theorem h2940 : Reduced f2940 p2940 := .add h2904 h2939 ⟨cancel2940, by decide +kernel, by decide +kernel⟩

def f2941 : Formula := .add f2903 f2940
def num2941 : Expr := .bands [
  ⟨0, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2941 : Expr := .bands [
  ⟨2, 0, 1, 0x0, 0x4, 1⟩,
  ⟨3, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2941 : Expr := .bands [
  ⟨10, 0, 1, 0x0, 0x40, 1⟩,
  ⟨11, 0, 1, 0x20, 0x0, 1⟩
]

def p2941 : Fraction := ⟨num2941, den2941⟩
theorem h2941 : Reduced f2941 p2941 := .add h2903 h2940 ⟨cancel2941, by decide +kernel, by decide +kernel⟩

def f2942 : Formula := .add f2893 f2941
def num2942 : Expr := .bands [

]

def den2942 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2942 : Expr := .bands [
  ⟨4, 0, 1, 0x10, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x4, 0x0, 1⟩
]

def p2942 : Fraction := ⟨num2942, den2942⟩
theorem h2942 : Reduced f2942 p2942 := .add h2893 h2941 ⟨cancel2942, by decide +kernel, by decide +kernel⟩

def f2943 : Formula := .mul f7 f2482
def num2943 : Expr := .bands [
  ⟨0, 2, 3, 0x0, 0x100000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2943 : Expr := .bands [
  ⟨2, 0, 1, 0x10, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2943 : Expr := .bands [
  ⟨1, 0, 1, 0x2, 0x0, 1⟩
]

def p2943 : Fraction := ⟨num2943, den2943⟩
theorem h2943 : Reduced f2943 p2943 := .mul h7 h2482 ⟨cancel2943, by decide +kernel, by decide +kernel⟩

def f2944 : Formula := .dr f2758
def num2944 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x1800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 3, 0x0, 0x500000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2944 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x40, 1⟩,
  ⟨6, 0, 1, 0x60, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x30, 1⟩,
  ⟨8, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2944 : Expr := .bands [
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x8, 0x0, 1⟩
]

def p2944 : Fraction := ⟨num2944, den2944⟩
theorem h2944 : Reduced f2944 p2944 := .dr h2758 ⟨cancel2944, by decide +kernel, by decide +kernel⟩

def f2945 : Formula := .mul f2760 f101
def num2945 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0xc00000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2945 : Expr := .bands [
  ⟨5, 0, 1, 0x40, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x40, 1⟩,
  ⟨7, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2945 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2945 : Fraction := ⟨num2945, den2945⟩
theorem h2945 : Reduced f2945 p2945 := .mul h2760 h101 ⟨cancel2945, by decide +kernel, by decide +kernel⟩

def f2946 : Formula := .add f2944 f2945
def num2946 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x2600000000000000000000000000040000000000000000000000000000, 0x60000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xb00000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2946 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x80, 1⟩,
  ⟨6, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x60, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2946 : Expr := .bands [
  ⟨5, 0, 1, 0x20, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x20, 1⟩,
  ⟨7, 0, 1, 0x8, 0x0, 1⟩
]

def p2946 : Fraction := ⟨num2946, den2946⟩
theorem h2946 : Reduced f2946 p2946 := .add h2944 h2945 ⟨cancel2946, by decide +kernel, by decide +kernel⟩

def f2947 : Formula := .mul f2900 f104
def num2947 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x300000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2947 : Expr := .bands [
  ⟨5, 0, 1, 0x8, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x8, 1⟩,
  ⟨7, 0, 1, 0x2, 0x0, 1⟩
]

def cancel2947 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2947 : Fraction := ⟨num2947, den2947⟩
theorem h2947 : Reduced f2947 p2947 := .mul h2900 h104 ⟨cancel2947, by decide +kernel, by decide +kernel⟩

def f2948 : Formula := .add f2946 f2947
def num2948 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x40000000000000000000000000000, 0x60000000000000000000000000008000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2948 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x80, 1⟩,
  ⟨6, 0, 1, 0xc0, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x60, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2948 : Expr := .bands [
  ⟨5, 0, 1, 0x8, 0x0, 1⟩,
  ⟨6, 0, 1, 0x0, 0x8, 1⟩,
  ⟨7, 0, 1, 0x2, 0x0, 1⟩
]

def p2948 : Fraction := ⟨num2948, den2948⟩
theorem h2948 : Reduced f2948 p2948 := .add h2946 h2947 ⟨cancel2948, by decide +kernel, by decide +kernel⟩

def f2949 : Formula := .mul f6 f2948
def num2949 : Expr := .bands [
  ⟨0, 0, 3, 0x1800000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 5, 0x40000000000000000000000000000, 0x60000000000000000000000000008000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x300000000000000000000000000020000000000000000000000000000, 1⟩
]

def den2949 : Expr := .bands [
  ⟨6, 0, 1, 0x40, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x40, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2949 : Expr := .bands [
  ⟨0, 0, 1, 0x0, 0x2, 1⟩,
  ⟨1, 0, 1, 0x1, 0x0, 1⟩
]

def p2949 : Fraction := ⟨num2949, den2949⟩
theorem h2949 : Reduced f2949 p2949 := .mul h6 h2948 ⟨cancel2949, by decide +kernel, by decide +kernel⟩

def f2950 : Formula := .mul f1168 f2758
def num2950 : Expr := .bands [
  ⟨0, 0, 3, 0x300000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨1, 0, 3, 0x0, 0x400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨2, 0, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2950 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x10, 1⟩,
  ⟨8, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2950 : Expr := .bands [
  ⟨0, 0, 1, 0x2, 0x0, 1⟩
]

def p2950 : Fraction := ⟨num2950, den2950⟩
theorem h2950 : Reduced f2950 p2950 := .mul h1168 h2758 ⟨cancel2950, by decide +kernel, by decide +kernel⟩

def f2951 : Formula := .mul f709 f2825
def num2951 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x2400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x20000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000000000000000, 0x0, 1⟩,
  ⟨2, 0, 5, 0x0, 0x10000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2951 : Expr := .bands [
  ⟨6, 0, 1, 0x40, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x40, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2951 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def p2951 : Fraction := ⟨num2951, den2951⟩
theorem h2951 : Reduced f2951 p2951 := .mul h709 h2825 ⟨cancel2951, by decide +kernel, by decide +kernel⟩

def f2952 : Formula := .mul f2090 f2935
def num2952 : Expr := .bands [
  ⟨0, 0, 5, 0x10000000000000000000000000000, 0x10000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩
]

def den2952 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def cancel2952 : Expr := .bands [
  ⟨0, 0, 2, 0x20000000000000000000000000000, 0x1, 1⟩
]

def p2952 : Fraction := ⟨num2952, den2952⟩
theorem h2952 : Reduced f2952 p2952 := .mul h2090 h2935 ⟨cancel2952, by decide +kernel, by decide +kernel⟩

def f2953 : Formula := .add f2951 f2952
def num2953 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x2400000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000001200000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x20000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2953 : Expr := .bands [
  ⟨6, 0, 1, 0x40, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x40, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2953 : Expr := .bands [
  ⟨5, 0, 1, 0x0, 0x10, 1⟩,
  ⟨6, 0, 1, 0x8, 0x0, 1⟩
]

def p2953 : Fraction := ⟨num2953, den2953⟩
theorem h2953 : Reduced f2953 p2953 := .add h2951 h2952 ⟨cancel2953, by decide +kernel, by decide +kernel⟩

def f2954 : Formula := .add f2950 f2953
def num2954 : Expr := .bands [
  ⟨0, 0, 3, 0x0, 0x1800000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨1, 0, 5, 0x60000000000000000000000000008000000000000000000000000000200000000000000000000000000000000000000000000000000000000, 0x40000000000000000000000000000, 1⟩,
  ⟨2, 0, 5, 0x300000000000000000000000000020000000000000000000000000000, 0x30000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1⟩,
  ⟨4, 2, 3, 0x400000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2954 : Expr := .bands [
  ⟨6, 0, 1, 0x40, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x40, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def cancel2954 : Expr := .bands [
  ⟨6, 0, 1, 0x10, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x10, 1⟩,
  ⟨8, 0, 1, 0x4, 0x0, 1⟩
]

def p2954 : Fraction := ⟨num2954, den2954⟩
theorem h2954 : Reduced f2954 p2954 := .add h2950 h2953 ⟨cancel2954, by decide +kernel, by decide +kernel⟩

def f2955 : Formula := .add f2949 f2954
def num2955 : Expr := .bands [
  ⟨0, 2, 3, 0x100000000000000000000000000000000000000000000000000000000, 0x0, 1⟩
]

def den2955 : Expr := .bands [
  ⟨2, 0, 1, 0x10, 0x0, 1⟩,
  ⟨3, 0, 1, 0x0, 0x10, 1⟩,
  ⟨4, 0, 1, 0x4, 0x0, 1⟩
]

def cancel2955 : Expr := .bands [
  ⟨10, 0, 1, 0x100, 0x0, 1⟩,
  ⟨11, 0, 1, 0x0, 0x100, 1⟩,
  ⟨12, 0, 1, 0x40, 0x0, 1⟩
]

def p2955 : Fraction := ⟨num2955, den2955⟩
theorem h2955 : Reduced f2955 p2955 := .add h2949 h2954 ⟨cancel2955, by decide +kernel, by decide +kernel⟩

def f2956 : Formula := .add f2943 f2955
def num2956 : Expr := .bands [

]

def den2956 : Expr := .bands [
  ⟨0, 0, 1, 0x1, 0x0, 1⟩
]

def cancel2956 : Expr := .bands [
  ⟨4, 0, 1, 0x100, 0x0, 1⟩,
  ⟨5, 0, 1, 0x0, 0x200, 1⟩,
  ⟨6, 0, 1, 0x180, 0x0, 1⟩,
  ⟨7, 0, 1, 0x0, 0x80, 1⟩,
  ⟨8, 0, 1, 0x10, 0x0, 1⟩
]

def p2956 : Fraction := ⟨num2956, den2956⟩
theorem h2956 : Reduced f2956 p2956 := .add h2943 h2955 ⟨cancel2956, by decide +kernel, by decide +kernel⟩

end SchwarzschildEinstein.PureOdd.Master
