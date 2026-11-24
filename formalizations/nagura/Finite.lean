import Mathlib.Data.Nat.Prime.Defs

namespace Nagura

private def PrimeByDivisors (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → ¬ d ∣ p

private def intervalProduct (start : Nat) : Nat → Nat
  | 0 => start
  | depth + 1 =>
    intervalProduct start depth * intervalProduct (start + 2 ^ depth) depth

private theorem dvd_intervalProduct (d start depth : Nat)
    (lo : start ≤ d) (hi : d < start + 2 ^ depth) :
    d ∣ intervalProduct start depth := by
  induction depth generalizing start with
  | zero =>
    simp only [Nat.pow_zero] at hi
    have heq : d = start := by omega
    subst d
    exact Nat.dvd_refl start
  | succ depth ih =>
    change d ∣ intervalProduct start depth * intervalProduct (start + 2 ^ depth) depth
    rw [Nat.pow_succ] at hi
    by_cases h : d < start + 2 ^ depth
    · exact Nat.dvd_mul_right_of_dvd (ih start lo h) _
    · exact Nat.dvd_mul_left_of_dvd (ih _ (by omega) (by omega)) _

private theorem prime_of_no_small_divisor (p divisorLimit : Nat)
    (bounds : 2 ≤ p ∧ p < (divisorLimit + 1) * (divisorLimit + 1))
    (nosmall : ∀ d, 2 ≤ d → d ≤ divisorLimit → ¬ d ∣ p) : PrimeByDivisors p := by
  obtain ⟨small, large⟩ := bounds
  refine ⟨small, ?_⟩
  intro d d2 dlt hd
  obtain ⟨q, heq⟩ := hd
  have q2 : 2 ≤ q := by
    by_cases hq : q < 2
    · have choices : q = 0 ∨ q = 1 := by omega
      rcases choices with h | h
      · simp [h] at heq
        omega
      · simp [h] at heq
        omega
    · omega
  by_cases ds : d ≤ divisorLimit
  · exact nosmall d d2 ds ⟨q, heq⟩
  by_cases qs : q ≤ divisorLimit
  · exact nosmall q q2 qs ⟨d, heq.trans (Nat.mul_comm d q)⟩
  have hlarge : (divisorLimit + 1) * (divisorLimit + 1) ≤ d * q :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

private theorem certifiedPrime (depth product p : Nat)
    (productChecked : product = intervalProduct 2 depth)
    (bounds : 2 ≤ p ∧ p < (1 + 2 ^ depth + 1) * (1 + 2 ^ depth + 1))
    (check : Nat.gcd p product = 1) : p.Prime := by
  apply Nat.prime_def_lt'.2
  apply prime_of_no_small_divisor p (1 + 2 ^ depth) bounds
  intro d lo hi dvdP
  have dvdTrial : d ∣ product := by
    rw [productChecked]
    exact dvd_intervalProduct d 2 depth lo (by omega)
  have divides := Nat.dvd_gcd dvdP dvdTrial
  rw [check] at divides
  have eq := Nat.eq_one_of_dvd_one divides
  omega

private def checkProduct3 : Nat := 0x58980

private theorem checkProductValid3 : checkProduct3 = intervalProduct 2 3 := by
  decide +kernel

private def checkProduct6 : Nat := 0x40c815a3daacb61ee8fed306f99401a8ab21b40df96c282d48712a12c1658000000000000000

private theorem checkProductValid6 : checkProduct6 = intervalProduct 2 6 := by
  decide +kernel

private def checkProduct11 : Nat := 0x91b8a2b8c5d4d2e5baa2c7c5558f7af6959bade02ac3afa59794dd2c8520e312f5d300350eb674c56dbe884319e6ea774e7b109bd5d862794893cb5e1e713866e17a11d97d6c751c11c28e481d240da8958e93aa1bf6bdf30e9ab5649c434a5ceba1bbbe67085d03840b8ce7781b1990525f36155162a202e2ce92a2c73cd945926518ada7b1d81c4b29f24b67e1dff3ea7c302234c01f41f2320d6fe7495dadfc97ec794cc835f091ca4e89607a6b82612382e61093f90eee0ea52e134b8785bc1bbedf89ef0bf1990db328e3dd782a50f927b86d845e9ac29b72349c62047b0866100a137ac35d1ad466233e3cf6197361287bd8cfcccca727a8f391f7fb28f89f1e2140045f38ffef1be97bb567417a3f8c2f40326704277a77cf14348519142462df5f5095f8231119705bf14023f93dcae947bf3a217f46fb004da7b62440e559a51567ece05029591dfecce4d964faec81c2dbeae6b0bd3b69fd382591c8d3dcee61e26ccf12924e3409378c9fa55368350c91bf01e6c89496dfeb6999085f3cafcff172a04bfb621f46f6db046e3232dac60ca475067c3ef59764e0bbfb494c791d92dc830756c94dbfaa27691dd43212a3515c42db42d5f8d643feb470196bc6521726d122d2367f3384a42ff0da27dfd1d15b72023823fee1fead4c1135bc6393b3ad32c26281d5978f1ba3d9eb27e96810ff73ec210c828448798b059048f3e9d0b826454383f0762659a83d50b6ae0d0bcff3f3748bf61cbc8ab8f83e08088bb0ea5ca5fb46a9aa800a974ae4d065c0c1740cc23dee815d1ecf55966fc668986268cf427690508d52c89abe66a9010f3949cb8186f6f386a7028f70ee4829cfa13ed217919b2553d222fcca46857c14394fd4f7615cd054753dacd2909620b388665901e949b7cdb7c5f483082c0956e7064349306c1836a57442586a6b14b5f69e2ade980ebc6e39893ad132b19ca057039553b51e7cba3eec22170aed64ad0a74348dff5ae9897ff40b1d05aedbbe4c6c0b60446ff340c6c9aa64d18287f13753083cf8b9884648fbe85becc2949d6909732c9526847ea338e8defcab1ff1a37df270ce32db38d098dacd0b70edd534a7a64214c0c238db625176c16c8226288220705f22e5fc60c6575c737f265d3fc8fce0530f241237dcabaf13669d6f94ed0d3ceb73c79a25f8c26a3a7c165e16ca830ec46a6a22489d202e8d58a5ea9d582c536508e4ccb7dcbeed3d581d1c12282d3ded84eabc991dd0d5bcb7d91dcab14af41c4b823d7b8e5b622863b8b5dfad628cf849098716d2627798343bb7331da15f8b6c62153f1cd64a29a595d5fcbfa32ed9530e3f8a71af103a19aaef08a046a4627a2ff667fd4214166dd3644218705d18beb771a869171f6d40f707216a64568c24e48216b729c560c9fe55aa987e0a602845e83aaab864dd500c1fbdafe37664ac766e3d7166322628eb6ea956c8384c003452884c023aa92a8481d99f489e4a19c94731464524e02127a1cc9fec12eb62549ed9b1e82c1f8f89997748f4b7e84453f220fe859465c32868970587571af69d463c3606a851b14081ca162a2fb7104e1371a18dc23db14d0fff6bb90e6040ded1fd1e1806b93e20e24b439874ab4018be96d643a9ef6623bd24240a9f18877a11dc86f67f1347a8e262bb40aa9c5c076a752b5b3c526587efad7020dc20b38b25ee1f8855e32fc66ea370d833f510822d1360db5b48b6ec15cae106b5ac17ee3ba8b820e59347a423cae861c0fd4b6e692579d3b39b0653c27e02b619e329fa7a7147699926c040787f775582b8798236643b2275d624f5ee133b7d46dd9e8171a26f19cc53da5dd1051f9144e44c8ca7e4c6b35bd0ba8f404e46064a80b9787fe35f4cfd4688d5eec602824c470045743ca69c0c2df1e256c43f413fda86e29d6da8b41eb97a04602c6dc9c6d3a2001f4713f325a9d97a4dd5d7ff234ead111610a6d50975ec34d2cde36a6d0d89219d29d4f71a795071b8d6251fd2164ea5df8ba28b9601b3f773eb8042b86047799942698794a33726e950a014f3fd44ccc7d52ec2023a88f5ea0ce2e4ed29657c3a7deeb8d35aacb36cbf1c4b3c382d5eb2dd570161e7cda0c13a0d3caa6e3ae3a72c7d3cd1516c9b30c6a249088a36fb31c8d2424dd118433d13d2bb027311f0e3c672a4712647f4bf4f125c8d193ab3a5016d905b2dbadbdc8cac1b2cef23ad687b002ce7391be0bef4513facda8e78d18ec5e7b0304526cbf3a3669ee7483f420f06f26df9b52f8156ea2807cd8e99d1b3124acf2c8d38caadc5b59c2a795fafbd53a18e77e8821efc893c067e731a02c728b826af852631e4c118e1e72e8ea8fd0562fa4810a035007876c12cd4d1b7a439cee9d66c3740466a23f3a36e025ca16dab41240a842db52a178e94407ed21cababf4db6e0f47ac645c50f68fe4600a7702e4e15b85b8df715de08b62e87fb53d4638a4584d300acb41e6b239e9a5022f9c06cfe9f2ebc7f169c298f68c65ed0384a365d227b3c5139ac9321ed5ddea4ee1d7161e413e94fa1088809f92f53bcaadf33a50823922f32b141230fd4256ba91f9e3bf4fc777b3fad440d936518d833b70ba7c3baa83ede943f810db8e51592dd7bf29018d6dac25a0dfbda01dbeec5df7dd5f55c366c37bf3ffb5755e32e82df52240c852281addf583d09e565cc1c0cb1eab0cff13e2cd97f5c6c7360c554c9876fefc2df9165416d33e27e0faca71dc3ace727a0ba64f8216c176aaa45cffa72572e6427df65fef65a767e0009ba2558022c38b2908917459dbd41a4cd669e1d8a5d0adc63108c034e8e414ca1f09d5dd05fa50c6e64bf741926ffbced5be3476cac077f1f5c0299b2952d0cb89ef96a766b0ba64885b3dd5fb0f2636572eb639ffc9fc1b76a9f9cd4145e64c0b36188a181547ecbfc0f73c9b17c59517c3959e4201dbc9eda5bd266d7d4e7fe4d31d830a04f2e0b9e2fda56f0377649c985340c4609338f3cffc86e4c68adfa802fc7fa6a8d92230959aca470de6335a47d1cf98d8bee0339177a32feee4fd0bf9acdf36d243b12aa48d443b3562b6994f4580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private theorem checkProductValid11 : checkProduct11 = intervalProduct 2 11 := by
  decide +kernel

private def Covers (a b : Nat) : Prop :=
  ∀ x : Nat, a ≤ x → x < b → ∃ p : Nat, p.Prime ∧ x < p ∧ 5 * p < 6 * x

private theorem onePrime {a p : Nat} (prime : p.Prime) (upper : 5 * p < 6 * a) :
    Covers a p := by
  intro x hx hpx
  exact ⟨p, prime, hpx, by omega⟩

private theorem join {a b c : Nat} (left : Covers a b) (right : Covers b c) :
    Covers a c := by
  intro x hx hcx
  by_cases h : x < b
  · exact left x hx h
  · exact right x (by omega) hcx

private theorem interval1 : Covers 25 29 :=
  onePrime (certifiedPrime 3 checkProduct3 29 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval2 : Covers 29 31 :=
  onePrime (certifiedPrime 3 checkProduct3 31 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval3 : Covers 31 37 :=
  onePrime (certifiedPrime 3 checkProduct3 37 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval4 : Covers 37 43 :=
  onePrime (certifiedPrime 3 checkProduct3 43 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval5 : Covers 43 47 :=
  onePrime (certifiedPrime 3 checkProduct3 47 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval6 : Covers 47 53 :=
  onePrime (certifiedPrime 3 checkProduct3 53 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval7 : Covers 53 61 :=
  onePrime (certifiedPrime 3 checkProduct3 61 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval8 : Covers 61 73 :=
  onePrime (certifiedPrime 3 checkProduct3 73 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval9 : Covers 73 83 :=
  onePrime (certifiedPrime 3 checkProduct3 83 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval10 : Covers 83 97 :=
  onePrime (certifiedPrime 3 checkProduct3 97 checkProductValid3 (by decide) (by decide +kernel)) (by decide)

private theorem interval11 : Covers 97 113 :=
  onePrime (certifiedPrime 6 checkProduct6 113 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval12 : Covers 113 131 :=
  onePrime (certifiedPrime 6 checkProduct6 131 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval13 : Covers 131 157 :=
  onePrime (certifiedPrime 6 checkProduct6 157 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval14 : Covers 157 181 :=
  onePrime (certifiedPrime 6 checkProduct6 181 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval15 : Covers 181 211 :=
  onePrime (certifiedPrime 6 checkProduct6 211 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval16 : Covers 211 251 :=
  onePrime (certifiedPrime 6 checkProduct6 251 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval17 : Covers 251 293 :=
  onePrime (certifiedPrime 6 checkProduct6 293 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval18 : Covers 293 349 :=
  onePrime (certifiedPrime 6 checkProduct6 349 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval19 : Covers 349 409 :=
  onePrime (certifiedPrime 6 checkProduct6 409 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval20 : Covers 409 487 :=
  onePrime (certifiedPrime 6 checkProduct6 487 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval21 : Covers 487 577 :=
  onePrime (certifiedPrime 6 checkProduct6 577 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval22 : Covers 577 691 :=
  onePrime (certifiedPrime 6 checkProduct6 691 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval23 : Covers 691 829 :=
  onePrime (certifiedPrime 6 checkProduct6 829 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval24 : Covers 829 991 :=
  onePrime (certifiedPrime 6 checkProduct6 991 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval25 : Covers 991 1187 :=
  onePrime (certifiedPrime 6 checkProduct6 1187 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval26 : Covers 1187 1423 :=
  onePrime (certifiedPrime 6 checkProduct6 1423 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval27 : Covers 1423 1699 :=
  onePrime (certifiedPrime 6 checkProduct6 1699 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval28 : Covers 1699 2029 :=
  onePrime (certifiedPrime 6 checkProduct6 2029 checkProductValid6 (by decide) (by decide +kernel)) (by decide)

private theorem interval29 : Covers 2029 2423 :=
  onePrime (certifiedPrime 11 checkProduct11 2423 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval30 : Covers 2423 2903 :=
  onePrime (certifiedPrime 11 checkProduct11 2903 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval31 : Covers 2903 3469 :=
  onePrime (certifiedPrime 11 checkProduct11 3469 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval32 : Covers 3469 4159 :=
  onePrime (certifiedPrime 11 checkProduct11 4159 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval33 : Covers 4159 4987 :=
  onePrime (certifiedPrime 11 checkProduct11 4987 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval34 : Covers 4987 5981 :=
  onePrime (certifiedPrime 11 checkProduct11 5981 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval35 : Covers 5981 7177 :=
  onePrime (certifiedPrime 11 checkProduct11 7177 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval36 : Covers 7177 8609 :=
  onePrime (certifiedPrime 11 checkProduct11 8609 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval37 : Covers 8609 10321 :=
  onePrime (certifiedPrime 11 checkProduct11 10321 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval38 : Covers 10321 12379 :=
  onePrime (certifiedPrime 11 checkProduct11 12379 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval39 : Covers 12379 14851 :=
  onePrime (certifiedPrime 11 checkProduct11 14851 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval40 : Covers 14851 17807 :=
  onePrime (certifiedPrime 11 checkProduct11 17807 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval41 : Covers 17807 21347 :=
  onePrime (certifiedPrime 11 checkProduct11 21347 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval42 : Covers 21347 25609 :=
  onePrime (certifiedPrime 11 checkProduct11 25609 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval43 : Covers 25609 30727 :=
  onePrime (certifiedPrime 11 checkProduct11 30727 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval44 : Covers 30727 36871 :=
  onePrime (certifiedPrime 11 checkProduct11 36871 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval45 : Covers 36871 44221 :=
  onePrime (certifiedPrime 11 checkProduct11 44221 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval46 : Covers 44221 53051 :=
  onePrime (certifiedPrime 11 checkProduct11 53051 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval47 : Covers 53051 63659 :=
  onePrime (certifiedPrime 11 checkProduct11 63659 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval48 : Covers 63659 76387 :=
  onePrime (certifiedPrime 11 checkProduct11 76387 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval49 : Covers 76387 91639 :=
  onePrime (certifiedPrime 11 checkProduct11 91639 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval50 : Covers 91639 109961 :=
  onePrime (certifiedPrime 11 checkProduct11 109961 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval51 : Covers 109961 131947 :=
  onePrime (certifiedPrime 11 checkProduct11 131947 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval52 : Covers 131947 158329 :=
  onePrime (certifiedPrime 11 checkProduct11 158329 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval53 : Covers 158329 189989 :=
  onePrime (certifiedPrime 11 checkProduct11 189989 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval54 : Covers 189989 227977 :=
  onePrime (certifiedPrime 11 checkProduct11 227977 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval55 : Covers 227977 273569 :=
  onePrime (certifiedPrime 11 checkProduct11 273569 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval56 : Covers 273569 328277 :=
  onePrime (certifiedPrime 11 checkProduct11 328277 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval57 : Covers 328277 393931 :=
  onePrime (certifiedPrime 11 checkProduct11 393931 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval58 : Covers 393931 472711 :=
  onePrime (certifiedPrime 11 checkProduct11 472711 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval59 : Covers 472711 567209 :=
  onePrime (certifiedPrime 11 checkProduct11 567209 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval60 : Covers 567209 680633 :=
  onePrime (certifiedPrime 11 checkProduct11 680633 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval61 : Covers 680633 816743 :=
  onePrime (certifiedPrime 11 checkProduct11 816743 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval62 : Covers 816743 980081 :=
  onePrime (certifiedPrime 11 checkProduct11 980081 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval63 : Covers 980081 1176089 :=
  onePrime (certifiedPrime 11 checkProduct11 1176089 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval64 : Covers 1176089 1411297 :=
  onePrime (certifiedPrime 11 checkProduct11 1411297 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval65 : Covers 1411297 1693553 :=
  onePrime (certifiedPrime 11 checkProduct11 1693553 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

private theorem interval66 : Covers 1693553 2032253 :=
  onePrime (certifiedPrime 11 checkProduct11 2032253 checkProductValid11 (by decide) (by decide +kernel)) (by decide)

theorem finite (x : Nat) (hx : 25 ≤ x) (hx' : x < 2000000) :
    ∃ p : Nat, p.Prime ∧ x < p ∧ 5 * p < 6 * x :=
  (join (join (join (join (join (join interval1 interval2) (join interval3 interval4)) (join (join interval5 interval6) (join interval7 interval8))) (join (join (join interval9 interval10) (join interval11 interval12)) (join (join interval13 interval14) (join interval15 interval16)))) (join (join (join (join interval17 interval18) (join interval19 interval20)) (join (join interval21 interval22) (join interval23 interval24))) (join (join (join interval25 interval26) (join interval27 interval28)) (join (join interval29 interval30) (join interval31 (join interval32 interval33)))))) (join (join (join (join (join interval34 interval35) (join interval36 interval37)) (join (join interval38 interval39) (join interval40 interval41))) (join (join (join interval42 interval43) (join interval44 interval45)) (join (join interval46 interval47) (join interval48 interval49)))) (join (join (join (join interval50 interval51) (join interval52 interval53)) (join (join interval54 interval55) (join interval56 interval57))) (join (join (join interval58 interval59) (join interval60 interval61)) (join (join interval62 interval63) (join interval64 (join interval65 interval66))))))) x hx (by omega)

#print axioms finite

end Nagura
