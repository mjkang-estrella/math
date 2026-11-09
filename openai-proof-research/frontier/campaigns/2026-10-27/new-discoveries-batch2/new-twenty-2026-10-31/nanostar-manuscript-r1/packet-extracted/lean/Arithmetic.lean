import Definitions
import Mathlib.Tactic.NormNum.Prime
namespace R162
theorem phi_1 : Nat.totient 1 = 1 := Nat.totient_one
theorem phi_2 : Nat.totient 2 = 1 := by
  rw [show 2 = 2^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_3 : Nat.totient 3 = 2 := by
  rw [show 3 = 3^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_4 : Nat.totient 4 = 2 := by
  rw [show 4 = 2^2 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_5 : Nat.totient 5 = 4 := by
  rw [show 5 = 5^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_8 : Nat.totient 8 = 4 := by
  rw [show 8 = 2^3 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_9 : Nat.totient 9 = 6 := by
  rw [show 9 = 3^2 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_11 : Nat.totient 11 = 10 := by
  rw [show 11 = 11^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_16 : Nat.totient 16 = 8 := by
  rw [show 16 = 2^4 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_17 : Nat.totient 17 = 16 := by
  rw [show 17 = 17^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_23 : Nat.totient 23 = 22 := by
  rw [show 23 = 23^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_27 : Nat.totient 27 = 18 := by
  rw [show 27 = 3^3 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_32 : Nat.totient 32 = 16 := by
  rw [show 32 = 2^5 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_40 : Nat.totient 40 = 16 := by
  rw [show 40 = 2^3 * 5 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_5]
  norm_num
theorem phi_41 : Nat.totient 41 = 40 := by
  rw [show 41 = 41^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_47 : Nat.totient 47 = 46 := by
  rw [show 47 = 47^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_64 : Nat.totient 64 = 32 := by
  rw [show 64 = 2^6 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_69 : Nat.totient 69 = 44 := by
  rw [show 69 = 3^1 * 23 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_23]
  norm_num
theorem phi_81 : Nat.totient 81 = 54 := by
  rw [show 81 = 3^4 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_82 : Nat.totient 82 = 40 := by
  rw [show 82 = 2^1 * 41 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_41]
  norm_num
theorem phi_83 : Nat.totient 83 = 82 := by
  rw [show 83 = 83^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_109 : Nat.totient 109 = 108 := by
  rw [show 109 = 109^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_128 : Nat.totient 128 = 64 := by
  rw [show 128 = 2^7 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_137 : Nat.totient 137 = 136 := by
  rw [show 137 = 137^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_163 : Nat.totient 163 = 162 := by
  rw [show 163 = 163^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_166 : Nat.totient 166 = 82 := by
  rw [show 166 = 2^1 * 83 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_83]
  norm_num
theorem phi_167 : Nat.totient 167 = 166 := by
  rw [show 167 = 167^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_256 : Nat.totient 256 = 128 := by
  rw [show 256 = 2^8 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_320 : Nat.totient 320 = 128 := by
  rw [show 320 = 2^6 * 5 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_5]
  norm_num
theorem phi_329 : Nat.totient 329 = 276 := by
  rw [show 329 = 7^1 * 47 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_47]
  norm_num
theorem phi_334 : Nat.totient 334 = 166 := by
  rw [show 334 = 2^1 * 167 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_167]
  norm_num
theorem phi_411 : Nat.totient 411 = 272 := by
  rw [show 411 = 3^1 * 137 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_137]
  norm_num
theorem phi_512 : Nat.totient 512 = 256 := by
  rw [show 512 = 2^9 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_545 : Nat.totient 545 = 432 := by
  rw [show 545 = 5^1 * 109 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_109]
  norm_num
theorem phi_611 : Nat.totient 611 = 552 := by
  rw [show 611 = 13^1 * 47 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_47]
  norm_num
theorem phi_653 : Nat.totient 653 = 652 := by
  rw [show 653 = 653^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_659 : Nat.totient 659 = 658 := by
  rw [show 659 = 659^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_704 : Nat.totient 704 = 320 := by
  rw [show 704 = 2^6 * 11 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_11]
  norm_num
theorem phi_823 : Nat.totient 823 = 822 := by
  rw [show 823 = 823^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1024 : Nat.totient 1024 = 512 := by
  rw [show 1024 = 2^10 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1091 : Nat.totient 1091 = 1090 := by
  rw [show 1091 = 1091^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1097 : Nat.totient 1097 = 1096 := by
  rw [show 1097 = 1097^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1223 : Nat.totient 1223 = 1222 := by
  rw [show 1223 = 1223^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1307 : Nat.totient 1307 = 1306 := by
  rw [show 1307 = 1307^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1319 : Nat.totient 1319 = 1318 := by
  rw [show 1319 = 1319^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_2048 : Nat.totient 2048 = 1024 := by
  rw [show 2048 = 2^11 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_2208 : Nat.totient 2208 = 704 := by
  rw [show 2208 = 2^5 * 69 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_69]
  norm_num
theorem phi_2447 : Nat.totient 2447 = 2446 := by
  rw [show 2447 = 2447^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_3072 : Nat.totient 3072 = 1024 := by
  rw [show 3072 = 2^10 * 3 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_3]
  norm_num
theorem phi_3273 : Nat.totient 3273 = 2180 := by
  rw [show 3273 = 3^1 * 1091 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1091]
  norm_num
theorem phi_3957 : Nat.totient 3957 = 2636 := by
  rw [show 3957 = 3^1 * 1319 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1319]
  norm_num
theorem phi_4096 : Nat.totient 4096 = 2048 := by
  rw [show 4096 = 2^12 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_4115 : Nat.totient 4115 = 3288 := by
  rw [show 4115 = 5^1 * 823 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_823]
  norm_num
theorem phi_4888 : Nat.totient 4888 = 2208 := by
  rw [show 4888 = 2^3 * 611 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_611]
  norm_num
theorem phi_5264 : Nat.totient 5264 = 2208 := by
  rw [show 5264 = 2^4 * 329 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_329]
  norm_num
theorem phi_6535 : Nat.totient 6535 = 5224 := by
  rw [show 6535 = 5^1 * 1307 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1307]
  norm_num
theorem phi_6547 : Nat.totient 6547 = 6546 := by
  rw [show 6547 = 6547^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_8192 : Nat.totient 8192 = 4096 := by
  rw [show 8192 = 2^13 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_8231 : Nat.totient 8231 = 8230 := by
  rw [show 8231 = 8231^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_9216 : Nat.totient 9216 = 3072 := by
  rw [show 9216 = 2^10 * 9 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_9]
  norm_num
theorem phi_9784 : Nat.totient 9784 = 4888 := by
  rw [show 9784 = 2^3 * 1223 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1223]
  norm_num
theorem phi_10457 : Nat.totient 10457 = 10456 := by
  rw [show 10457 = 10457^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_10544 : Nat.totient 10544 = 5264 := by
  rw [show 10544 = 2^4 * 659 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_659]
  norm_num
theorem phi_16384 : Nat.totient 16384 = 8192 := by
  rw [show 16384 = 2^14 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_17408 : Nat.totient 17408 = 8192 := by
  rw [show 17408 = 2^10 * 17 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_17]
  norm_num
theorem phi_19576 : Nat.totient 19576 = 9784 := by
  rw [show 19576 = 2^3 * 2447 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_2447]
  norm_num
theorem phi_19577 : Nat.totient 19577 = 19576 := by
  rw [show 19577 = 19577^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_24693 : Nat.totient 24693 = 16460 := by
  rw [show 24693 = 3^1 * 8231 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_8231]
  norm_num
theorem phi_26189 : Nat.totient 26189 = 26188 := by
  rw [show 26189 = 26189^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_27648 : Nat.totient 27648 = 9216 := by
  rw [show 27648 = 2^10 * 27 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_27]
  norm_num
theorem phi_31371 : Nat.totient 31371 = 20912 := by
  rw [show 31371 = 3^1 * 10457 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_10457]
  norm_num
theorem phi_31656 : Nat.totient 31656 = 10544 := by
  rw [show 31656 = 2^3 * 3957 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_3957]
  norm_num
theorem phi_31657 : Nat.totient 31657 = 31656 := by
  rw [show 31657 = 31657^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_32768 : Nat.totient 32768 = 16384 := by
  rw [show 32768 = 2^15 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_39154 : Nat.totient 39154 = 19576 := by
  rw [show 39154 = 2^1 * 19577 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_19577]
  norm_num
theorem phi_41155 : Nat.totient 41155 = 32920 := by
  rw [show 41155 = 5^1 * 8231 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_8231]
  norm_num
theorem phi_52379 : Nat.totient 52379 = 52378 := by
  rw [show 52379 = 52379^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_52608 : Nat.totient 52608 = 17408 := by
  rw [show 52608 = 2^7 * 411 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_411]
  norm_num
theorem phi_62743 : Nat.totient 62743 = 62742 := by
  rw [show 62743 = 62743^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_63314 : Nat.totient 63314 = 31656 := by
  rw [show 63314 = 2^1 * 31657 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_31657]
  norm_num
theorem phi_65536 : Nat.totient 65536 = 32768 := by
  rw [show 65536 = 2^16 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_65537 : Nat.totient 65537 = 65536 := by
  rw [show 65537 = 65537^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_69760 : Nat.totient 69760 = 27648 := by
  rw [show 69760 = 2^7 * 545 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_545]
  norm_num
theorem phi_78567 : Nat.totient 78567 = 52376 := by
  rw [show 78567 = 3^1 * 26189 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_26189]
  norm_num
theorem phi_82944 : Nat.totient 82944 = 27648 := by
  rw [show 82944 = 2^10 * 81 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_81]
  norm_num
theorem phi_98773 : Nat.totient 98773 = 98772 := by
  rw [show 98773 = 98773^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_104561 : Nat.totient 104561 = 104560 := by
  rw [show 104561 = 104561^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_104759 : Nat.totient 104759 = 104758 := by
  rw [show 104759 = 104759^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_131072 : Nat.totient 131072 = 65536 := by
  rw [show 131072 = 2^17 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_131680 : Nat.totient 131680 = 52608 := by
  rw [show 131680 = 2^5 * 4115 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_4115]
  norm_num
theorem phi_139264 : Nat.totient 139264 = 65536 := by
  rw [show 139264 = 2^13 * 17 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_17]
  norm_num
theorem phi_140417 : Nat.totient 140417 = 140416 := by
  rw [show 140417 = 140417^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_164621 : Nat.totient 164621 = 164620 := by
  rw [show 164621 = 164621^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_166912 : Nat.totient 166912 = 82944 := by
  rw [show 166912 = 2^10 * 163 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_163]
  norm_num
theorem phi_209123 : Nat.totient 209123 = 209122 := by
  rw [show 209123 = 209123^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_209472 : Nat.totient 209472 = 69760 := by
  rw [show 209472 = 2^6 * 3273 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_3273]
  norm_num
theorem phi_209519 : Nat.totient 209519 = 209518 := by
  rw [show 209519 = 209519^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_262144 : Nat.totient 262144 = 131072 := by
  rw [show 262144 = 2^18 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_280576 : Nat.totient 280576 = 139264 := by
  rw [show 280576 = 2^11 * 137 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_137]
  norm_num
theorem phi_327685 : Nat.totient 327685 = 262144 := by
  rw [show 327685 = 5^1 * 65537 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_65537]
  norm_num
theorem phi_329240 : Nat.totient 329240 = 131680 := by
  rw [show 329240 = 2^3 * 41155 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_41155]
  norm_num
theorem phi_329243 : Nat.totient 329243 = 329242 := by
  rw [show 329243 = 329243^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_334336 : Nat.totient 334336 = 166912 := by
  rw [show 334336 = 2^9 * 653 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_653]
  norm_num
theorem phi_366653 : Nat.totient 366653 = 314268 := by
  rw [show 366653 = 7^1 * 52379 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_52379]
  norm_num
theorem phi_395088 : Nat.totient 395088 = 131680 := by
  rw [show 395088 = 2^4 * 24693 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_24693]
  norm_num
theorem phi_395093 : Nat.totient 395093 = 395092 := by
  rw [show 395093 = 395093^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_419008 : Nat.totient 419008 = 209472 := by
  rw [show 419008 = 2^6 * 6547 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_6547]
  norm_num
theorem phi_524288 : Nat.totient 524288 = 262144 := by
  rw [show 524288 = 2^19 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_561664 : Nat.totient 561664 = 280576 := by
  rw [show 561664 = 2^9 * 1097 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1097]
  norm_num
theorem phi_658484 : Nat.totient 658484 = 329240 := by
  rw [show 658484 = 2^2 * 164621 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_164621]
  norm_num
theorem phi_658487 : Nat.totient 658487 = 658486 := by
  rw [show 658487 = 658487^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_669184 : Nat.totient 669184 = 334336 := by
  rw [show 669184 = 2^9 * 1307 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1307]
  norm_num
theorem phi_702085 : Nat.totient 702085 = 561664 := by
  rw [show 702085 = 5^1 * 140417 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_140417]
  norm_num
theorem phi_733307 : Nat.totient 733307 = 733306 := by
  rw [show 733307 = 733307^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_790184 : Nat.totient 790184 = 395088 := by
  rw [show 790184 = 2^3 * 98773 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_98773]
  norm_num
theorem phi_836480 : Nat.totient 836480 = 334336 := by
  rw [show 836480 = 2^7 * 6535 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_6535]
  norm_num
theorem phi_838048 : Nat.totient 838048 = 419008 := by
  rw [show 838048 = 2^5 * 26189 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_26189]
  norm_num
theorem phi_983055 : Nat.totient 983055 = 524288 := by
  rw [show 983055 = 3^1 * 327685 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_327685]
  norm_num
theorem phi_1003889 : Nat.totient 1003889 = 1003888 := by
  rw [show 1003889 = 1003889^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1045615 : Nat.totient 1045615 = 836488 := by
  rw [show 1045615 = 5^1 * 209123 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_209123]
  norm_num
theorem phi_1048576 : Nat.totient 1048576 = 524288 := by
  rw [show 1048576 = 2^20 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_1123336 : Nat.totient 1123336 = 561664 := by
  rw [show 1123336 = 2^3 * 140417 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_140417]
  norm_num
theorem phi_1185279 : Nat.totient 1185279 = 790184 := by
  rw [show 1185279 = 3^1 * 395093 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_395093]
  norm_num
theorem phi_1257072 : Nat.totient 1257072 = 419008 := by
  rw [show 1257072 = 2^4 * 78567 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_78567]
  norm_num
theorem phi_1316972 : Nat.totient 1316972 = 658484 := by
  rw [show 1316972 = 2^2 * 329243 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_329243]
  norm_num
theorem phi_1672976 : Nat.totient 1672976 = 836480 := by
  rw [show 1672976 = 2^4 * 104561 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_104561]
  norm_num
theorem phi_1676128 : Nat.totient 1676128 = 838048 := by
  rw [show 1676128 = 2^5 * 52379 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_52379]
  norm_num
theorem phi_1975461 : Nat.totient 1975461 = 1316972 := by
  rw [show 1975461 = 3^1 * 658487 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_658487]
  norm_num
theorem phi_2007744 : Nat.totient 2007744 = 669184 := by
  rw [show 2007744 = 2^6 * 31371 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_31371]
  norm_num
theorem phi_2370558 : Nat.totient 2370558 = 790184 := by
  rw [show 2370558 = 2^1 * 1185279 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1185279]
  norm_num
theorem phi_2370559 : Nat.totient 2370559 = 2370558 := by
  rw [show 2370559 = 2370559^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_2633948 : Nat.totient 2633948 = 1316972 := by
  rw [show 2633948 = 2^2 * 658487 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_658487]
  norm_num
theorem phi_2933224 : Nat.totient 2933224 = 1257072 := by
  rw [show 2933224 = 2^3 * 366653 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_366653]
  norm_num
theorem phi_3352288 : Nat.totient 3352288 = 1676128 := by
  rw [show 3352288 = 2^5 * 104759 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_104759]
  norm_num
theorem phi_3352289 : Nat.totient 3352289 = 3352288 := by
  rw [show 3352289 = 3352289^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_3561823 : Nat.totient 3561823 = 3352288 := by
  rw [show 3561823 = 17^1 * 209519 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_209519]
  norm_num
theorem phi_4015552 : Nat.totient 4015552 = 2007744 := by
  rw [show 4015552 = 2^6 * 62743 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_62743]
  norm_num
theorem phi_4182460 : Nat.totient 4182460 = 1672976 := by
  rw [show 4182460 = 2^2 * 1045615 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1045615]
  norm_num
theorem phi_4182461 : Nat.totient 4182461 = 4182460 := by
  rw [show 4182461 = 4182461^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_4741118 : Nat.totient 4741118 = 2370558 := by
  rw [show 4741118 = 2^1 * 2370559 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_2370559]
  norm_num
theorem phi_5019445 : Nat.totient 5019445 = 4015552 := by
  rw [show 5019445 = 5^1 * 1003889 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1003889]
  norm_num
theorem phi_5866456 : Nat.totient 5866456 = 2933224 := by
  rw [show 5866456 = 2^3 * 733307 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_733307]
  norm_num
theorem phi_5866457 : Nat.totient 5866457 = 5866456 := by
  rw [show 5866457 = 5866457^1 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num
theorem phi_8031112 : Nat.totient 8031112 = 4015552 := by
  rw [show 8031112 = 2^3 * 1003889 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_1003889]
  norm_num
theorem phi_8364922 : Nat.totient 8364922 = 4182460 := by
  rw [show 8364922 = 2^1 * 4182461 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_4182461]
  norm_num
theorem phi_11732914 : Nat.totient 11732914 = 5866456 := by
  rw [show 11732914 = 2^1 * 5866457 by norm_num, Nat.totient_mul (by decide), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_5866457]
  norm_num
end R162
