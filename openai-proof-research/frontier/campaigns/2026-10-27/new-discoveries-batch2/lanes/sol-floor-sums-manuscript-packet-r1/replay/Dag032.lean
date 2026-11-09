import Dag031
import generated.th_lemma_0
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8355 (_v : Vars) (_q : Query _v)  : (e4893 _v) := by
  simp only [e5, e6, e12, e2987, e4871, e4874, e4888, e4893] at *
  omega
theorem n8357 (_v : Vars) (_q : Query _v)  : (e8356 _v) := by
  have p8354 := n8354 _v _q 
  have p8355 := n8355 _v _q 
  change ((e4887 _v) ↔ (e4872 _v)) at p8354
  change ((e4888 _v) ↔ (e4874 _v)) at p8355
  simp only [e8356, e4889, e4894, p8354, p8355]
theorem n8360 (_v : Vars) (_q : Query _v)  : (e8359 _v) := by
  simp only [e5, e6, e12, e2987, e4871, e4872, e4873, e4874, e4875, e4894, e8350, e8358, e8359] at *
  omega
theorem n8370 (_v : Vars) (_q : Query _v)  : (e8369 _v) := by
  simp only [e12, e4902, e4903, e4904, e4907, e4908, e4909, e4910, e8369] at *
  omega
theorem n8371 (_v : Vars) (_q : Query _v)  : (e4917 _v) := by
  simp only [e5, e6, e12, e4895, e4896, e4897, e4912, e4917] at *
  omega
theorem n8372 (_v : Vars) (_q : Query _v)  : (e4918 _v) := by
  simp only [e5, e6, e12, e4895, e4896, e4899, e4913, e4918] at *
  omega
theorem n8374 (_v : Vars) (_q : Query _v)  : (e8373 _v) := by
  have p8371 := n8371 _v _q 
  have p8372 := n8372 _v _q 
  change ((e4912 _v) ↔ (e4897 _v)) at p8371
  change ((e4913 _v) ↔ (e4899 _v)) at p8372
  simp only [e8373, e4914, e4919, p8371, p8372]
theorem n8377 (_v : Vars) (_q : Query _v)  : (e8376 _v) := by
  simp only [e5, e6, e12, e4895, e4896, e4897, e4898, e4899, e4900, e4919, e8367, e8375, e8376] at *
  omega
theorem n8386 (_v : Vars) (_q : Query _v)  : (e4932 _v) := by
  simp only [e5, e6, e12, e4920, e4921, e4922, e4927, e4932] at *
  omega
theorem n8387 (_v : Vars) (_q : Query _v)  : (e4933 _v) := by
  simp only [e5, e6, e12, e4920, e4921, e4924, e4928, e4933] at *
  omega
theorem n8389 (_v : Vars) (_q : Query _v)  : (e8388 _v) := by
  have p8386 := n8386 _v _q 
  have p8387 := n8387 _v _q 
  change ((e4927 _v) ↔ (e4922 _v)) at p8386
  change ((e4928 _v) ↔ (e4924 _v)) at p8387
  simp only [e8388, e4929, e4934, p8386, p8387]
theorem n8392 (_v : Vars) (_q : Query _v)  : (e8391 _v) := by
  simp only [e5, e6, e12, e4920, e4921, e4922, e4923, e4924, e4925, e4934, e8384, e8390, e8391] at *
  omega
theorem n8397 (_v : Vars) (_q : Query _v)  : (e8396 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e781, e782, e2788, e4935, e4937, e8395, e8396] at *
  omega
theorem n8400 (_v : Vars) (_q : Query _v)  : (e8399 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e781, e782, e2788, e4936, e4937, e8398, e8399] at *
  omega
theorem n8404 (_v : Vars) (_q : Query _v)  : (e8403 _v) := by
  have p8397 := n8397 _v _q 
  have p8400 := n8400 _v _q 
  change ((e4935 _v) ↔ (e8395 _v)) at p8397
  change ((e4936 _v) ↔ (e8398 _v)) at p8400
  simp only [e8403, e8401, e8402, p8397, p8400]
theorem n8410 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2722 _v) := by
  exact h2722
theorem n8411 (_v : Vars) (_q : Query _v) (h6694 : (e6694 _v)) : (e6694 _v) := by
  exact h6694
theorem n8412 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) (h6694 : (e6694 _v)) : (e7489 _v) := by
  have p3130 := n3130 _v _q 
  have p8410 := n8410 _v _q h2722
  have p8411 := n8411 _v _q h6694
  exact FloorCertificate.node_8412 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p3130 p8410 p8411
theorem n8414 (_v : Vars) (_q : Query _v)  : (e8413 _v) := by
  by_contra hc
  change ¬ ((e251 _v) ∨ (¬ (e2722 _v))) at hc
  have h2722 : (e2722 _v) := by
    tauto
  have h6694 : (e6694 _v) := by
    change (¬ (e251 _v))
    tauto
  have p8412 := n8412 _v _q h2722 h6694
  exact p8412
theorem n8415 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2771 _v) := by
  exact h2771
theorem n8416 (_v : Vars) (_q : Query _v) (h6742 : (e6742 _v)) : (e6742 _v) := by
  exact h6742
theorem n8417 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) (h6742 : (e6742 _v)) : (e7489 _v) := by
  have p8415 := n8415 _v _q h2771
  have p4016 := n4016 _v _q 
  have p8416 := n8416 _v _q h6742
  exact FloorCertificate.node_8417 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8415 p4016 p8416
theorem n8419 (_v : Vars) (_q : Query _v)  : (e8418 _v) := by
  by_contra hc
  change ¬ ((e2722 _v) ∨ (¬ (e2771 _v))) at hc
  have h2771 : (e2771 _v) := by
    tauto
  have h6742 : (e6742 _v) := by
    change (¬ (e2722 _v))
    tauto
  have p8417 := n8417 _v _q h2771 h6742
  exact p8417
theorem n8420 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e6750 _v) := by
  exact h6750
theorem n8421 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2781 _v) := by
  exact h2781
theorem n8422 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p8420 := n8420 _v _q h6750
  have p8421 := n8421 _v _q h2781
  exact FloorCertificate.node_8422 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p8420 p8421
theorem n8424 (_v : Vars) (_q : Query _v)  : (e8423 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (¬ (e2781 _v))) at hc
  have h2781 : (e2781 _v) := by
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have p8422 := n8422 _v _q h2781 h6750
  exact p8422
theorem n8425 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6758 _v) := by
  exact h6758
theorem n8426 (_v : Vars) (_q : Query _v) (h2793 : (e2793 _v)) : (e2793 _v) := by
  exact h2793
theorem n8427 (_v : Vars) (_q : Query _v) (h2793 : (e2793 _v)) (h6758 : (e6758 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p8425 := n8425 _v _q h6758
  have p8426 := n8426 _v _q h2793
  exact FloorCertificate.node_8427 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p8425 p8426
theorem n8429 (_v : Vars) (_q : Query _v)  : (e8428 _v) := by
  by_contra hc
  change ¬ ((¬ (e2793 _v)) ∨ (e2746 _v)) at hc
  have h2793 : (e2793 _v) := by
    tauto
  have h6758 : (e6758 _v) := by
    change (¬ (e2746 _v))
    tauto
  have p8427 := n8427 _v _q h2793 h6758
  exact p8427
theorem n8430 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6454 _v) := by
  exact h6454
theorem n8431 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p8430 := n8430 _v _q h6454
  have p4016 := n4016 _v _q 
  have p4946 := n4946 _v _q 
  have p8415 := n8415 _v _q h2771
  have p4951 := n4951 _v _q 
  exact FloorCertificate.node_8431 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8430 p4016 p4946 p8415 p4951
theorem n8433 (_v : Vars) (_q : Query _v)  : (e8432 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e2771 _v))) at hc
  have h2771 : (e2771 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p8431 := n8431 _v _q h2771 h6454
  exact p8431
theorem n8434 (_v : Vars) (_q : Query _v) (h6630 : (e6630 _v)) : (e6630 _v) := by
  exact h6630
theorem n8435 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p3130 := n3130 _v _q 
  have p4951 := n4951 _v _q 
  have p8434 := n8434 _v _q h6630
  have p8415 := n8415 _v _q h2771
  exact FloorCertificate.node_8435 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p3130 p4951 p8434 p8415
theorem n8437 (_v : Vars) (_q : Query _v)  : (e8436 _v) := by
  by_contra hc
  change ¬ ((e2468 _v) ∨ (¬ (e2771 _v))) at hc
  have h2771 : (e2771 _v) := by
    tauto
  have h6630 : (e6630 _v) := by
    change (¬ (e2468 _v))
    tauto
  have p8435 := n8435 _v _q h2771 h6630
  exact p8435
theorem n8438 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e2468 _v) := by
  exact h2468
theorem n8439 (_v : Vars) (_q : Query _v) (h6600 : (e6600 _v)) : (e6600 _v) := by
  exact h6600
theorem n8440 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p8438 := n8438 _v _q h2468
  have p4016 := n4016 _v _q 
  have p8439 := n8439 _v _q h6600
  exact FloorCertificate.node_8440 (e2 _v) (e7 _v) (e17 _v) (e45 _v) p8438 p4016 p8439
theorem n8442 (_v : Vars) (_q : Query _v)  : (e8441 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e2468 _v))) at hc
  have h2468 : (e2468 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have p8440 := n8440 _v _q h2468 h6600
  exact p8440
theorem n8443 (_v : Vars) (_q : Query _v)  : (e4482 _v) := by
  simp only [e4458, e4459, e4463, e4464, e4465, e4482] at *
  tauto
theorem n8444 (_v : Vars) (_q : Query _v) (h4464 : (e4464 _v)) : (e4464 _v) := by
  exact h4464
theorem n8445 (_v : Vars) (_q : Query _v) (h4464 : (e4464 _v)) : (e4465 _v) := by
  have p8443 := n8443 _v _q 
  have p8444 := n8444 _v _q h4464
  simp only [e4458, e4459, e4463, e4464, e4465, e4482] at *
  tauto
theorem n8447 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e6571 _v) := by
  exact h6571
end
end Assembly
