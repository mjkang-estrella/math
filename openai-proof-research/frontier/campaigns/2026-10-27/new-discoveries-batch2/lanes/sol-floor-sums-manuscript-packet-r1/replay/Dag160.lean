import Dag159
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16886 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) (h5195 : (e5195 _v)) : (e2781 _v) := by
  have p8549 := n8549 _v _q h5195
  have p16885 := n16885 _v _q h3158
  have p16578 := n16578 _v _q 
  have p16858 := n16858 _v _q 
  exact FloorCertificate.node_16886 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2863 _v) (e2935 _v) p8549 p16885 p16578 p16858
theorem n16887 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p8602 := n8602 _v _q h8038
  have p11350 := n11350 _v _q h7807
  simp only [e2303, e2475, e4419, e4420, e7807, e8038, e16831] at *
  tauto
theorem n16888 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p16887 := n16887 _v _q h7807 h8038
  simp only [e4417, e4418, e4419, e4420, e7921, e7922] at *
  tauto
theorem n16889 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p16688 := n16688 _v _q h2475
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n16890 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e7496 _v) := by
  have p16732 := n16732 _v _q 
  have p11366 := n11366 _v _q h5108
  have p16729 := n16729 _v _q h51
  simp only [e48, e51, e57, e5108, e7495, e7496, e16731] at *
  tauto
theorem n16891 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e7497 _v) := by
  have p16733 := n16733 _v _q 
  have p16890 := n16890 _v _q h51 h5108
  simp only [e7493, e7494, e7495, e7496, e7497, e8599] at *
  tauto
theorem n16892 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16745 := n16745 _v _q h5108
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16893 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16747 := n16747 _v _q h6676
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16894 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16751 := n16751 _v _q h2132
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16895 (_v : Vars) (_q : Query _v) (h5247 : (e5247 _v)) : (e7489 _v) := by
  have p8683 := n8683 _v _q h5247
  have p16144 := n16144 _v _q h5247
  have p16754 := n16754 _v _q h5247
  exact FloorCertificate.node_16895 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e211 _v) p8683 p16144 p16754
theorem n16897 (_v : Vars) (_q : Query _v)  : (e16896 _v) := by
  have p14220 := n14220 _v _q 
  have p8951 := n8951 _v _q 
  exact (Eq.trans p14220 p8951)
theorem n16899 (_v : Vars) (_q : Query _v)  : (e16898 _v) := by
  have p14226 := n14226 _v _q 
  have p9000 := n9000 _v _q 
  exact (Eq.trans p14226 p9000)
theorem n16901 (_v : Vars) (_q : Query _v)  : (e16900 _v) := by
  have p14230 := n14230 _v _q 
  have p9015 := n9015 _v _q 
  exact (Eq.trans p14230 p9015)
theorem n16903 (_v : Vars) (_q : Query _v)  : (e16902 _v) := by
  have p14254 := n14254 _v _q 
  have p9075 := n9075 _v _q 
  exact (Eq.trans p14254 p9075)
theorem n16905 (_v : Vars) (_q : Query _v)  : (e16904 _v) := by
  have p14258 := n14258 _v _q 
  have p9090 := n9090 _v _q 
  exact (Eq.trans p14258 p9090)
theorem n16907 (_v : Vars) (_q : Query _v)  : (e16906 _v) := by
  have p14280 := n14280 _v _q 
  have p9116 := n9116 _v _q 
  exact (Eq.trans p14280 p9116)
theorem n16909 (_v : Vars) (_q : Query _v)  : (e16908 _v) := by
  have p13064 := n13064 _v _q 
  have p14214 := n14214 _v _q 
  have p14216 := n14216 _v _q 
  have p16897 := n16897 _v _q 
  have p14222 := n14222 _v _q 
  have p16899 := n16899 _v _q 
  have p16901 := n16901 _v _q 
  have p16156 := n16156 _v _q 
  have p14250 := n14250 _v _q 
  have p16903 := n16903 _v _q 
  have p16905 := n16905 _v _q 
  have p16160 := n16160 _v _q 
  have p16907 := n16907 _v _q 
  have p16164 := n16164 _v _q 
  have p16168 := n16168 _v _q 
  have p16760 := n16760 _v _q 
  change ((e11643 _v) = (e8865 _v)) at p13064
  change ((e11644 _v) = (e8902 _v)) at p14214
  change ((e11645 _v) = (e8936 _v)) at p14216
  change ((e11646 _v) = (e8948 _v)) at p16897
  change ((e11647 _v) = (e8985 _v)) at p14222
  change ((e11648 _v) = (e8997 _v)) at p16899
  change ((e11649 _v) = (e9012 _v)) at p16901
  change ((e11650 _v) = (e5774 _v)) at p16156
  change ((e11651 _v) = (e9060 _v)) at p14250
  change ((e11652 _v) = (e9072 _v)) at p16903
  change ((e11653 _v) = (e9087 _v)) at p16905
  change ((e11654 _v) = (e5919 _v)) at p16160
  change ((e11655 _v) = (e9113 _v)) at p16907
  change ((e11656 _v) = (e5993 _v)) at p16164
  change ((e11657 _v) = (e6031 _v)) at p16168
  change ((e11659 _v) = (e9159 _v)) at p16760
  simp only [e16908, e11660, e11808, p13064, p14214, p14216, p16897, p14222, p16899, p16901, p16156, p14250, p16903, p16905, p16160, p16907, p16164, p16168, p16760]
theorem n16910 (_v : Vars) (_q : Query _v) (h4031 : (e4031 _v)) : (e7489 _v) := by
  have p16762 := n16762 _v _q h4031
  have p16197 := n16197 _v _q h4031
  have p16195 := n16195 _v _q h4031
  exact FloorCertificate.node_16910 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e61 _v) p16762 p16197 p16195
theorem n16911 (_v : Vars) (_q : Query _v)  : (e4026 _v) := by
  by_contra hc
  change ¬ (e4026 _v) at hc
  have h4031 : (e4031 _v) := by
    change (¬ (e4026 _v))
    tauto
  have p16910 := n16910 _v _q h4031
  exact p16910
theorem n16912 (_v : Vars) (_q : Query _v) (h4133 : (e4133 _v)) : (e7489 _v) := by
  have p16765 := n16765 _v _q h4133
  have p16203 := n16203 _v _q h4133
  have p16205 := n16205 _v _q h4133
  exact FloorCertificate.node_16912 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2907 _v) p16765 p16203 p16205
theorem n16913 (_v : Vars) (_q : Query _v)  : (e4128 _v) := by
  by_contra hc
  change ¬ (e4128 _v) at hc
  have h4133 : (e4133 _v) := by
    change (¬ (e4128 _v))
    tauto
  have p16912 := n16912 _v _q h4133
  exact p16912
theorem n16914 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e2132 _v) := by
  have p14942 := n14942 _v _q 
  have p16773 := n16773 _v _q h4481
  simp only [e2132, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n16915 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e4484 _v) := by
  have p8139 := n8139 _v _q 
  have p16914 := n16914 _v _q h4481
  exact FloorCertificate.node_16915 (e2 _v) (e7 _v) (e110 _v) p8139 p16914
theorem n16916 (_v : Vars) (_q : Query _v) (h7655 : (e7655 _v)) : (e7489 _v) := by
  have p16790 := n16790 _v _q h7655
  have p16327 := n16327 _v _q h7655
  have p11407 := n11407 _v _q h7655
  exact FloorCertificate.node_16916 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2877 _v) p16790 p16327 p11407
theorem n16917 (_v : Vars) (_q : Query _v) (h8345 : (e8345 _v)) : (e7489 _v) := by
  have p11422 := n11422 _v _q h8345
  have p16339 := n16339 _v _q h8345
  have p16798 := n16798 _v _q h8345
  exact FloorCertificate.node_16917 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2898 _v) p11422 p16339 p16798
theorem n16918 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p15192 := n15192 _v _q h8038
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n16919 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p16918 := n16918 _v _q h8038
  simp only [e4459, e7749, e7752, e16783] at *
  tauto
theorem n16920 (_v : Vars) (_q : Query _v) (h7698 : (e7698 _v)) : (e7489 _v) := by
  have p16825 := n16825 _v _q h7698
  have p16433 := n16433 _v _q h7698
  have p11451 := n11451 _v _q h7698
  exact FloorCertificate.node_16920 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2879 _v) p16825 p16433 p11451
theorem n16921 (_v : Vars) (_q : Query _v) (h4649 : (e4649 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15377 := n15377 _v _q h4649
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n16922 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h4562 : (e4562 _v)) (h4649 : (e4649 _v)) (h8038 : (e8038 _v)) : (e4573 _v) := by
  have p16394 := n16394 _v _q 
  have p4973 := n4973 _v _q h4562
  have p15526 := n15526 _v _q h8038
  have p16921 := n16921 _v _q h4649
  have p15374 := n15374 _v _q h4649
  have p16833 := n16833 _v _q h4419 h8038
  exact FloorCertificate.node_16922 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2834 _v) (e2879 _v) (e2918 _v) (e2951 _v) p16394 p4973 p15526 p16921 p15374 p16833
theorem n16923 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h4562 : (e4562 _v)) (h4649 : (e4649 _v)) (h8038 : (e8038 _v)) : (e4574 _v) := by
  have p15882 := n15882 _v _q 
  have p16922 := n16922 _v _q h4419 h4562 h4649 h8038
  simp only [e4567, e4568, e4572, e4573, e4574, e5015] at *
  tauto
theorem n16924 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h8038 : (e8038 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p16833 := n16833 _v _q h4419 h8038
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16925 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16924 := n16924 _v _q h4419 h8038
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16926 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h7807 : (e7807 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p16834 := n16834 _v _q h4419 h7807
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n16927 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h7807 : (e7807 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16926 := n16926 _v _q h4419 h7807
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16928 (_v : Vars) (_q : Query _v)  : (e5023 _v) := by
  simp only [e4439, e4440, e4444, e4445, e4446, e5023] at *
  tauto
theorem n16929 (_v : Vars) (_q : Query _v)  : (e4627 _v) := by
  have p8116 := n8116 _v _q 
  have p14628 := n14628 _v _q 
  simp only [e4627, e4628, e8112, e8113, e8114, e8115, e8131] at *
  tauto
theorem n16930 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) (h8338 : (e8338 _v)) : (e4445 _v) := by
  have p8457 := n8457 _v _q h2475
  have p4987 := n4987 _v _q h4434
  have p16929 := n16929 _v _q 
  have p16835 := n16835 _v _q h8338
  have p15577 := n15577 _v _q h4302
  have p16517 := n16517 _v _q h4302
  exact FloorCertificate.node_16930 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2849 _v) (e2898 _v) (e2926 _v) (e2970 _v) p8457 p4987 p16929 p16835 p15577 p16517
theorem n16931 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) (h8338 : (e8338 _v)) : (e7489 _v) := by
  have p16928 := n16928 _v _q 
  have p16837 := n16837 _v _q h2475 h4302 h8338
  have p16930 := n16930 _v _q h2475 h4302 h4434 h8338
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e5023] at *
  tauto
theorem n16932 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h7807 : (e7807 _v)) : (e4445 _v) := by
  have p16834 := n16834 _v _q h4419 h7807
  have p4987 := n4987 _v _q h4434
  have p16929 := n16929 _v _q 
  have p15582 := n15582 _v _q h7807
  have p16517 := n16517 _v _q h4302
  have p15577 := n15577 _v _q h4302
  exact FloorCertificate.node_16932 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2849 _v) (e2898 _v) (e2926 _v) (e2970 _v) p16834 p4987 p16929 p15582 p16517 p15577
theorem n16933 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h7807 : (e7807 _v)) : (e4446 _v) := by
  have p16928 := n16928 _v _q 
  have p16932 := n16932 _v _q h4302 h4419 h4434 h7807
  simp only [e4439, e4440, e4444, e4445, e4446, e5023] at *
  tauto
theorem n16934 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p16849 := n16849 _v _q h8310
  simp only [e4417, e4418, e4419, e4420, e7921, e7922] at *
  tauto
theorem n16935 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p16934 := n16934 _v _q h8310
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n16936 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p16935 := n16935 _v _q h8310
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n16937 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p16860 := n16860 _v _q h2468
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
end
end Assembly
