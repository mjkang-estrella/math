import Dag115
import generated.th_lemma_6
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14877 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p14876 := n14876 _v _q h6792
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n14878 (_v : Vars) (_q : Query _v)  : (e8137 _v) := by
  simp only [e3069, e3071, e3074, e3075, e6829, e8137] at *
  tauto
theorem n14879 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p13994 := n13994 _v _q h6792
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n14880 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p14879 := n14879 _v _q h6792
  simp only [e3069, e3071, e3074, e3075, e6829, e6830, e8137] at *
  tauto
theorem n14881 (_v : Vars) (_q : Query _v)  : (e8148 _v) := by
  simp only [e3963, e3965, e3968, e3969, e7431, e8148] at *
  tauto
theorem n14882 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7432 _v) := by
  have p14630 := n14630 _v _q 
  have p10895 := n10895 _v _q h6792
  simp only [e2805, e3963, e3965, e3968, e3969, e6792, e7431, e7432, e7435] at *
  tauto
theorem n14883 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3965 _v) := by
  have p14881 := n14881 _v _q 
  have p14882 := n14882 _v _q h6792
  simp only [e3963, e3965, e3968, e3969, e7431, e7432, e8148] at *
  tauto
theorem n14884 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6583 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14884 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p8663 p11376 p10895 p10893 p10896
theorem n14885 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p14884 := n14884 _v _q h6792
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n14886 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6525 _v) := by
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14886 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p11375 p10893 p8663 p10895 p10896
theorem n14887 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p14886 := n14886 _v _q h6792
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n14888 (_v : Vars) (_q : Query _v)  : (e11242 _v) := by
  have p14640 := n14640 _v _q 
  simp only [e2261, e4706, e4708, e4711, e4712, e8183, e8184, e8185, e8186, e8187, e8193, e8194, e8197, e8199, e8204, e8205, e11242, e11244, e11245, e11246] at *
  tauto
theorem n14889 (_v : Vars) (_q : Query _v)  : (e8197 _v) := by
  have p10896 := n10896 _v _q 
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_14889 (e2 _v) (e7 _v) (e9 _v) p10896 p11376
theorem n14890 (_v : Vars) (_q : Query _v)  : (e8204 _v) := by
  have p14888 := n14888 _v _q 
  have p14889 := n14889 _v _q 
  simp only [e2261, e8183, e8184, e8185, e8186, e8187, e8197, e8204, e11242] at *
  tauto
theorem n14891 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6531 _v) := by
  have p11375 := n11375 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14891 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p10895 p10893
theorem n14892 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8214 _v) := by
  have p14642 := n14642 _v _q 
  have p14891 := n14891 _v _q h6792
  simp only [e2254, e4718, e4719, e4720, e4721, e6531, e8206, e8214, e8217] at *
  tauto
theorem n14893 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6549 _v) := by
  have p11375 := n11375 _v _q 
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14893 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p11376 p8663 p10895 p10893 p10896
theorem n14894 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p14893 := n14893 _v _q h6792
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n14895 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6591 _v) := by
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14895 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p10893
theorem n14896 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8232 _v) := by
  have p14645 := n14645 _v _q 
  have p14895 := n14895 _v _q h6792
  simp only [e2377, e4742, e4743, e4744, e4745, e6591, e8224, e8232, e8235] at *
  tauto
theorem n14897 (_v : Vars) (_q : Query _v)  : (e8246 _v) := by
  simp only [e8241, e8242, e8243, e8244, e8245, e8246] at *
  tauto
theorem n14898 (_v : Vars) (_q : Query _v)  : (e11267 _v) := by
  have p14653 := n14653 _v _q 
  simp only [e2384, e4774, e4776, e4779, e4780, e6587, e8241, e8242, e8243, e8244, e8245, e8251, e8252, e8255, e8265, e8266, e11267, e11269, e11270, e11271] at *
  tauto
theorem n14899 (_v : Vars) (_q : Query _v)  : (e6587 _v) := by
  have p10896 := n10896 _v _q 
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_14899 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p10896 p11376 p11375
theorem n14900 (_v : Vars) (_q : Query _v)  : (e8265 _v) := by
  have p14898 := n14898 _v _q 
  have p14899 := n14899 _v _q 
  simp only [e2384, e6587, e8241, e8242, e8243, e8244, e8245, e8265, e11267] at *
  tauto
theorem n14901 (_v : Vars) (_q : Query _v)  : (e8241 _v) := by
  have p14897 := n14897 _v _q 
  have p14900 := n14900 _v _q 
  simp only [e8241, e8242, e8243, e8244, e8245, e8246, e8265] at *
  tauto
theorem n14902 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6630 _v) := by
  have p11375 := n11375 _v _q 
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p10895 := n10895 _v _q h6792
  exact FloorCertificate.node_14902 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p10893 p11376 p8663 p10896 p10895
theorem n14903 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p14902 := n14902 _v _q h6792
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n14904 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6650 _v) := by
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  have p10895 := n10895 _v _q h6792
  exact FloorCertificate.node_14904 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11376 p8663 p11375 p10896 p10895
theorem n14905 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p14904 := n14904 _v _q h6792
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n14906 (_v : Vars) (_q : Query _v)  : (e8312 _v) := by
  have p14663 := n14663 _v _q 
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312, e8315, e8317, e8319, e8320, e8321, e8322, e8323, e11298, e11300, e11301, e11302] at *
  tauto
theorem n14907 (_v : Vars) (_q : Query _v)  : (e8333 _v) := by
  have p14671 := n14671 _v _q 
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333, e8335, e8338, e8345, e8346, e8347, e8348, e8349, e11307, e11309, e11310, e11311] at *
  tauto
theorem n14908 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6742 _v) := by
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14908 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p11376 p11375 p10895 p10896 p10893
theorem n14909 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8358 _v) := by
  have p14673 := n14673 _v _q 
  have p14908 := n14908 _v _q h6792
  simp only [e2722, e4872, e4873, e4874, e4875, e6742, e8350, e8358, e8361] at *
  tauto
theorem n14910 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6784 _v) := by
  have p10895 := n10895 _v _q h6792
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14910 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p11375 p8663 p11376 p10896 p10893
theorem n14911 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8375 _v) := by
  have p14675 := n14675 _v _q 
  have p14910 := n14910 _v _q h6792
  simp only [e2793, e4897, e4898, e4899, e4900, e6784, e8367, e8375, e8378] at *
  tauto
theorem n14912 (_v : Vars) (_q : Query _v)  : (e8393 _v) := by
  have p14683 := n14683 _v _q 
  simp only [e2799, e4922, e4923, e4924, e4925, e6780, e8384, e8390, e8393, e8395, e8398, e8405, e8406, e8407, e8408, e8409, e11332, e11334, e11335, e11336] at *
  tauto
theorem n14913 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2722 _v) := by
  have p8419 := n8419 _v _q 
  have p8415 := n8415 _v _q h2771
  simp only [e2722, e2771, e6768, e8418] at *
  tauto
theorem n14914 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e251 _v) := by
  have p8414 := n8414 _v _q 
  have p14913 := n14913 _v _q h2771
  simp only [e251, e2722, e6742, e8413] at *
  tauto
theorem n14915 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e4380 _v) := by
  have p14685 := n14685 _v _q 
  have p14914 := n14914 _v _q h2771
  simp only [e251, e4372, e4373, e4377, e4378, e4379, e4380, e6694, e7901] at *
  tauto
theorem n14916 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p12802 := n12802 _v _q h2771
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n14917 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2585 _v) := by
  have p10946 := n10946 _v _q 
  have p14916 := n14916 _v _q h2771
  simp only [e2585, e2733, e6750, e10945] at *
  tauto
theorem n14918 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2364 _v) := by
  have p11343 := n11343 _v _q 
  have p14917 := n14917 _v _q h2771
  simp only [e2364, e2585, e6676, e11342] at *
  tauto
theorem n14919 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p14918 := n14918 _v _q h2771
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n14920 (_v : Vars) (_q : Query _v)  : (e4940 _v) := by
  simp only [e4747, e4748, e4752, e4753, e4754, e4940] at *
  tauto
theorem n14921 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2746 _v) := by
  have p8429 := n8429 _v _q 
  have p12803 := n12803 _v _q h2771
  simp only [e2746, e2793, e6784, e8428] at *
  tauto
end
end Assembly
