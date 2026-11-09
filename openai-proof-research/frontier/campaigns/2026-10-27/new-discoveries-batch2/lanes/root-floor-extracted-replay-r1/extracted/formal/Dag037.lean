import Dag036
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8906 (_v : Vars) (_q : Query _v)  : (e905 _v) := by
  simp only [e5, e6, e12, e36, e898, e902, e903, e904, e905] at *
  omega
theorem n8907 (_v : Vars) (_q : Query _v)  : (e5562 _v) := by
  have p8905 := n8905 _v _q 
  have p8906 := n8906 _v _q 
  exact (Iff.trans p8905 p8906)
theorem n8908 (_v : Vars) (_q : Query _v)  : (e5570 _v) := by
  have p5569 := n5569 _v _q 
  change ((e563 _v) = (e914 _v)) at p5569
  simp only [e5570, e564, e1623, p5569]
theorem n8909 (_v : Vars) (_q : Query _v)  : (e5571 _v) := by
  have p5569 := n5569 _v _q 
  change ((e563 _v) = (e914 _v)) at p5569
  simp only [e5571, e565, e919, p5569]
theorem n8910 (_v : Vars) (_q : Query _v)  : (e922 _v) := by
  simp only [e12, e43, e760, e761, e914, e919, e920, e921, e922] at *
  omega
theorem n8911 (_v : Vars) (_q : Query _v)  : (e5572 _v) := by
  have p8909 := n8909 _v _q 
  have p8910 := n8910 _v _q 
  exact (Iff.trans p8909 p8910)
theorem n8913 (_v : Vars) (_q : Query _v)  : (e8912 _v) := by
  have p8911 := n8911 _v _q 
  have p5569 := n5569 _v _q 
  change ((e565 _v) ↔ (e921 _v)) at p8911
  change ((e563 _v) = (e914 _v)) at p5569
  simp only [e8912, e5435, e923, p8911, p5569]
theorem n8915 (_v : Vars) (_q : Query _v)  : (e8914 _v) := by
  have p8908 := n8908 _v _q 
  have p8913 := n8913 _v _q 
  change ((e564 _v) ↔ (e1623 _v)) at p8908
  change ((e5435 _v) = (e923 _v)) at p8913
  simp only [e8914, e8769, e5573, p8908, p8913]
theorem n8916 (_v : Vars) (_q : Query _v)  : (e5580 _v) := by
  have p5579 := n5579 _v _q 
  change ((e566 _v) = (e931 _v)) at p5579
  simp only [e5580, e567, e1630, p5579]
theorem n8917 (_v : Vars) (_q : Query _v)  : (e5581 _v) := by
  have p5579 := n5579 _v _q 
  change ((e566 _v) = (e931 _v)) at p5579
  simp only [e5581, e568, e936, p5579]
theorem n8918 (_v : Vars) (_q : Query _v)  : (e939 _v) := by
  simp only [e12, e266, e781, e782, e931, e936, e937, e938, e939] at *
  omega
theorem n8919 (_v : Vars) (_q : Query _v)  : (e5582 _v) := by
  have p8917 := n8917 _v _q 
  have p8918 := n8918 _v _q 
  exact (Iff.trans p8917 p8918)
theorem n8921 (_v : Vars) (_q : Query _v)  : (e8920 _v) := by
  have p8919 := n8919 _v _q 
  have p5579 := n5579 _v _q 
  change ((e568 _v) ↔ (e938 _v)) at p8919
  change ((e566 _v) = (e931 _v)) at p5579
  simp only [e8920, e5436, e940, p8919, p5579]
theorem n8923 (_v : Vars) (_q : Query _v)  : (e8922 _v) := by
  have p8916 := n8916 _v _q 
  have p8921 := n8921 _v _q 
  change ((e567 _v) ↔ (e1630 _v)) at p8916
  change ((e5436 _v) = (e940 _v)) at p8921
  simp only [e8922, e8770, e5583, p8916, p8921]
theorem n8924 (_v : Vars) (_q : Query _v)  : (e5590 _v) := by
  have p5589 := n5589 _v _q 
  change ((e569 _v) = (e948 _v)) at p5589
  simp only [e5590, e570, e1637, p5589]
theorem n8925 (_v : Vars) (_q : Query _v)  : (e5591 _v) := by
  have p5589 := n5589 _v _q 
  change ((e569 _v) = (e948 _v)) at p5589
  simp only [e5591, e571, e953, p5589]
theorem n8926 (_v : Vars) (_q : Query _v)  : (e956 _v) := by
  simp only [e12, e108, e802, e803, e948, e953, e954, e955, e956] at *
  omega
theorem n8927 (_v : Vars) (_q : Query _v)  : (e5592 _v) := by
  have p8925 := n8925 _v _q 
  have p8926 := n8926 _v _q 
  exact (Iff.trans p8925 p8926)
theorem n8929 (_v : Vars) (_q : Query _v)  : (e8928 _v) := by
  have p8927 := n8927 _v _q 
  have p5589 := n5589 _v _q 
  change ((e571 _v) ↔ (e955 _v)) at p8927
  change ((e569 _v) = (e948 _v)) at p5589
  simp only [e8928, e5437, e957, p8927, p5589]
theorem n8931 (_v : Vars) (_q : Query _v)  : (e8930 _v) := by
  have p8924 := n8924 _v _q 
  have p8929 := n8929 _v _q 
  change ((e570 _v) ↔ (e1637 _v)) at p8924
  change ((e5437 _v) = (e957 _v)) at p8929
  simp only [e8930, e8771, e5593, p8924, p8929]
theorem n8938 (_v : Vars) (_q : Query _v)  : (e8937 _v) := by
  have p5595 := n5595 _v _q 
  have p963 := n963 _v _q 
  exact (Eq.trans p5595 p963)
theorem n8939 (_v : Vars) (_q : Query _v)  : (e5602 _v) := by
  have p5601 := n5601 _v _q 
  have p5603 := n5603 _v _q 
  exact (Eq.trans p5601 p5603)
theorem n8941 (_v : Vars) (_q : Query _v)  : (e8940 _v) := by
  have p5605 := n5605 _v _q 
  have p976 := n976 _v _q 
  exact (Eq.trans p5605 p976)
theorem n8942 (_v : Vars) (_q : Query _v)  : (e5612 _v) := by
  have p5611 := n5611 _v _q 
  have p5613 := n5613 _v _q 
  exact (Eq.trans p5611 p5613)
theorem n8944 (_v : Vars) (_q : Query _v)  : (e8943 _v) := by
  have p5615 := n5615 _v _q 
  have p986 := n986 _v _q 
  exact (Eq.trans p5615 p986)
theorem n8945 (_v : Vars) (_q : Query _v)  : (e5622 _v) := by
  have p5621 := n5621 _v _q 
  have p5623 := n5623 _v _q 
  exact (Eq.trans p5621 p5623)
theorem n8947 (_v : Vars) (_q : Query _v)  : (e8946 _v) := by
  have p5625 := n5625 _v _q 
  have p996 := n996 _v _q 
  exact (Eq.trans p5625 p996)
theorem n8951 (_v : Vars) (_q : Query _v)  : (e8950 _v) := by
  simp only [e5, e8948, e8949, e8950] at *
  omega
theorem n8952 (_v : Vars) (_q : Query _v)  : (e1012 _v) := by
  have p5630 := n5630 _v _q 
  have p1011 := n1011 _v _q 
  exact (Eq.trans p5630 p1011)
theorem n8953 (_v : Vars) (_q : Query _v)  : (e1016 _v) := by
  have p8952 := n8952 _v _q 
  have p1015 := n1015 _v _q 
  exact (Eq.trans p8952 p1015)
theorem n8954 (_v : Vars) (_q : Query _v)  : (e5632 _v) := by
  have p8953 := n8953 _v _q 
  change ((e587 _v) = (e1013 _v)) at p8953
  simp only [e5632, e589, e1017, p8953]
theorem n8955 (_v : Vars) (_q : Query _v)  : (e1020 _v) := by
  simp only [e5, e6, e12, e36, e1013, e1017, e1018, e1019, e1020] at *
  omega
theorem n8956 (_v : Vars) (_q : Query _v)  : (e5633 _v) := by
  have p8954 := n8954 _v _q 
  have p8955 := n8955 _v _q 
  exact (Iff.trans p8954 p8955)
theorem n8957 (_v : Vars) (_q : Query _v)  : (e5641 _v) := by
  have p5640 := n5640 _v _q 
  change ((e590 _v) = (e1029 _v)) at p5640
  simp only [e5641, e591, e1679, p5640]
theorem n8958 (_v : Vars) (_q : Query _v)  : (e5642 _v) := by
  have p5640 := n5640 _v _q 
  change ((e590 _v) = (e1029 _v)) at p5640
  simp only [e5642, e592, e1034, p5640]
theorem n8959 (_v : Vars) (_q : Query _v)  : (e1037 _v) := by
  simp only [e12, e43, e760, e761, e1029, e1034, e1035, e1036, e1037] at *
  omega
theorem n8960 (_v : Vars) (_q : Query _v)  : (e5643 _v) := by
  have p8958 := n8958 _v _q 
  have p8959 := n8959 _v _q 
  exact (Iff.trans p8958 p8959)
theorem n8962 (_v : Vars) (_q : Query _v)  : (e8961 _v) := by
  have p8960 := n8960 _v _q 
  have p5640 := n5640 _v _q 
  change ((e592 _v) ↔ (e1036 _v)) at p8960
  change ((e590 _v) = (e1029 _v)) at p5640
  simp only [e8961, e5443, e1038, p8960, p5640]
theorem n8964 (_v : Vars) (_q : Query _v)  : (e8963 _v) := by
  have p8957 := n8957 _v _q 
  have p8962 := n8962 _v _q 
  change ((e591 _v) ↔ (e1679 _v)) at p8957
  change ((e5443 _v) = (e1038 _v)) at p8962
  simp only [e8963, e8779, e5644, p8957, p8962]
theorem n8965 (_v : Vars) (_q : Query _v)  : (e5651 _v) := by
  have p5650 := n5650 _v _q 
  change ((e593 _v) = (e1046 _v)) at p5650
  simp only [e5651, e594, e1686, p5650]
theorem n8966 (_v : Vars) (_q : Query _v)  : (e5652 _v) := by
  have p5650 := n5650 _v _q 
  change ((e593 _v) = (e1046 _v)) at p5650
  simp only [e5652, e595, e1051, p5650]
theorem n8967 (_v : Vars) (_q : Query _v)  : (e1054 _v) := by
  simp only [e12, e266, e781, e782, e1046, e1051, e1052, e1053, e1054] at *
  omega
theorem n8968 (_v : Vars) (_q : Query _v)  : (e5653 _v) := by
  have p8966 := n8966 _v _q 
  have p8967 := n8967 _v _q 
  exact (Iff.trans p8966 p8967)
theorem n8970 (_v : Vars) (_q : Query _v)  : (e8969 _v) := by
  have p8968 := n8968 _v _q 
  have p5650 := n5650 _v _q 
  change ((e595 _v) ↔ (e1053 _v)) at p8968
  change ((e593 _v) = (e1046 _v)) at p5650
  simp only [e8969, e5444, e1055, p8968, p5650]
theorem n8972 (_v : Vars) (_q : Query _v)  : (e8971 _v) := by
  have p8965 := n8965 _v _q 
  have p8970 := n8970 _v _q 
  change ((e594 _v) ↔ (e1686 _v)) at p8965
  change ((e5444 _v) = (e1055 _v)) at p8970
  simp only [e8971, e8780, e5654, p8965, p8970]
end
end Assembly
