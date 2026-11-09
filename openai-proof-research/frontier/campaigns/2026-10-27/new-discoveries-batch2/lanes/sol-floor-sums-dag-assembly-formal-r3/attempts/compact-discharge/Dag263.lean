import Dag262
import generated.th_lemma_35
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22004 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p22003 := n22003 _v _q 
  have p8583 := n8583 _v _q h2296
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  simp only [e51, e57, e79, e2296, e4306, e4311, e4653, e4658, e4813, e4814, e6549, e22002] at *
  tauto
theorem n22005 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22004 := n22004 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n22006 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22005 := n22005 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n22007 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8310 _v) := by
  have p21698 := n21698 _v _q 
  have p22006 := n22006 _v _q h51 h2296 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8583 := n8583 _v _q h2296
  simp only [e51, e57, e91, e95, e2296, e2529, e4306, e4311, e4653, e4658, e4813, e4814, e6549, e8310, e21697] at *
  tauto
theorem n22008 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7807 _v) := by
  have p11387 := n11387 _v _q 
  have p22007 := n22007 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2303, e2529, e7807, e8310, e11386] at *
  tauto
theorem n22009 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p22008 := n22008 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2132, e2303, e7742, e7807, e11352] at *
  tauto
theorem n22010 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p22009 := n22009 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n22011 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22008 := n22008 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n22012 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8038 _v) := by
  have p11493 := n11493 _v _q 
  have p22007 := n22007 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2475, e2529, e8038, e8310, e11492] at *
  tauto
theorem n22013 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p22012 := n22012 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n22014 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22013 := n22013 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n22015 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p22012 := n22012 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n22016 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p22015 := n22015 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n22017 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2781 _v) := by
  have p8605 := n8605 _v _q 
  have p8583 := n8583 _v _q h2296
  have p22012 := n22012 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2296, e2475, e2781, e6549, e8038, e8604] at *
  tauto
theorem n22018 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p22017 := n22017 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n22019 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p22010 := n22010 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n22020 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p22019 := n22019 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e4459, e7749, e7752, e16783] at *
  tauto
theorem n22021 (_v : Vars) (_q : Query _v)  : (e8600 _v) := by
  simp only [e7812, e7814, e7816, e7817, e7818, e8600] at *
  tauto
theorem n22022 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7812 _v) := by
  have p22021 := n22021 _v _q 
  have p22011 := n22011 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8600] at *
  tauto
theorem n22023 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p22022 := n22022 _v _q h51 h2296 h4306 h4653 h4813
  have p15100 := n15100 _v _q h2296
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_22023 (e2 _v) (e9 _v) (e17 _v) (e110 _v) (e2945 _v) (e3141 _v) p22022 p15100 p8583
theorem n22024 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5098 _v) := by
  have p16684 := n16684 _v _q 
  have p22014 := n22014 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8582] at *
  tauto
theorem n22025 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4675 _v) := by
  have p16115 := n16115 _v _q h2296
  have p22024 := n22024 _v _q h51 h2296 h4306 h4653 h4813
  have p16102 := n16102 _v _q h2296
  exact FloorCertificate.node_22025 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e2941 _v) p16115 p22024 p16102
theorem n22026 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22014 := n22014 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8479] at *
  tauto
theorem n22027 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22011 := n22011 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n22028 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p22018 := n22018 _v _q h51 h2296 h4306 h4653 h4813
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n22029 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3942 _v) := by
  have p20869 := n20869 _v _q 
  have p22023 := n22023 _v _q h51 h2296 h4306 h4653 h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p22006 := n22006 _v _q h51 h2296 h4306 h4653 h4813
  have p22026 := n22026 _v _q h51 h2296 h4306 h4653 h4813
  have p22020 := n22020 _v _q h51 h2296 h4306 h4653 h4813
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p22027 := n22027 _v _q h51 h2296 h4306 h4653 h4813
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  have p22016 := n22016 _v _q h51 h2296 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p22025 := n22025 _v _q h51 h2296 h4306 h4653 h4813
  have p22012 := n22012 _v _q h51 h2296 h4306 h4653 h4813
  have p22028 := n22028 _v _q h51 h2296 h4306 h4653 h4813
  have p17065 := n17065 _v _q h4101
  have p4983 := n4983 _v _q h4813
  simp only [e51, e57, e91, e95, e196, e2475, e3152, e3156, e3158, e3159, e3937, e3942, e4101, e4106, e4264, e4269, e4306, e4311, e4439, e4444, e4459, e4464, e4567, e4572, e4653, e4658, e4675, e4676, e4787, e4788, e4813, e4814, e5100, e5103, e5195, e7814, e7817, e8038, e8045, e8048, e8317, e8320, e20868] at *
  tauto
theorem n22030 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p22029 := n22029 _v _q h51 h2296 h3158 h4101 h4306 h4653 h4813
  simp only [e3937, e3939, e3942, e3943, e7415, e7633] at *
  tauto
theorem n22031 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p22030 := n22030 _v _q h51 h2296 h3158 h4101 h4306 h4653 h4813
  simp only [e2402, e3937, e3939, e3942, e3943, e7415, e7416, e7419] at *
  tauto
theorem n22032 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22031 := n22031 _v _q h51 h2296 h3158 h4101 h4306 h4653 h4813
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n22033 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22032 := n22032 _v _q h51 h2296 h3158 h4101 h4306 h4653 h4813
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n22034 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p331 := n331 _v _q 
  have p22004 := n22004 _v _q h51 h2296 h4306 h4653 h4813
  have p16102 := n16102 _v _q h2296
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  have p22006 := n22006 _v _q h51 h2296 h4306 h4653 h4813
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p22020 := n22020 _v _q h51 h2296 h4306 h4653 h4813
  have p17072 := n17072 _v _q 
  have p22033 := n22033 _v _q h51 h2296 h3158 h4101 h4306 h4653 h4813
  have p17074 := n17074 _v _q 
  have p15100 := n15100 _v _q h2296
  have p16115 := n16115 _v _q h2296
  have p22028 := n22028 _v _q h51 h2296 h4306 h4653 h4813
  have p17069 := n17069 _v _q 
  have p13951 := n13951 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p22016 := n22016 _v _q h51 h2296 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  exact FloorCertificate.node_22034 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17108 p17294 p331 p22004 p16102 p21944 p22006 p16943 p17064 p17067 p17080 p22020 p17072 p22033 p17074 p15100 p16115 p22028 p17069 p13951 p17065 p20836 p20461 p21948 p16885 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p22016 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21728 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131
theorem n22036 (_v : Vars) (_q : Query _v)  : (e22035 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h2296 : (e2296 _v) := by
    tauto
  have h3158 : (e3158 _v) := by
    tauto
  have h4101 : (e4101 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have p22034 := n22034 _v _q h51 h2296 h3158 h4101 h4306 h4653 h4813
  exact p22034
theorem n22037 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6549 _v) := by
  have p22036 := n22036 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  simp only [e51, e57, e2296, e3158, e3159, e4101, e4106, e4306, e4311, e4653, e4658, e4813, e4814, e6549, e22035] at *
  tauto
theorem n22038 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p22037 := n22037 _v _q h51 h3158 h4101 h4306 h4653 h4813
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n22039 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p22038 := n22038 _v _q h51 h3158 h4101 h4306 h4653 h4813
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n22040 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e3942 _v) := by
  have p17131 := n17131 _v _q 
  have p17147 := n17147 _v _q 
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p17108 := n17108 _v _q 
  have p5255 := n5255 _v _q 
  have p13951 := n13951 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p15373 := n15373 _v _q h7807
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p16578 := n16578 _v _q 
  have p8601 := n8601 _v _q h6776
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17069 := n17069 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p16858 := n16858 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p11350 := n11350 _v _q h7807
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p15209 := n15209 _v _q h8038
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p8602 := n8602 _v _q h8038
  have p17009 := n17009 _v _q 
  have p17786 := n17786 _v _q h7807
  have p15956 := n15956 _v _q h6776
  have p16966 := n16966 _v _q h7807 h8038
  have p18959 := n18959 _v _q h7807
  have p5006 := n5006 _v _q h4675
  have p17245 := n17245 _v _q h5145
  exact FloorCertificate.node_22040 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17131 p17147 p20096 p17294 p17108 p5255 p13951 p16943 p17064 p17067 p17080 p15373 p17072 p17074 p16578 p8601 p22039 p17069 p16885 p17065 p20836 p20461 p21948 p16858 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p11350 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p15209 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21728 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p8602 p17009 p17786 p15956 p16966 p18959 p5006 p17245
theorem n22041 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p22040 := n22040 _v _q h51 h3158 h4101 h4306 h4653 h4675 h4813 h5145 h6776 h7807 h8038
  simp only [e3937, e3939, e3942, e3943, e7415, e7633] at *
  tauto
theorem n22042 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p22041 := n22041 _v _q h51 h3158 h4101 h4306 h4653 h4675 h4813 h5145 h6776 h7807 h8038
  simp only [e2402, e3937, e3939, e3942, e3943, e7415, e7416, e7419] at *
  tauto
theorem n22043 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22042 := n22042 _v _q h51 h3158 h4101 h4306 h4653 h4675 h4813 h5145 h6776 h7807 h8038
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n22044 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22043 := n22043 _v _q h51 h3158 h4101 h4306 h4653 h4675 h4813 h5145 h6776 h7807 h8038
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n22045 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p4946 := n4946 _v _q 
  have p16885 := n16885 _v _q h3158
  have p13951 := n13951 _v _q 
  have p17245 := n17245 _v _q h5145
  have p8601 := n8601 _v _q h6776
  have p8602 := n8602 _v _q h8038
  have p11350 := n11350 _v _q h7807
  have p17131 := n17131 _v _q 
  have p16966 := n16966 _v _q h7807 h8038
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17053 := n17053 _v _q 
  have p17072 := n17072 _v _q 
  have p22044 := n22044 _v _q h51 h3158 h4101 h4306 h4653 h4675 h4813 h5145 h6776 h7807 h8038
  have p17074 := n17074 _v _q 
  have p18959 := n18959 _v _q h7807
  have p5006 := n5006 _v _q h4675
  have p15956 := n15956 _v _q h6776
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p15209 := n15209 _v _q h8038
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17786 := n17786 _v _q h7807
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p15373 := n15373 _v _q h7807
  exact FloorCertificate.node_22045 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4946 p16885 p13951 p17245 p8601 p8602 p11350 p17131 p16966 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p22044 p17074 p18959 p5006 p15956 p17069 p20096 p17065 p20836 p20461 p21948 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p15209 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21728 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17009 p17786 p22039 p15373
theorem n22047 (_v : Vars) (_q : Query _v)  : (e22046 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e3158 _v)) ∨ (e2781 _v) ∨ (e2475 _v) ∨ (e2303 _v) ∨ (¬ (e4675 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h3158 : (e3158 _v) := by
    tauto
  have h4101 : (e4101 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h5145 : (e5145 _v) := by
    tauto
  have h6776 : (e6776 _v) := by
    change (¬ (e2781 _v))
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p22045 := n22045 _v _q h51 h3158 h4101 h4306 h4653 h4675 h4813 h5145 h6776 h7807 h8038
  exact p22045
theorem n22048 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6776 : (e6776 _v)) : (e5148 _v) := by
  have p22047 := n22047 _v _q 
  have p21600 := n21600 _v _q h51 h4306 h4653 h4813 h6525
  have p8601 := n8601 _v _q h6776
  have p16885 := n16885 _v _q h3158
  have p21601 := n21601 _v _q h51 h4306 h4653 h4813 h6525
  have p16058 := n16058 _v _q h6525
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  simp only [e51, e57, e2303, e2475, e2781, e3158, e3159, e4101, e4106, e4306, e4311, e4653, e4658, e4675, e4676, e4813, e4814, e5145, e5148, e6776, e7807, e8038, e22046] at *
  tauto
theorem n22049 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6776 : (e6776 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p22048 := n22048 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525 h6776
  simp only [e5143, e5145, e5147, e5148, e5149, e5152] at *
  tauto
theorem n22050 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6776 : (e6776 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p22049 := n22049 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525 h6776
  simp only [e79, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
end
end Assembly
