import Dag029
import generated.th_lemma_0
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8009 (_v : Vars) (_q : Query _v)  : (e4533 _v) := by
  simp only [e5, e6, e12, e4525, e4530, e4531, e4532, e4533] at *
  omega
theorem n8010 (_v : Vars) (_q : Query _v)  : (e4535 _v) := by
  simp only [e5, e6, e12, e4526, e4530, e4531, e4534, e4535] at *
  omega
theorem n8012 (_v : Vars) (_q : Query _v)  : (e8011 _v) := by
  have p8009 := n8009 _v _q 
  have p8010 := n8010 _v _q 
  change ((e4525 _v) ↔ (e4532 _v)) at p8009
  change ((e4526 _v) ↔ (e4534 _v)) at p8010
  simp only [e8011, e4527, e4536, p8009, p8010]
theorem n8016 (_v : Vars) (_q : Query _v)  : (e8015 _v) := by
  simp only [e5, e6, e12, e4530, e4531, e4532, e4534, e4536, e4537, e4538, e8013, e8014, e8015] at *
  omega
theorem n8020 (_v : Vars) (_q : Query _v)  : (e8019 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e108, e109, e111, e802, e803, e2800, e4523, e4539, e8003, e8019] at *
  omega
theorem n8022 (_v : Vars) (_q : Query _v)  : (e8021 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e108, e109, e111, e802, e803, e2800, e4523, e4540, e8005, e8021] at *
  omega
theorem n8026 (_v : Vars) (_q : Query _v)  : (e8025 _v) := by
  have p8020 := n8020 _v _q 
  have p8022 := n8022 _v _q 
  change ((e4539 _v) ↔ (e8003 _v)) at p8020
  change ((e4540 _v) ↔ (e8005 _v)) at p8022
  simp only [e8025, e8023, e8024, p8020, p8022]
theorem n8031 (_v : Vars) (_q : Query _v)  : (e4554 _v) := by
  simp only [e5, e6, e12, e4542, e4543, e4544, e4549, e4554] at *
  omega
theorem n8032 (_v : Vars) (_q : Query _v)  : (e4555 _v) := by
  simp only [e5, e6, e12, e4542, e4543, e4546, e4550, e4555] at *
  omega
theorem n8034 (_v : Vars) (_q : Query _v)  : (e8033 _v) := by
  have p8031 := n8031 _v _q 
  have p8032 := n8032 _v _q 
  change ((e4549 _v) ↔ (e4544 _v)) at p8031
  change ((e4550 _v) ↔ (e4546 _v)) at p8032
  simp only [e8033, e4551, e4556, p8031, p8032]
theorem n8037 (_v : Vars) (_q : Query _v)  : (e8036 _v) := by
  simp only [e5, e6, e12, e4542, e4543, e4544, e4545, e4546, e4547, e4556, e8029, e8035, e8036] at *
  omega
theorem n8055 (_v : Vars) (_q : Query _v)  : (e8054 _v) := by
  simp only [e12, e4567, e4568, e4569, e4572, e4573, e4574, e4575, e8054] at *
  omega
theorem n8056 (_v : Vars) (_q : Query _v)  : (e4582 _v) := by
  simp only [e5, e6, e12, e2919, e4561, e4562, e4577, e4582] at *
  omega
theorem n8057 (_v : Vars) (_q : Query _v)  : (e4583 _v) := by
  simp only [e5, e6, e12, e2919, e4561, e4564, e4578, e4583] at *
  omega
theorem n8059 (_v : Vars) (_q : Query _v)  : (e8058 _v) := by
  have p8056 := n8056 _v _q 
  have p8057 := n8057 _v _q 
  change ((e4577 _v) ↔ (e4562 _v)) at p8056
  change ((e4578 _v) ↔ (e4564 _v)) at p8057
  simp only [e8058, e4579, e4584, p8056, p8057]
theorem n8062 (_v : Vars) (_q : Query _v)  : (e8061 _v) := by
  simp only [e5, e6, e12, e2919, e4561, e4562, e4563, e4564, e4565, e4584, e8052, e8060, e8061] at *
  omega
theorem n8074 (_v : Vars) (_q : Query _v)  : (e8073 _v) := by
  simp only [e4587, e4588, e8070, e8071, e8072, e8073] at *
  tauto
theorem n8075 (_v : Vars) (_q : Query _v)  : (e4598 _v) := by
  simp only [e5, e6, e12, e4590, e4595, e4596, e4597, e4598] at *
  omega
theorem n8076 (_v : Vars) (_q : Query _v)  : (e4600 _v) := by
  simp only [e5, e6, e12, e4591, e4595, e4596, e4599, e4600] at *
  omega
theorem n8078 (_v : Vars) (_q : Query _v)  : (e8077 _v) := by
  have p8075 := n8075 _v _q 
  have p8076 := n8076 _v _q 
  change ((e4590 _v) ↔ (e4597 _v)) at p8075
  change ((e4591 _v) ↔ (e4599 _v)) at p8076
  simp only [e8077, e4592, e4601, p8075, p8076]
theorem n8082 (_v : Vars) (_q : Query _v)  : (e8081 _v) := by
  simp only [e5, e6, e12, e4595, e4596, e4597, e4599, e4601, e4602, e4603, e8079, e8080, e8081] at *
  omega
theorem n8098 (_v : Vars) (_q : Query _v)  : (e8097 _v) := by
  simp only [e12, e3158, e3159, e3160, e3161, e3162, e4613, e4616, e8097] at *
  omega
theorem n8099 (_v : Vars) (_q : Query _v)  : (e4623 _v) := by
  simp only [e5, e6, e12, e2936, e4607, e4608, e4618, e4623] at *
  omega
theorem n8100 (_v : Vars) (_q : Query _v)  : (e4624 _v) := by
  simp only [e5, e6, e12, e2936, e4607, e4610, e4619, e4624] at *
  omega
theorem n8102 (_v : Vars) (_q : Query _v)  : (e8101 _v) := by
  have p8099 := n8099 _v _q 
  have p8100 := n8100 _v _q 
  change ((e4618 _v) ↔ (e4608 _v)) at p8099
  change ((e4619 _v) ↔ (e4610 _v)) at p8100
  simp only [e8101, e4620, e4625, p8099, p8100]
theorem n8105 (_v : Vars) (_q : Query _v)  : (e8104 _v) := by
  simp only [e5, e6, e12, e2936, e4607, e4608, e4609, e4610, e4611, e4625, e8095, e8103, e8104] at *
  omega
theorem n8116 (_v : Vars) (_q : Query _v)  : (e8115 _v) := by
  simp only [e4627, e4628, e8112, e8113, e8114, e8115] at *
  tauto
theorem n8117 (_v : Vars) (_q : Query _v)  : (e4638 _v) := by
  simp only [e5, e6, e12, e4630, e4635, e4636, e4637, e4638] at *
  omega
theorem n8118 (_v : Vars) (_q : Query _v)  : (e4640 _v) := by
  simp only [e5, e6, e12, e4631, e4635, e4636, e4639, e4640] at *
  omega
theorem n8120 (_v : Vars) (_q : Query _v)  : (e8119 _v) := by
  have p8117 := n8117 _v _q 
  have p8118 := n8118 _v _q 
  change ((e4630 _v) ↔ (e4637 _v)) at p8117
  change ((e4631 _v) ↔ (e4639 _v)) at p8118
  simp only [e8119, e4632, e4641, p8117, p8118]
theorem n8124 (_v : Vars) (_q : Query _v)  : (e8123 _v) := by
  simp only [e5, e6, e12, e4635, e4636, e4637, e4639, e4641, e4642, e4643, e8121, e8122, e8123] at *
  omega
theorem n8139 (_v : Vars) (_q : Query _v)  : (e8138 _v) := by
  exact FloorCertificate.node_8139  
theorem n8140 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) : (e196 _v) := by
  exact h196
theorem n8143 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) : (e8142 _v) := by
  have p8139 := n8139 _v _q 
  have p8140 := n8140 _v _q h196
  exact FloorCertificate.node_8143 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p8139 p8140
theorem n8144 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e496 _v) := by
  exact h496
theorem n8147 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e8146 _v) := by
  have p8139 := n8139 _v _q 
  have p8144 := n8144 _v _q h496
  exact FloorCertificate.node_8147 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p8139 p8144
theorem n8152 (_v : Vars) (_q : Query _v)  : (e8151 _v) := by
  simp only [e12, e4653, e4654, e4655, e4658, e4659, e4660, e4661, e8151] at *
  omega
theorem n8153 (_v : Vars) (_q : Query _v)  : (e4668 _v) := by
  simp only [e5, e6, e12, e2952, e4647, e4648, e4663, e4668] at *
  omega
theorem n8154 (_v : Vars) (_q : Query _v)  : (e4669 _v) := by
  simp only [e5, e6, e12, e2952, e4647, e4650, e4664, e4669] at *
  omega
theorem n8156 (_v : Vars) (_q : Query _v)  : (e8155 _v) := by
  have p8153 := n8153 _v _q 
  have p8154 := n8154 _v _q 
  change ((e4663 _v) ↔ (e4648 _v)) at p8153
  change ((e4664 _v) ↔ (e4650 _v)) at p8154
  simp only [e8155, e4665, e4670, p8153, p8154]
theorem n8159 (_v : Vars) (_q : Query _v)  : (e8158 _v) := by
  simp only [e5, e6, e12, e2952, e4647, e4648, e4649, e4650, e4651, e4670, e8149, e8157, e8158] at *
  omega
theorem n8169 (_v : Vars) (_q : Query _v)  : (e8168 _v) := by
  simp only [e12, e4678, e4679, e4680, e4683, e4684, e4685, e4686, e8168] at *
  omega
theorem n8170 (_v : Vars) (_q : Query _v)  : (e4693 _v) := by
  simp only [e5, e6, e12, e4671, e4672, e4673, e4688, e4693] at *
  omega
theorem n8171 (_v : Vars) (_q : Query _v)  : (e4694 _v) := by
  simp only [e5, e6, e12, e4671, e4672, e4675, e4689, e4694] at *
  omega
theorem n8173 (_v : Vars) (_q : Query _v)  : (e8172 _v) := by
  have p8170 := n8170 _v _q 
  have p8171 := n8171 _v _q 
  change ((e4688 _v) ↔ (e4673 _v)) at p8170
  change ((e4689 _v) ↔ (e4675 _v)) at p8171
  simp only [e8172, e4690, e4695, p8170, p8171]
end
end Assembly
