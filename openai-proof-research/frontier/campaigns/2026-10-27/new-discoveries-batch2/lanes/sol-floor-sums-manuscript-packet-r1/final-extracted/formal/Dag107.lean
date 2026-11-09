import Dag106
import generated.th_lemma_5
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14410 (_v : Vars) (_q : Query _v)  : (e7112 _v) := by
  have p14409 := n14409 _v _q 
  simp only [e2417, e3462, e3463, e3464, e3465, e3466, e3472, e3480, e3482, e3485, e3486, e6608, e7105, e7106, e7109, e7112, e7114, e10703, e10704, e13595] at *
  tauto
theorem n14411 (_v : Vars) (_q : Query _v)  : (e2417 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14411 (e2 _v) (e17 _v) (e45 _v) p8663 p10893
theorem n14412 (_v : Vars) (_q : Query _v)  : (e3472 _v) := by
  have p14410 := n14410 _v _q 
  have p14411 := n14411 _v _q 
  simp only [e2417, e3462, e3463, e3464, e3465, e3466, e3472, e6608, e7112] at *
  tauto
theorem n14413 (_v : Vars) (_q : Query _v)  : (e13605 _v) := by
  have p10326 := n10326 _v _q 
  have p13609 := n13609 _v _q 
  simp only [e2451, e3487, e3488, e3489, e3490, e3491, e3493, e3497, e3498, e3505, e3507, e3510, e3511, e6624, e6625, e6626, e6627, e7121, e7122, e7125, e7128, e7130, e10711, e10712, e13605, e13608] at *
  tauto
theorem n14414 (_v : Vars) (_q : Query _v)  : (e7128 _v) := by
  have p14413 := n14413 _v _q 
  simp only [e2451, e3487, e3488, e3489, e3490, e3491, e3497, e3505, e3507, e3510, e3511, e6624, e7121, e7122, e7125, e7128, e7130, e10711, e10712, e13605] at *
  tauto
theorem n14415 (_v : Vars) (_q : Query _v)  : (e2451 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14415 (e2 _v) (e17 _v) (e45 _v) p8663 p10893 p331
theorem n14416 (_v : Vars) (_q : Query _v)  : (e3497 _v) := by
  have p14414 := n14414 _v _q 
  have p14415 := n14415 _v _q 
  simp only [e2451, e3487, e3488, e3489, e3490, e3491, e3497, e6624, e7128] at *
  tauto
theorem n14417 (_v : Vars) (_q : Query _v)  : (e13615 _v) := by
  have p12210 := n12210 _v _q 
  have p13619 := n13619 _v _q 
  simp only [e2324, e3512, e3513, e3514, e3515, e3516, e3518, e3522, e3524, e3532, e3534, e3537, e3538, e6561, e6562, e6563, e6564, e7137, e7138, e7141, e7144, e7146, e10719, e10720, e13615, e13618] at *
  tauto
theorem n14418 (_v : Vars) (_q : Query _v)  : (e7144 _v) := by
  have p14417 := n14417 _v _q 
  simp only [e2324, e3512, e3513, e3514, e3515, e3516, e3522, e3532, e3534, e3537, e3538, e6561, e7137, e7138, e7141, e7144, e7146, e10719, e10720, e13615] at *
  tauto
theorem n14419 (_v : Vars) (_q : Query _v)  : (e2324 _v) := by
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_14419 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p10896 p8663
theorem n14420 (_v : Vars) (_q : Query _v)  : (e3522 _v) := by
  have p14418 := n14418 _v _q 
  have p14419 := n14419 _v _q 
  simp only [e2324, e3512, e3513, e3514, e3515, e3516, e3522, e6561, e7144] at *
  tauto
theorem n14421 (_v : Vars) (_q : Query _v)  : (e13625 _v) := by
  have p10148 := n10148 _v _q 
  have p13629 := n13629 _v _q 
  simp only [e2076, e3539, e3540, e3541, e3542, e3543, e3545, e3549, e3550, e3557, e3559, e3562, e3563, e6462, e6463, e6464, e6465, e7153, e7154, e7157, e7160, e7162, e10727, e10728, e13625, e13628] at *
  tauto
theorem n14422 (_v : Vars) (_q : Query _v)  : (e7160 _v) := by
  have p14421 := n14421 _v _q 
  simp only [e2076, e3539, e3540, e3541, e3542, e3543, e3549, e3557, e3559, e3562, e3563, e6462, e7153, e7154, e7157, e7160, e7162, e10727, e10728, e13625] at *
  tauto
theorem n14423 (_v : Vars) (_q : Query _v)  : (e2076 _v) := by
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_14423 (e2 _v) (e17 _v) (e110 _v) p8663 p11375
theorem n14424 (_v : Vars) (_q : Query _v)  : (e3549 _v) := by
  have p14422 := n14422 _v _q 
  have p14423 := n14423 _v _q 
  simp only [e2076, e3539, e3540, e3541, e3542, e3543, e3549, e6462, e7160] at *
  tauto
theorem n14425 (_v : Vars) (_q : Query _v)  : (e13635 _v) := by
  have p12304 := n12304 _v _q 
  have p13639 := n13639 _v _q 
  simp only [e2536, e3564, e3565, e3566, e3570, e3571, e3572, e3573, e3575, e3583, e3585, e3588, e3589, e6656, e6657, e6658, e6659, e7169, e7170, e7173, e7176, e7178, e10735, e10736, e13635, e13638] at *
  tauto
theorem n14426 (_v : Vars) (_q : Query _v)  : (e7176 _v) := by
  have p14425 := n14425 _v _q 
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173, e7176, e7178, e10735, e10736, e13635] at *
  tauto
theorem n14427 (_v : Vars) (_q : Query _v)  : (e7173 _v) := by
  have p14425 := n14425 _v _q 
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173, e7176, e7178, e10735, e10736, e13635] at *
  tauto
theorem n14428 (_v : Vars) (_q : Query _v)  : (e7200 _v) := by
  have p12489 := n12489 _v _q 
  change ((e3592 _v) ↔ (e7194 _v)) at p12489
  simp only [e7200, e7198, e7199, p12489]
theorem n14429 (_v : Vars) (_q : Query _v)  : (e12496 _v) := by
  have p14428 := n14428 _v _q 
  have p13642 := n13642 _v _q 
  change ((e7198 _v) ↔ (e7199 _v)) at p14428
  change ((e6655 _v) ↔ (e10747 _v)) at p13642
  simp only [e12496, e10347, e10748, p14428, p13642]
theorem n14431 (_v : Vars) (_q : Query _v)  : (e14430 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e2542, e2543, e3591, e3598, e3599, e3600, e3602, e3605, e3606, e7183, e7184, e7185, e7186, e7187, e7193, e7194, e7197, e7199, e7204, e7205, e10747, e10748, e10749, e10750, e10751, e14430] at *
  omega
theorem n14432 (_v : Vars) (_q : Query _v)  : (e12497 _v) := by
  have p14429 := n14429 _v _q 
  have p14431 := n14431 _v _q 
  exact (Iff.trans p14429 p14431)
theorem n14433 (_v : Vars) (_q : Query _v)  : (e10751 _v) := by
  have p10348 := n10348 _v _q 
  have p14432 := n14432 _v _q 
  simp only [e2543, e3592, e3600, e3602, e3605, e3606, e6654, e6655, e7183, e7184, e7185, e7186, e7187, e7193, e7194, e7197, e7198, e7199, e7204, e7205, e10347, e10747, e10749, e10750, e10751, e12497] at *
  tauto
theorem n14434 (_v : Vars) (_q : Query _v)  : (e13648 _v) := by
  have p10202 := n10202 _v _q 
  have p13652 := n13652 _v _q 
  simp only [e2194, e3610, e3611, e3612, e3613, e3614, e3616, e3620, e3621, e3628, e3630, e3633, e3634, e6509, e6510, e6511, e6512, e7212, e7213, e7216, e7219, e7221, e10758, e10759, e13648, e13651] at *
  tauto
theorem n14435 (_v : Vars) (_q : Query _v)  : (e7219 _v) := by
  have p14434 := n14434 _v _q 
  simp only [e2194, e3610, e3611, e3612, e3613, e3614, e3620, e3628, e3630, e3633, e3634, e6509, e7212, e7213, e7216, e7219, e7221, e10758, e10759, e13648] at *
  tauto
theorem n14436 (_v : Vars) (_q : Query _v)  : (e2194 _v) := by
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14436 (e2 _v) (e9 _v) (e17 _v) p8663 p10896
theorem n14437 (_v : Vars) (_q : Query _v)  : (e3620 _v) := by
  have p14435 := n14435 _v _q 
  have p14436 := n14436 _v _q 
  simp only [e2194, e3610, e3611, e3612, e3613, e3614, e3620, e6509, e7219] at *
  tauto
theorem n14438 (_v : Vars) (_q : Query _v)  : (e13658 _v) := by
  have p10128 := n10128 _v _q 
  have p13662 := n13662 _v _q 
  simp only [e2044, e3635, e3636, e3637, e3638, e3639, e3641, e3645, e3646, e3653, e3655, e3658, e3659, e6447, e6448, e6449, e6450, e7228, e7229, e7232, e7235, e7237, e10766, e10767, e13658, e13661] at *
  tauto
theorem n14439 (_v : Vars) (_q : Query _v)  : (e7235 _v) := by
  have p14438 := n14438 _v _q 
  simp only [e2044, e3635, e3636, e3637, e3638, e3639, e3645, e3653, e3655, e3658, e3659, e6447, e7228, e7229, e7232, e7235, e7237, e10766, e10767, e13658] at *
  tauto
theorem n14440 (_v : Vars) (_q : Query _v)  : (e2044 _v) := by
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14440 (e2 _v) (e7 _v) (e17 _v) p11376 p8663 p331
theorem n14441 (_v : Vars) (_q : Query _v)  : (e3645 _v) := by
  have p14439 := n14439 _v _q 
  have p14440 := n14440 _v _q 
  simp only [e2044, e3635, e3636, e3637, e3638, e3639, e3645, e6447, e7235] at *
  tauto
theorem n14442 (_v : Vars) (_q : Query _v)  : (e13668 _v) := by
  have p12274 := n12274 _v _q 
  have p13672 := n13672 _v _q 
  simp only [e2496, e3660, e3661, e3662, e3663, e3664, e3666, e3670, e3672, e3680, e3682, e3685, e3686, e6642, e6643, e6644, e6645, e7244, e7245, e7248, e7251, e7253, e10774, e10775, e13668, e13671] at *
  tauto
theorem n14443 (_v : Vars) (_q : Query _v)  : (e7251 _v) := by
  have p14442 := n14442 _v _q 
  simp only [e2496, e3660, e3661, e3662, e3663, e3664, e3670, e3680, e3682, e3685, e3686, e6642, e7244, e7245, e7248, e7251, e7253, e10774, e10775, e13668] at *
  tauto
theorem n14444 (_v : Vars) (_q : Query _v)  : (e2496 _v) := by
  have p11376 := n11376 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_14444 (e2 _v) (e7 _v) (e17 _v) (e45 _v) p11376 p10893 p8663
theorem n14445 (_v : Vars) (_q : Query _v)  : (e3670 _v) := by
  have p14443 := n14443 _v _q 
  have p14444 := n14444 _v _q 
  simp only [e2496, e3660, e3661, e3662, e3663, e3664, e3670, e6642, e7251] at *
  tauto
theorem n14446 (_v : Vars) (_q : Query _v)  : (e13678 _v) := by
  have p12180 := n12180 _v _q 
  have p13682 := n13682 _v _q 
  simp only [e2282, e3687, e3688, e3689, e3690, e3691, e3693, e3697, e3699, e3707, e3709, e3712, e3713, e6543, e6544, e6545, e6546, e7260, e7261, e7264, e7267, e7269, e10782, e10783, e13678, e13681] at *
  tauto
theorem n14447 (_v : Vars) (_q : Query _v)  : (e7267 _v) := by
  have p14446 := n14446 _v _q 
  simp only [e2282, e3687, e3688, e3689, e3690, e3691, e3697, e3707, e3709, e3712, e3713, e6543, e7260, e7261, e7264, e7267, e7269, e10782, e10783, e13678] at *
  tauto
theorem n14448 (_v : Vars) (_q : Query _v)  : (e2282 _v) := by
  have p10896 := n10896 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14448 (e2 _v) (e7 _v) (e9 _v) (e17 _v) p10896 p8663 p11376 p331
theorem n14449 (_v : Vars) (_q : Query _v)  : (e3697 _v) := by
  have p14447 := n14447 _v _q 
  have p14448 := n14448 _v _q 
  simp only [e2282, e3687, e3688, e3689, e3690, e3691, e3697, e6543, e7267] at *
  tauto
theorem n14450 (_v : Vars) (_q : Query _v)  : (e13688 _v) := by
  have p12220 := n12220 _v _q 
  have p13692 := n13692 _v _q 
  simp only [e2338, e3714, e3715, e3716, e3717, e3718, e3720, e3724, e3726, e3734, e3736, e3739, e3740, e6567, e6568, e6569, e6570, e7276, e7277, e7280, e7283, e7285, e10790, e10791, e13688, e13691] at *
  tauto
theorem n14451 (_v : Vars) (_q : Query _v)  : (e7283 _v) := by
  have p14450 := n14450 _v _q 
  simp only [e2338, e3714, e3715, e3716, e3717, e3718, e3724, e3734, e3736, e3739, e3740, e6567, e7276, e7277, e7280, e7283, e7285, e10790, e10791, e13688] at *
  tauto
theorem n14452 (_v : Vars) (_q : Query _v)  : (e2338 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14452 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p8663 p10896 p331
theorem n14453 (_v : Vars) (_q : Query _v)  : (e3724 _v) := by
  have p14451 := n14451 _v _q 
  have p14452 := n14452 _v _q 
  simp only [e2338, e3714, e3715, e3716, e3717, e3718, e3724, e6567, e7283] at *
  tauto
theorem n14454 (_v : Vars) (_q : Query _v)  : (e13698 _v) := by
  have p12380 := n12380 _v _q 
  have p13702 := n13702 _v _q 
  simp only [e2662, e3741, e3742, e3743, e3744, e3745, e3747, e3751, e3753, e3761, e3763, e3766, e3767, e6712, e6713, e6714, e6715, e7292, e7293, e7296, e7299, e7301, e10798, e10799, e13698, e13701] at *
  tauto
theorem n14455 (_v : Vars) (_q : Query _v)  : (e7299 _v) := by
  have p14454 := n14454 _v _q 
  simp only [e2662, e3741, e3742, e3743, e3744, e3745, e3751, e3761, e3763, e3766, e3767, e6712, e7292, e7293, e7296, e7299, e7301, e10798, e10799, e13698] at *
  tauto
end
end Assembly
