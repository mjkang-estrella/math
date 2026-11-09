import R9_5_0MergeB0
import R9_5_0MergeB1
import R9_5_0MergeB2
import R9_5_0MergeB3
import R9_5_0MergeB4
import R9_5_0MergeB5
import R9_5_0MergeB6
import R9_5_0MergeB7
import R9_5_0MergeB8
import R9_5_0MergeB9
import R9_5_0MergeB10
import R9_5_0MergeB11
import R9_5_0MergeB12
import R9_5_0MergeB13
import R9_5_0MergeB14
import R9_5_0MergeB15
import R9_5_0MergeB16
import R9_5_0MergeB17
import R9_5_0MergeB18
import R9_5_0MergeB19
import R9_5_0MergeB20
import R9_5_0MergeB21
import R9_5_0MergeB22
import R9_5_0MergeB23
import R9_5_0MergeB24
import R9_5_0MergeB25
import R9_5_0MergeB26
import R9_5_0MergeB27
import R9_5_0MergeB28
import R9_5_0MergeB29
import R9_5_0MergeB30
import R9_5_0MergeB31
import R9_5_0MergeB32
import R9_5_0MergeB33
import R9_5_0MergeB34
import R9_5_0MergeB35
import R9_5_0MergeB36
import R9_5_0MergeB37
import R9_5_0MergeB38
import R9_5_0MergeB39
import R9_5_0MergeB40
import R9_5_0MergeB41
import R9_5_0MergeB42
import R9_5_0MergeB43
import R9_5_0MergeB44
import R9_5_0MergeB45
import R9_5_0MergeB46
import R9_5_0MergeB47
import R9_5_0MergeB48
import R9_5_0MergeB49
import R9_5_0MergeB50
import R9_5_0MergeB51
import R9_5_0MergeB52
import R9_5_0MergeB53
import R9_5_0MergeB54
import R9_5_0MergeB55
import R9_5_0MergeB56
import R9_5_0MergeB57
import R9_5_0MergeB58
import R9_5_0MergeB59
import R9_5_0MergeB60
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 1024, halfCheck 10 30 table u.val = true := by
  intro u
  by_cases h30 : u.val < 743
  ·
    by_cases h15 : u.val < 467
    ·
      by_cases h7 : u.val < 287
      ·
        by_cases h3 : u.val < 177
        ·
          by_cases h1 : u.val < 90
          ·
            have hb : u.val-0 < 90 := by omega
            have he : u.val-0+0 = u.val := by omega
            have hp := merge_checkB0 ⟨u.val-0,hb⟩
            simpa only [he] using hp
          ·
            by_cases h2 : u.val < 126
            ·
              have hb : u.val-90 < 36 := by omega
              have he : u.val-90+90 = u.val := by omega
              have hp := merge_checkB1 ⟨u.val-90,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-126 < 51 := by omega
              have he : u.val-126+126 = u.val := by omega
              have hp := merge_checkB2 ⟨u.val-126,hb⟩
              simpa only [he] using hp
        ·
          by_cases h5 : u.val < 237
          ·
            by_cases h4 : u.val < 211
            ·
              have hb : u.val-177 < 34 := by omega
              have he : u.val-177+177 = u.val := by omega
              have hp := merge_checkB3 ⟨u.val-177,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-211 < 26 := by omega
              have he : u.val-211+211 = u.val := by omega
              have hp := merge_checkB4 ⟨u.val-211,hb⟩
              simpa only [he] using hp
          ·
            by_cases h6 : u.val < 252
            ·
              have hb : u.val-237 < 15 := by omega
              have he : u.val-237+237 = u.val := by omega
              have hp := merge_checkB5 ⟨u.val-237,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-252 < 35 := by omega
              have he : u.val-252+252 = u.val := by omega
              have hp := merge_checkB6 ⟨u.val-252,hb⟩
              simpa only [he] using hp
      ·
        by_cases h11 : u.val < 383
        ·
          by_cases h9 : u.val < 351
          ·
            by_cases h8 : u.val < 319
            ·
              have hb : u.val-287 < 32 := by omega
              have he : u.val-287+287 = u.val := by omega
              have hp := merge_checkB7 ⟨u.val-287,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-319 < 32 := by omega
              have he : u.val-319+319 = u.val := by omega
              have hp := merge_checkB8 ⟨u.val-319,hb⟩
              simpa only [he] using hp
          ·
            by_cases h10 : u.val < 374
            ·
              have hb : u.val-351 < 23 := by omega
              have he : u.val-351+351 = u.val := by omega
              have hp := merge_checkB9 ⟨u.val-351,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-374 < 9 := by omega
              have he : u.val-374+374 = u.val := by omega
              have hp := merge_checkB10 ⟨u.val-374,hb⟩
              simpa only [he] using hp
        ·
          by_cases h13 : u.val < 435
          ·
            by_cases h12 : u.val < 413
            ·
              have hb : u.val-383 < 30 := by omega
              have he : u.val-383+383 = u.val := by omega
              have hp := merge_checkB11 ⟨u.val-383,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-413 < 22 := by omega
              have he : u.val-413+413 = u.val := by omega
              have hp := merge_checkB12 ⟨u.val-413,hb⟩
              simpa only [he] using hp
          ·
            by_cases h14 : u.val < 447
            ·
              have hb : u.val-435 < 12 := by omega
              have he : u.val-435+435 = u.val := by omega
              have hp := merge_checkB13 ⟨u.val-435,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-447 < 20 := by omega
              have he : u.val-447+447 = u.val := by omega
              have hp := merge_checkB14 ⟨u.val-447,hb⟩
              simpa only [he] using hp
    ·
      by_cases h22 : u.val < 582
      ·
        by_cases h18 : u.val < 501
        ·
          by_cases h16 : u.val < 479
          ·
            have hb : u.val-467 < 12 := by omega
            have he : u.val-467+467 = u.val := by omega
            have hp := merge_checkB15 ⟨u.val-467,hb⟩
            simpa only [he] using hp
          ·
            by_cases h17 : u.val < 492
            ·
              have hb : u.val-479 < 13 := by omega
              have he : u.val-479+479 = u.val := by omega
              have hp := merge_checkB16 ⟨u.val-479,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-492 < 9 := by omega
              have he : u.val-492+492 = u.val := by omega
              have hp := merge_checkB17 ⟨u.val-492,hb⟩
              simpa only [he] using hp
        ·
          by_cases h20 : u.val < 511
          ·
            by_cases h19 : u.val < 507
            ·
              have hb : u.val-501 < 6 := by omega
              have he : u.val-501+501 = u.val := by omega
              have hp := merge_checkB18 ⟨u.val-501,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-507 < 4 := by omega
              have he : u.val-507+507 = u.val := by omega
              have hp := merge_checkB19 ⟨u.val-507,hb⟩
              simpa only [he] using hp
          ·
            by_cases h21 : u.val < 547
            ·
              have hb : u.val-511 < 36 := by omega
              have he : u.val-511+511 = u.val := by omega
              have hp := merge_checkB20 ⟨u.val-511,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-547 < 35 := by omega
              have he : u.val-547+547 = u.val := by omega
              have hp := merge_checkB21 ⟨u.val-547,hb⟩
              simpa only [he] using hp
      ·
        by_cases h26 : u.val < 681
        ·
          by_cases h24 : u.val < 633
          ·
            by_cases h23 : u.val < 613
            ·
              have hb : u.val-582 < 31 := by omega
              have he : u.val-582+582 = u.val := by omega
              have hp := merge_checkB22 ⟨u.val-582,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-613 < 20 := by omega
              have he : u.val-613+613 = u.val := by omega
              have hp := merge_checkB23 ⟨u.val-613,hb⟩
              simpa only [he] using hp
          ·
            by_cases h25 : u.val < 652
            ·
              have hb : u.val-633 < 19 := by omega
              have he : u.val-633+633 = u.val := by omega
              have hp := merge_checkB24 ⟨u.val-633,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-652 < 29 := by omega
              have he : u.val-652+652 = u.val := by omega
              have hp := merge_checkB25 ⟨u.val-652,hb⟩
              simpa only [he] using hp
        ·
          by_cases h28 : u.val < 715
          ·
            by_cases h27 : u.val < 699
            ·
              have hb : u.val-681 < 18 := by omega
              have he : u.val-681+681 = u.val := by omega
              have hp := merge_checkB26 ⟨u.val-681,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-699 < 16 := by omega
              have he : u.val-699+699 = u.val := by omega
              have hp := merge_checkB27 ⟨u.val-699,hb⟩
              simpa only [he] using hp
          ·
            by_cases h29 : u.val < 731
            ·
              have hb : u.val-715 < 16 := by omega
              have he : u.val-715+715 = u.val := by omega
              have hp := merge_checkB28 ⟨u.val-715,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-731 < 12 := by omega
              have he : u.val-731+731 = u.val := by omega
              have hp := merge_checkB29 ⟨u.val-731,hb⟩
              simpa only [he] using hp
  ·
    by_cases h45 : u.val < 937
    ·
      by_cases h37 : u.val < 846
      ·
        by_cases h33 : u.val < 767
        ·
          by_cases h31 : u.val < 753
          ·
            have hb : u.val-743 < 10 := by omega
            have he : u.val-743+743 = u.val := by omega
            have hp := merge_checkB30 ⟨u.val-743,hb⟩
            simpa only [he] using hp
          ·
            by_cases h32 : u.val < 762
            ·
              have hb : u.val-753 < 9 := by omega
              have he : u.val-753+753 = u.val := by omega
              have hp := merge_checkB31 ⟨u.val-753,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-762 < 5 := by omega
              have he : u.val-762+762 = u.val := by omega
              have hp := merge_checkB32 ⟨u.val-762,hb⟩
              simpa only [he] using hp
        ·
          by_cases h35 : u.val < 815
          ·
            by_cases h34 : u.val < 791
            ·
              have hb : u.val-767 < 24 := by omega
              have he : u.val-767+767 = u.val := by omega
              have hp := merge_checkB33 ⟨u.val-767,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-791 < 24 := by omega
              have he : u.val-791+791 = u.val := by omega
              have hp := merge_checkB34 ⟨u.val-791,hb⟩
              simpa only [he] using hp
          ·
            by_cases h36 : u.val < 829
            ·
              have hb : u.val-815 < 14 := by omega
              have he : u.val-815+815 = u.val := by omega
              have hp := merge_checkB35 ⟨u.val-815,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-829 < 17 := by omega
              have he : u.val-829+829 = u.val := by omega
              have hp := merge_checkB36 ⟨u.val-829,hb⟩
              simpa only [he] using hp
      ·
        by_cases h41 : u.val < 891
        ·
          by_cases h39 : u.val < 873
          ·
            by_cases h38 : u.val < 861
            ·
              have hb : u.val-846 < 15 := by omega
              have he : u.val-846+846 = u.val := by omega
              have hp := merge_checkB37 ⟨u.val-846,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-861 < 12 := by omega
              have he : u.val-861+861 = u.val := by omega
              have hp := merge_checkB38 ⟨u.val-861,hb⟩
              simpa only [he] using hp
          ·
            by_cases h40 : u.val < 883
            ·
              have hb : u.val-873 < 10 := by omega
              have he : u.val-873+873 = u.val := by omega
              have hp := merge_checkB39 ⟨u.val-873,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-883 < 8 := by omega
              have he : u.val-883+883 = u.val := by omega
              have hp := merge_checkB40 ⟨u.val-883,hb⟩
              simpa only [he] using hp
        ·
          by_cases h43 : u.val < 910
          ·
            by_cases h42 : u.val < 895
            ·
              have hb : u.val-891 < 4 := by omega
              have he : u.val-891+891 = u.val := by omega
              have hp := merge_checkB41 ⟨u.val-891,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-895 < 15 := by omega
              have he : u.val-895+895 = u.val := by omega
              have hp := merge_checkB42 ⟨u.val-895,hb⟩
              simpa only [he] using hp
          ·
            by_cases h44 : u.val < 925
            ·
              have hb : u.val-910 < 15 := by omega
              have he : u.val-910+910 = u.val := by omega
              have hp := merge_checkB43 ⟨u.val-910,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-925 < 12 := by omega
              have he : u.val-925+925 = u.val := by omega
              have hp := merge_checkB44 ⟨u.val-925,hb⟩
              simpa only [he] using hp
    ·
      by_cases h53 : u.val < 998
      ·
        by_cases h49 : u.val < 969
        ·
          by_cases h47 : u.val < 955
          ·
            by_cases h46 : u.val < 947
            ·
              have hb : u.val-937 < 10 := by omega
              have he : u.val-937+937 = u.val := by omega
              have hp := merge_checkB45 ⟨u.val-937,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-947 < 8 := by omega
              have he : u.val-947+947 = u.val := by omega
              have hp := merge_checkB46 ⟨u.val-947,hb⟩
              simpa only [he] using hp
          ·
            by_cases h48 : u.val < 959
            ·
              have hb : u.val-955 < 4 := by omega
              have he : u.val-955+955 = u.val := by omega
              have hp := merge_checkB47 ⟨u.val-955,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-959 < 10 := by omega
              have he : u.val-959+959 = u.val := by omega
              have hp := merge_checkB48 ⟨u.val-959,hb⟩
              simpa only [he] using hp
        ·
          by_cases h51 : u.val < 987
          ·
            by_cases h50 : u.val < 979
            ·
              have hb : u.val-969 < 10 := by omega
              have he : u.val-969+969 = u.val := by omega
              have hp := merge_checkB49 ⟨u.val-969,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-979 < 8 := by omega
              have he : u.val-979+979 = u.val := by omega
              have hp := merge_checkB50 ⟨u.val-979,hb⟩
              simpa only [he] using hp
          ·
            by_cases h52 : u.val < 991
            ·
              have hb : u.val-987 < 4 := by omega
              have he : u.val-987+987 = u.val := by omega
              have hp := merge_checkB51 ⟨u.val-987,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-991 < 7 := by omega
              have he : u.val-991+991 = u.val := by omega
              have hp := merge_checkB52 ⟨u.val-991,hb⟩
              simpa only [he] using hp
      ·
        by_cases h57 : u.val < 1015
        ·
          by_cases h55 : u.val < 1007
          ·
            by_cases h54 : u.val < 1004
            ·
              have hb : u.val-998 < 6 := by omega
              have he : u.val-998+998 = u.val := by omega
              have hp := merge_checkB53 ⟨u.val-998,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-1004 < 3 := by omega
              have he : u.val-1004+1004 = u.val := by omega
              have hp := merge_checkB54 ⟨u.val-1004,hb⟩
              simpa only [he] using hp
          ·
            by_cases h56 : u.val < 1011
            ·
              have hb : u.val-1007 < 4 := by omega
              have he : u.val-1007+1007 = u.val := by omega
              have hp := merge_checkB55 ⟨u.val-1007,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-1011 < 4 := by omega
              have he : u.val-1011+1011 = u.val := by omega
              have hp := merge_checkB56 ⟨u.val-1011,hb⟩
              simpa only [he] using hp
        ·
          by_cases h59 : u.val < 1021
          ·
            by_cases h58 : u.val < 1018
            ·
              have hb : u.val-1015 < 3 := by omega
              have he : u.val-1015+1015 = u.val := by omega
              have hp := merge_checkB57 ⟨u.val-1015,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-1018 < 3 := by omega
              have he : u.val-1018+1018 = u.val := by omega
              have hp := merge_checkB58 ⟨u.val-1018,hb⟩
              simpa only [he] using hp
          ·
            by_cases h60 : u.val < 1023
            ·
              have hb : u.val-1021 < 2 := by omega
              have he : u.val-1021+1021 = u.val := by omega
              have hp := merge_checkB59 ⟨u.val-1021,hb⟩
              simpa only [he] using hp
            ·
              have hb : u.val-1023 < 1 := by omega
              have he : u.val-1023+1023 = u.val := by omega
              have hp := merge_checkB60 ⟨u.val-1023,hb⟩
              simpa only [he] using hp
end R9_5_0
