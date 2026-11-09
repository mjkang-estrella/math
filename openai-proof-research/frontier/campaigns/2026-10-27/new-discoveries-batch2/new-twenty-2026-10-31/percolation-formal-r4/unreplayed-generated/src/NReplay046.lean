import NReplay045
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_49913 : CNF.NClause := [(105,true),(37,false),(41,false)]
theorem der_49913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49913 :=
  CNF.rup_sound cl_49913 [cl_39402,cl_37492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39402 v h) (hints_cons _ _ _ (der_37492 v h) (by intro d hd; cases hd)))
def cl_49914 : CNF.NClause := [(40,false),(42,false),(100,true)]
theorem der_49914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49914 :=
  CNF.rup_sound cl_49914 [cl_38272,cl_49898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38272 v h) (hints_cons _ _ _ (der_49898 v h) (by intro d hd; cases hd)))
def cl_49915 : CNF.NClause := [(41,false),(53,false),(106,true)]
theorem der_49915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49915 :=
  CNF.rup_sound cl_49915 [cl_39728,cl_42819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39728 v h) (hints_cons _ _ _ (der_42819 v h) (by intro d hd; cases hd)))
def cl_49916 : CNF.NClause := [(50,false),(105,true),(33,false)]
theorem der_49916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49916 :=
  CNF.rup_sound cl_49916 [cl_40803,cl_37492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40803 v h) (hints_cons _ _ _ (der_37492 v h) (by intro d hd; cases hd)))
def cl_49917 : CNF.NClause := [(105,true),(50,false),(41,false)]
theorem der_49917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49917 :=
  CNF.rup_sound cl_49917 [cl_40447,cl_49913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40447 v h) (hints_cons _ _ _ (der_49913 v h) (by intro d hd; cases hd)))
def cl_49918 : CNF.NClause := [(74,true),(19,false),(23,false)]
theorem der_49918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49918 :=
  CNF.rup_sound cl_49918 [cl_43457,cl_44863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43457 v h) (hints_cons _ _ _ (der_44863 v h) (by intro d hd; cases hd)))
def cl_49920 : CNF.NClause := [(90,true),(8,false),(28,false)]
theorem der_49920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49920 :=
  CNF.rup_sound cl_49920 [cl_43624,cl_49801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43624 v h) (hints_cons _ _ _ (der_49801 v h) (by intro d hd; cases hd)))
def cl_49921 : CNF.NClause := [(35,false),(109,true),(58,false)]
theorem der_49921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49921 :=
  CNF.rup_sound cl_49921 [cl_43482,cl_43179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43482 v h) (hints_cons _ _ _ (der_43179 v h) (by intro d hd; cases hd)))
def cl_49922 : CNF.NClause := [(91,true),(12,false),(26,false)]
theorem der_49922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49922 :=
  CNF.rup_sound cl_49922 [cl_41213,cl_37342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41213 v h) (hints_cons _ _ _ (der_37342 v h) (by intro d hd; cases hd)))
def cl_49923 : CNF.NClause := [(73,true),(28,false),(4,false)]
theorem der_49923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49923 :=
  CNF.rup_sound cl_49923 [cl_42869,cl_29805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42869 v h) (hints_cons _ _ _ (der_29805 v h) (by intro d hd; cases hd)))
def cl_49924 : CNF.NClause := [(111,true),(38,false),(46,false)]
theorem der_49924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49924 :=
  CNF.rup_sound cl_49924 [cl_43651,cl_42523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43651 v h) (hints_cons _ _ _ (der_42523 v h) (by intro d hd; cases hd)))
def cl_49926 : CNF.NClause := [(99,true),(47,false),(35,false)]
theorem der_49926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49926 :=
  CNF.rup_sound cl_49926 [cl_43500,cl_43000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43500 v h) (hints_cons _ _ _ (der_43000 v h) (by intro d hd; cases hd)))
def cl_49927 : CNF.NClause := [(29,false),(86,true),(1,false)]
theorem der_49927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49927 :=
  CNF.rup_sound cl_49927 [cl_48867,cl_43068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48867 v h) (hints_cons _ _ _ (der_43068 v h) (by intro d hd; cases hd)))
def cl_49928 : CNF.NClause := [(116,true),(52,false),(58,false)]
theorem der_49928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49928 :=
  CNF.rup_sound cl_49928 [cl_43862,cl_42810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43862 v h) (hints_cons _ _ _ (der_42810 v h) (by intro d hd; cases hd)))
def cl_49930 : CNF.NClause := [(110,true),(46,false),(33,false)]
theorem der_49930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49930 :=
  CNF.rup_sound cl_49930 [cl_43917,cl_42648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43917 v h) (hints_cons _ _ _ (der_42648 v h) (by intro d hd; cases hd)))
def cl_49931 : CNF.NClause := [(50,false),(105,true),(54,false)]
theorem der_49931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49931 :=
  CNF.rup_sound cl_49931 [cl_43463,cl_49917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43463 v h) (hints_cons _ _ _ (der_49917 v h) (by intro d hd; cases hd)))
def cl_49932 : CNF.NClause := [(40,false),(100,true),(49,false)]
theorem der_49932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49932 :=
  CNF.rup_sound cl_49932 [cl_42469,cl_49914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42469 v h) (hints_cons _ _ _ (der_49914 v h) (by intro d hd; cases hd)))
def cl_49933 : CNF.NClause := [(40,false),(100,true),(58,false)]
theorem der_49933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49933 :=
  CNF.rup_sound cl_49933 [cl_42513,cl_42477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42513 v h) (hints_cons _ _ _ (der_42477 v h) (by intro d hd; cases hd)))
def cl_49934 : CNF.NClause := [(100,true),(58,false),(42,false)]
theorem der_49934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49934 :=
  CNF.rup_sound cl_49934 [cl_43524,cl_49898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43524 v h) (hints_cons _ _ _ (der_49898 v h) (by intro d hd; cases hd)))
def cl_49935 : CNF.NClause := [(110,true),(46,false),(45,false)]
theorem der_49935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49935 :=
  CNF.rup_sound cl_49935 [cl_42533,cl_42462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42533 v h) (hints_cons _ _ _ (der_42462 v h) (by intro d hd; cases hd)))
def cl_49936 : CNF.NClause := [(79,true),(26,false),(15,false)]
theorem der_49936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49936 :=
  CNF.rup_sound cl_49936 [cl_42752,cl_42466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42752 v h) (hints_cons _ _ _ (der_42466 v h) (by intro d hd; cases hd)))
def cl_49938 : CNF.NClause := [(84,true),(13,false),(28,false)]
theorem der_49938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49938 :=
  CNF.rup_sound cl_49938 [cl_42976,cl_48778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42976 v h) (hints_cons _ _ _ (der_48778 v h) (by intro d hd; cases hd)))
def cl_49939 : CNF.NClause := [(59,false),(112,true),(54,false)]
theorem der_49939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49939 :=
  CNF.rup_sound cl_49939 [cl_43458,cl_43031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43458 v h) (hints_cons _ _ _ (der_43031 v h) (by intro d hd; cases hd)))
def cl_49940 : CNF.NClause := [(112,true),(59,false),(46,false)]
theorem der_49940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49940 :=
  CNF.rup_sound cl_49940 [cl_43030,cl_42453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43030 v h) (hints_cons _ _ _ (der_42453 v h) (by intro d hd; cases hd)))
def cl_49943 : CNF.NClause := [(58,false),(53,false),(109,true)]
theorem der_49943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49943 :=
  CNF.rup_sound cl_49943 [cl_43257,cl_43179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43257 v h) (hints_cons _ _ _ (der_43179 v h) (by intro d hd; cases hd)))
def cl_49945 : CNF.NClause := [(66,true),(16,false),(6,false)]
theorem der_49945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49945 :=
  CNF.rup_sound cl_49945 [cl_43346,cl_49804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43346 v h) (hints_cons _ _ _ (der_49804 v h) (by intro d hd; cases hd)))
def cl_49946 : CNF.NClause := [(7,false),(82,true),(5,false)]
theorem der_49946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49946 :=
  CNF.rup_sound cl_49946 [cl_42933,cl_49774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42933 v h) (hints_cons _ _ _ (der_49774 v h) (by intro d hd; cases hd)))
def cl_49947 : CNF.NClause := [(66,true),(6,false),(21,false)]
theorem der_49947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49947 :=
  CNF.rup_sound cl_49947 [cl_43182,cl_48502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43182 v h) (hints_cons _ _ _ (der_48502 v h) (by intro d hd; cases hd)))
def cl_49949 : CNF.NClause := [(75,true),(26,false),(3,false)]
theorem der_49949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49949 :=
  CNF.rup_sound cl_49949 [cl_47123,cl_44586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47123 v h) (hints_cons _ _ _ (der_44586 v h) (by intro d hd; cases hd)))
def cl_49950 : CNF.NClause := [(101,true),(37,false),(51,false)]
theorem der_49950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49950 :=
  CNF.rup_sound cl_49950 [cl_46744,cl_49845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46744 v h) (hints_cons _ _ _ (der_49845 v h) (by intro d hd; cases hd)))
def cl_49951 : CNF.NClause := [(112,true),(43,false),(46,false)]
theorem der_49951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49951 :=
  CNF.rup_sound cl_49951 [cl_44903,cl_42453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44903 v h) (hints_cons _ _ _ (der_42453 v h) (by intro d hd; cases hd)))
def cl_49952 : CNF.NClause := [(29,false),(74,true),(23,false)]
theorem der_49952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49952 :=
  CNF.rup_sound cl_49952 [cl_44556,cl_42451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44556 v h) (hints_cons _ _ _ (der_42451 v h) (by intro d hd; cases hd)))
def cl_49953 : CNF.NClause := [(19,false),(74,true),(23,false)]
theorem der_49953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49953 :=
  CNF.rup_sound cl_49953 [cl_44688,cl_42451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44688 v h) (hints_cons _ _ _ (der_42451 v h) (by intro d hd; cases hd)))
def cl_49954 : CNF.NClause := [(116,true),(52,false),(34,false)]
theorem der_49954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49954 :=
  CNF.rup_sound cl_49954 [cl_46638,cl_42810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46638 v h) (hints_cons _ _ _ (der_42810 v h) (by intro d hd; cases hd)))
def cl_49955 : CNF.NClause := [(43,false),(34,false),(116,true)]
theorem der_49955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49955 :=
  CNF.rup_sound cl_49955 [cl_46677,cl_42810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46677 v h) (hints_cons _ _ _ (der_42810 v h) (by intro d hd; cases hd)))
def cl_49956 : CNF.NClause := [(116,true),(34,false),(43,false)]
theorem der_49956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49956 :=
  CNF.rup_sound cl_49956 [cl_46250,cl_49954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46250 v h) (hints_cons _ _ _ (der_49954 v h) (by intro d hd; cases hd)))
def cl_49957 : CNF.NClause := [(58,false),(109,true),(44,false)]
theorem der_49957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49957 :=
  CNF.rup_sound cl_49957 [cl_45332,cl_49164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45332 v h) (hints_cons _ _ _ (der_49164 v h) (by intro d hd; cases hd)))
def cl_49958 : CNF.NClause := [(101,true),(59,false),(51,false)]
theorem der_49958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49958 :=
  CNF.rup_sound cl_49958 [cl_44358,cl_42870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44358 v h) (hints_cons _ _ _ (der_42870 v h) (by intro d hd; cases hd)))
def cl_49960 : CNF.NClause := [(73,true),(4,false),(18,false)]
theorem der_49960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49960 :=
  CNF.rup_sound cl_49960 [cl_44540,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44540 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_49961 : CNF.NClause := [(130,false),(82,true),(9,true)]
theorem der_49961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49961 :=
  CNF.rup_sound cl_49961 [cl_45014,cl_45060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45014 v h) (hints_cons _ _ _ (der_45060 v h) (by intro d hd; cases hd)))
def cl_49962 : CNF.NClause := [(40,false),(51,false),(100,true)]
theorem der_49962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49962 :=
  CNF.rup_sound cl_49962 [cl_46234,cl_49932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46234 v h) (hints_cons _ _ _ (der_49932 v h) (by intro d hd; cases hd)))
def cl_49963 : CNF.NClause := [(111,true),(46,false),(55,false)]
theorem der_49963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49963 :=
  CNF.rup_sound cl_49963 [cl_44187,cl_37447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44187 v h) (hints_cons _ _ _ (der_37447 v h) (by intro d hd; cases hd)))
def cl_49964 : CNF.NClause := [(59,false),(55,false),(115,true)]
theorem der_49964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49964 :=
  CNF.rup_sound cl_49964 [cl_43978,cl_36883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43978 v h) (hints_cons _ _ _ (der_36883 v h) (by intro d hd; cases hd)))
def cl_49965 : CNF.NClause := [(8,false),(79,true),(15,false)]
theorem der_49965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49965 :=
  CNF.rup_sound cl_49965 [cl_44547,cl_42539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44547 v h) (hints_cons _ _ _ (der_42539 v h) (by intro d hd; cases hd)))
def cl_49966 : CNF.NClause := [(79,true),(2,false),(15,false)]
theorem der_49966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49966 :=
  CNF.rup_sound cl_49966 [cl_45354,cl_42539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45354 v h) (hints_cons _ _ _ (der_42539 v h) (by intro d hd; cases hd)))
def cl_49967 : CNF.NClause := [(73,true),(4,false),(21,false)]
theorem der_49967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49967 :=
  CNF.rup_sound cl_49967 [cl_44582,cl_49923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44582 v h) (hints_cons _ _ _ (der_49923 v h) (by intro d hd; cases hd)))
def cl_49968 : CNF.NClause := [(29,false),(14,false),(86,true)]
theorem der_49968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49968 :=
  CNF.rup_sound cl_49968 [cl_44236,cl_42713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44236 v h) (hints_cons _ _ _ (der_42713 v h) (by intro d hd; cases hd)))
def cl_49969 : CNF.NClause := [(111,true),(34,false),(55,false)]
theorem der_49969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49969 :=
  CNF.rup_sound cl_49969 [cl_45112,cl_42523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45112 v h) (hints_cons _ _ _ (der_42523 v h) (by intro d hd; cases hd)))
def cl_49970 : CNF.NClause := [(111,true),(55,false),(46,false)]
theorem der_49970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49970 :=
  CNF.rup_sound cl_49970 [cl_46448,cl_42523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46448 v h) (hints_cons _ _ _ (der_42523 v h) (by intro d hd; cases hd)))
def cl_49971 : CNF.NClause := [(64,true),(17,false),(141,false)]
theorem der_49971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49971 :=
  CNF.rup_sound cl_49971 [cl_44758,cl_49763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44758 v h) (hints_cons _ _ _ (der_49763 v h) (by intro d hd; cases hd)))
def cl_49972 : CNF.NClause := [(75,true),(3,false),(16,false)]
theorem der_49972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49972 :=
  CNF.rup_sound cl_49972 [cl_45066,cl_44586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45066 v h) (hints_cons _ _ _ (der_44586 v h) (by intro d hd; cases hd)))
def cl_49973 : CNF.NClause := [(24,false),(84,true),(13,false)]
theorem der_49973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49973 :=
  CNF.rup_sound cl_49973 [cl_46584,cl_49938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46584 v h) (hints_cons _ _ _ (der_49938 v h) (by intro d hd; cases hd)))
def cl_49974 : CNF.NClause := [(12,false),(91,true),(24,false)]
theorem der_49974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49974 :=
  CNF.rup_sound cl_49974 [cl_44013,cl_37342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44013 v h) (hints_cons _ _ _ (der_37342 v h) (by intro d hd; cases hd)))
def cl_49975 : CNF.NClause := [(60,false),(99,true),(35,false)]
theorem der_49975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49975 :=
  CNF.rup_sound cl_49975 [cl_44282,cl_42999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44282 v h) (hints_cons _ _ _ (der_42999 v h) (by intro d hd; cases hd)))
def cl_49976 : CNF.NClause := [(39,false),(99,true),(47,false)]
theorem der_49976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49976 :=
  CNF.rup_sound cl_49976 [cl_47062,cl_47215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47062 v h) (hints_cons _ _ _ (der_47215 v h) (by intro d hd; cases hd)))
def cl_49977 : CNF.NClause := [(104,true),(59,false),(35,false)]
theorem der_49977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49977 :=
  CNF.rup_sound cl_49977 [cl_43975,cl_49912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43975 v h) (hints_cons _ _ _ (der_49912 v h) (by intro d hd; cases hd)))
def cl_49978 : CNF.NClause := [(100,true),(42,false),(51,false)]
theorem der_49978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49978 :=
  CNF.rup_sound cl_49978 [cl_44790,cl_49863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44790 v h) (hints_cons _ _ _ (der_49863 v h) (by intro d hd; cases hd)))
def cl_49979 : CNF.NClause := [(16,false),(84,true),(13,false)]
theorem der_49979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49979 :=
  CNF.rup_sound cl_49979 [cl_47268,cl_42738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47268 v h) (hints_cons _ _ _ (der_42738 v h) (by intro d hd; cases hd)))
def cl_49980 : CNF.NClause := [(116,true),(36,false),(34,false)]
theorem der_49980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49980 :=
  CNF.rup_sound cl_49980 [cl_47280,cl_49954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47280 v h) (hints_cons _ _ _ (der_49954 v h) (by intro d hd; cases hd)))
def cl_49981 : CNF.NClause := [(116,true),(36,false),(34,false)]
theorem der_49981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49981 :=
  CNF.rup_sound cl_49981 [cl_47368,cl_42810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47368 v h) (hints_cons _ _ _ (der_42810 v h) (by intro d hd; cases hd)))
def cl_49982 : CNF.NClause := [(29,false),(86,true),(5,false)]
theorem der_49982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49982 :=
  CNF.rup_sound cl_49982 [cl_47416,cl_43136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47416 v h) (hints_cons _ _ _ (der_43136 v h) (by intro d hd; cases hd)))
def cl_49983 : CNF.NClause := [(114,true),(36,false),(54,false)]
theorem der_49983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49983 :=
  CNF.rup_sound cl_49983 [cl_47466,cl_42767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47466 v h) (hints_cons _ _ _ (der_42767 v h) (by intro d hd; cases hd)))
def cl_49984 : CNF.NClause := [(60,false),(105,true),(54,false)]
theorem der_49984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49984 :=
  CNF.rup_sound cl_49984 [cl_47510,cl_43905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47510 v h) (hints_cons _ _ _ (der_43905 v h) (by intro d hd; cases hd)))
def cl_49986 : CNF.NClause := [(66,true),(6,false),(130,false)]
theorem der_49986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49986 :=
  CNF.rup_sound cl_49986 [cl_47656,cl_43827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47656 v h) (hints_cons _ _ _ (der_43827 v h) (by intro d hd; cases hd)))
def cl_49987 : CNF.NClause := [(73,true),(4,false),(903,false)]
theorem der_49987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49987 :=
  CNF.rup_sound cl_49987 [cl_48366,cl_49923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48366 v h) (hints_cons _ _ _ (der_49923 v h) (by intro d hd; cases hd)))
def cl_49988 : CNF.NClause := [(79,true),(15,false),(26,false)]
theorem der_49988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49988 :=
  CNF.rup_sound cl_49988 [cl_48458,cl_42539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48458 v h) (hints_cons _ _ _ (der_42539 v h) (by intro d hd; cases hd)))
def cl_49989 : CNF.NClause := [(4,false),(12,false),(68,true)]
theorem der_49989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49989 :=
  CNF.rup_sound cl_49989 [cl_48599,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48599 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd)))
def cl_49990 : CNF.NClause := [(68,true),(4,false),(128,false)]
theorem der_49990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49990 :=
  CNF.rup_sound cl_49990 [cl_48673,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48673 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd)))
def cl_49991 : CNF.NClause := [(73,true),(4,false),(128,false)]
theorem der_49991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49991 :=
  CNF.rup_sound cl_49991 [cl_48773,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48773 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_49992 : CNF.NClause := [(70,true),(6,false),(1060,false)]
theorem der_49992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49992 :=
  CNF.rup_sound cl_49992 [cl_48813,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48813 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_49993 : CNF.NClause := [(87,true),(2,false),(1056,true)]
theorem der_49993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49993 :=
  CNF.rup_sound cl_49993 [cl_48866,cl_49790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48866 v h) (hints_cons _ _ _ (der_49790 v h) (by intro d hd; cases hd)))
def cl_49994 : CNF.NClause := [(1055,false),(86,true),(1,false)]
theorem der_49994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49994 :=
  CNF.rup_sound cl_49994 [cl_48878,cl_43068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48878 v h) (hints_cons _ _ _ (der_43068 v h) (by intro d hd; cases hd)))
def cl_49995 : CNF.NClause := [(79,true),(2,false),(69,true)]
theorem der_49995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49995 :=
  CNF.rup_sound cl_49995 [cl_48988,cl_49966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48988 v h) (hints_cons _ _ _ (der_49966 v h) (by intro d hd; cases hd)))
def cl_49996 : CNF.NClause := [(37,false),(44,false),(109,true)]
theorem der_49996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49996 :=
  CNF.rup_sound cl_49996 [cl_49007,cl_49725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49007 v h) (hints_cons _ _ _ (der_49725 v h) (by intro d hd; cases hd)))
def cl_49997 : CNF.NClause := [(125,false),(1,false),(66,true)]
theorem der_49997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49997 :=
  CNF.rup_sound cl_49997 [cl_49055,cl_49800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49055 v h) (hints_cons _ _ _ (der_49800 v h) (by intro d hd; cases hd)))
def cl_49998 : CNF.NClause := [(19,false),(22,false),(90,true)]
theorem der_49998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49998 :=
  CNF.rup_sound cl_49998 [cl_49137,cl_49821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49137 v h) (hints_cons _ _ _ (der_49821 v h) (by intro d hd; cases hd)))
def cl_49999 : CNF.NClause := [(14,false),(24,false),(63,true)]
theorem der_49999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_49999 :=
  CNF.rup_sound cl_49999 [cl_49235,cl_42527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49235 v h) (hints_cons _ _ _ (der_42527 v h) (by intro d hd; cases hd)))
def cl_50000 : CNF.NClause := [(89,true),(14,false),(138,true)]
theorem der_50000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50000 :=
  CNF.rup_sound cl_50000 [cl_49291,cl_37439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49291 v h) (hints_cons _ _ _ (der_37439 v h) (by intro d hd; cases hd)))
def cl_50001 : CNF.NClause := [(81,true),(1,false),(15,false)]
theorem der_50001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50001 :=
  CNF.rup_sound cl_50001 [cl_49311,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49311 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_50002 : CNF.NClause := [(101,true),(45,false),(48,false)]
theorem der_50002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50002 :=
  CNF.rup_sound cl_50002 [cl_49439,cl_42866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49439 v h) (hints_cons _ _ _ (der_42866 v h) (by intro d hd; cases hd)))
def cl_50003 : CNF.NClause := [(55,false),(44,false),(115,true)]
theorem der_50003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50003 :=
  CNF.rup_sound cl_50003 [cl_49445,cl_36883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49445 v h) (hints_cons _ _ _ (der_36883 v h) (by intro d hd; cases hd)))
def cl_50005 : CNF.NClause := [(29,false),(18,false),(86,true)]
theorem der_50005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50005 :=
  CNF.rup_sound cl_50005 [cl_49537,cl_49789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49537 v h) (hints_cons _ _ _ (der_49789 v h) (by intro d hd; cases hd)))
def cl_50006 : CNF.NClause := [(81,true),(12,false),(15,false)]
theorem der_50006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50006 :=
  CNF.rup_sound cl_50006 [cl_49542,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49542 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_50008 : CNF.NClause := [(23,false),(15,false),(81,true)]
theorem der_50008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50008 :=
  CNF.rup_sound cl_50008 [cl_49551,cl_50006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49551 v h) (hints_cons _ _ _ (der_50006 v h) (by intro d hd; cases hd)))
def cl_50009 : CNF.NClause := [(12,false),(68,true),(20,false)]
theorem der_50009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50009 :=
  CNF.rup_sound cl_50009 [cl_49552,cl_49989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49552 v h) (hints_cons _ _ _ (der_49989 v h) (by intro d hd; cases hd)))
def cl_50010 : CNF.NClause := [(7,false),(73,true),(21,false)]
theorem der_50010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50010 :=
  CNF.rup_sound cl_50010 [cl_49553,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49553 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_50011 : CNF.NClause := [(27,false),(69,true),(11,false)]
theorem der_50011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50011 :=
  CNF.rup_sound cl_50011 [cl_49556,cl_47172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49556 v h) (hints_cons _ _ _ (der_47172 v h) (by intro d hd; cases hd)))
def cl_50012 : CNF.NClause := [(75,true),(26,false),(9,false)]
theorem der_50012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50012 :=
  CNF.rup_sound cl_50012 [cl_49559,cl_49815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49559 v h) (hints_cons _ _ _ (der_49815 v h) (by intro d hd; cases hd)))
def cl_50015 : CNF.NClause := [(121,true),(42,false),(53,false)]
theorem der_50015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50015 :=
  CNF.rup_sound cl_50015 [cl_49573,cl_47827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49573 v h) (hints_cons _ _ _ (der_47827 v h) (by intro d hd; cases hd)))
def cl_50016 : CNF.NClause := [(105,true),(54,false),(41,false)]
theorem der_50016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50016 :=
  CNF.rup_sound cl_50016 [cl_49574,cl_37492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49574 v h) (hints_cons _ _ _ (der_37492 v h) (by intro d hd; cases hd)))
def cl_50017 : CNF.NClause := [(41,false),(34,false),(106,true)]
theorem der_50017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50017 :=
  CNF.rup_sound cl_50017 [cl_49575,cl_49893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49575 v h) (hints_cons _ _ _ (der_49893 v h) (by intro d hd; cases hd)))
def cl_50020 : CNF.NClause := [(60,false),(99,true),(35,false)]
theorem der_50020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50020 :=
  CNF.rup_sound cl_50020 [cl_49579,cl_49881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49579 v h) (hints_cons _ _ _ (der_49881 v h) (by intro d hd; cases hd)))
def cl_50021 : CNF.NClause := [(99,true),(47,false),(35,false)]
theorem der_50021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50021 :=
  CNF.rup_sound cl_50021 [cl_49580,cl_47014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49580 v h) (hints_cons _ _ _ (der_47014 v h) (by intro d hd; cases hd)))
def cl_50022 : CNF.NClause := [(104,true),(35,false),(49,false)]
theorem der_50022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50022 :=
  CNF.rup_sound cl_50022 [cl_49582,cl_49768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49582 v h) (hints_cons _ _ _ (der_49768 v h) (by intro d hd; cases hd)))
def cl_50024 : CNF.NClause := [(114,true),(48,false),(36,false)]
theorem der_50024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50024 :=
  CNF.rup_sound cl_50024 [cl_49586,cl_38487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49586 v h) (hints_cons _ _ _ (der_38487 v h) (by intro d hd; cases hd)))
def cl_50025 : CNF.NClause := [(98,true),(61,false),(54,false)]
theorem der_50025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50025 :=
  CNF.rup_sound cl_50025 [cl_49592,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49592 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50026 : CNF.NClause := [(105,true),(54,false),(37,false)]
theorem der_50026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50026 :=
  CNF.rup_sound cl_50026 [cl_49595,cl_49913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49595 v h) (hints_cons _ _ _ (der_49913 v h) (by intro d hd; cases hd)))
def cl_50027 : CNF.NClause := [(101,true),(45,false),(51,false)]
theorem der_50027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50027 :=
  CNF.rup_sound cl_50027 [cl_49597,cl_49892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49597 v h) (hints_cons _ _ _ (der_49892 v h) (by intro d hd; cases hd)))
def cl_50028 : CNF.NClause := [(61,false),(60,false),(93,true)]
theorem der_50028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50028 :=
  CNF.rup_sound cl_50028 [cl_49598,cl_49523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49598 v h) (hints_cons _ _ _ (der_49523 v h) (by intro d hd; cases hd)))
def cl_50029 : CNF.NClause := [(93,true),(61,false),(57,false)]
theorem der_50029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50029 :=
  CNF.rup_sound cl_50029 [cl_49602,cl_49524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49602 v h) (hints_cons _ _ _ (der_49524 v h) (by intro d hd; cases hd)))
def cl_50031 : CNF.NClause := [(117,true),(45,false),(32,false)]
theorem der_50031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50031 :=
  CNF.rup_sound cl_50031 [cl_49620,cl_49525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49620 v h) (hints_cons _ _ _ (der_49525 v h) (by intro d hd; cases hd)))
def cl_50032 : CNF.NClause := [(116,true),(52,false),(34,false)]
theorem der_50032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50032 :=
  CNF.rup_sound cl_50032 [cl_49621,cl_49956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49621 v h) (hints_cons _ _ _ (der_49956 v h) (by intro d hd; cases hd)))
def cl_50033 : CNF.NClause := [(59,false),(101,true),(34,false)]
theorem der_50033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50033 :=
  CNF.rup_sound cl_50033 [cl_49622,cl_43208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49622 v h) (hints_cons _ _ _ (der_43208 v h) (by intro d hd; cases hd)))
def cl_50034 : CNF.NClause := [(116,true),(58,false),(52,false)]
theorem der_50034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50034 :=
  CNF.rup_sound cl_50034 [cl_49623,cl_47407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49623 v h) (hints_cons _ _ _ (der_47407 v h) (by intro d hd; cases hd)))
def cl_50035 : CNF.NClause := [(116,true),(52,false),(43,false)]
theorem der_50035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50035 :=
  CNF.rup_sound cl_50035 [cl_49624,cl_49847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49624 v h) (hints_cons _ _ _ (der_49847 v h) (by intro d hd; cases hd)))
def cl_50036 : CNF.NClause := [(104,true),(38,false),(52,false)]
theorem der_50036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50036 :=
  CNF.rup_sound cl_50036 [cl_49625,cl_49860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49625 v h) (hints_cons _ _ _ (der_49860 v h) (by intro d hd; cases hd)))
def cl_50037 : CNF.NClause := [(121,true),(59,false),(39,false)]
theorem der_50037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50037 :=
  CNF.rup_sound cl_50037 [cl_49627,cl_43976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49627 v h) (hints_cons _ _ _ (der_43976 v h) (by intro d hd; cases hd)))
def cl_50040 : CNF.NClause := [(60,false),(93,true),(57,false)]
theorem der_50040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50040 :=
  CNF.rup_sound cl_50040 [cl_49631,cl_49523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49631 v h) (hints_cons _ _ _ (der_49523 v h) (by intro d hd; cases hd)))
def cl_50041 : CNF.NClause := [(60,false),(99,true),(47,false)]
theorem der_50041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50041 :=
  CNF.rup_sound cl_50041 [cl_49634,cl_49881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49634 v h) (hints_cons _ _ _ (der_49881 v h) (by intro d hd; cases hd)))
def cl_50042 : CNF.NClause := [(110,true),(33,false),(46,false)]
theorem der_50042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50042 :=
  CNF.rup_sound cl_50042 [cl_49636,cl_42630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49636 v h) (hints_cons _ _ _ (der_42630 v h) (by intro d hd; cases hd)))
def cl_50043 : CNF.NClause := [(105,true),(37,false),(33,false)]
theorem der_50043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50043 :=
  CNF.rup_sound cl_50043 [cl_49637,cl_43905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49637 v h) (hints_cons _ _ _ (der_43905 v h) (by intro d hd; cases hd)))
def cl_50044 : CNF.NClause := [(58,false),(100,true),(49,false)]
theorem der_50044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50044 :=
  CNF.rup_sound cl_50044 [cl_49640,cl_42981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49640 v h) (hints_cons _ _ _ (der_42981 v h) (by intro d hd; cases hd)))
def cl_50046 : CNF.NClause := [(99,true),(47,false),(43,false)]
theorem der_50046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50046 :=
  CNF.rup_sound cl_50046 [cl_49642,cl_49976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49642 v h) (hints_cons _ _ _ (der_49976 v h) (by intro d hd; cases hd)))
def cl_50047 : CNF.NClause := [(116,true),(36,false),(43,false)]
theorem der_50047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50047 :=
  CNF.rup_sound cl_50047 [cl_49643,cl_49956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49643 v h) (hints_cons _ _ _ (der_49956 v h) (by intro d hd; cases hd)))
def cl_50048 : CNF.NClause := [(122,true),(43,false),(49,false)]
theorem der_50048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50048 :=
  CNF.rup_sound cl_50048 [cl_49644,cl_48925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49644 v h) (hints_cons _ _ _ (der_48925 v h) (by intro d hd; cases hd)))
def cl_50049 : CNF.NClause := [(110,true),(46,false),(45,false)]
theorem der_50049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50049 :=
  CNF.rup_sound cl_50049 [cl_49646,cl_42630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49646 v h) (hints_cons _ _ _ (der_42630 v h) (by intro d hd; cases hd)))
def cl_50050 : CNF.NClause := [(123,true),(46,false),(36,false)]
theorem der_50050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50050 :=
  CNF.rup_sound cl_50050 [cl_49648,cl_40388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49648 v h) (hints_cons _ _ _ (der_40388 v h) (by intro d hd; cases hd)))
def cl_50051 : CNF.NClause := [(93,true),(59,false),(57,false)]
theorem der_50051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50051 :=
  CNF.rup_sound cl_50051 [cl_49649,cl_50029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49649 v h) (hints_cons _ _ _ (der_50029 v h) (by intro d hd; cases hd)))
def cl_50052 : CNF.NClause := [(117,true),(36,false),(45,false)]
theorem der_50052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50052 :=
  CNF.rup_sound cl_50052 [cl_49654,cl_49653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49654 v h) (hints_cons _ _ _ (der_49653 v h) (by intro d hd; cases hd)))
def cl_50053 : CNF.NClause := [(122,true),(37,false),(55,false)]
theorem der_50053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50053 :=
  CNF.rup_sound cl_50053 [cl_49655,cl_48925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49655 v h) (hints_cons _ _ _ (der_48925 v h) (by intro d hd; cases hd)))
def cl_50055 : CNF.NClause := [(115,true),(36,false),(47,false)]
theorem der_50055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50055 :=
  CNF.rup_sound cl_50055 [cl_49670,cl_49900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49670 v h) (hints_cons _ _ _ (der_49900 v h) (by intro d hd; cases hd)))
def cl_50056 : CNF.NClause := [(121,true),(31,false),(53,false)]
theorem der_50056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50056 :=
  CNF.rup_sound cl_50056 [cl_49671,cl_50015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49671 v h) (hints_cons _ _ _ (der_50015 v h) (by intro d hd; cases hd)))
def cl_50057 : CNF.NClause := [(88,false),(89,false),(31,false)]
theorem der_50057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50057 :=
  CNF.rup_sound cl_50057 [cl_49674,cl_49684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49674 v h) (hints_cons _ _ _ (der_49684 v h) (by intro d hd; cases hd)))
def cl_50059 : CNF.NClause := [(92,false),(88,true),(31,false)]
theorem der_50059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50059 :=
  CNF.rup_sound cl_50059 [cl_49676,cl_49683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49676 v h) (hints_cons _ _ _ (der_49683 v h) (by intro d hd; cases hd)))
def cl_50060 : CNF.NClause := [(22,false),(15,false),(78,true)]
theorem der_50060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50060 :=
  CNF.rup_sound cl_50060 [cl_49689,cl_49545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49689 v h) (hints_cons _ _ _ (der_49545 v h) (by intro d hd; cases hd)))
def cl_50063 : CNF.NClause := [(111,true),(55,false),(42,false)]
theorem der_50063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50063 :=
  CNF.rup_sound cl_50063 [cl_49743,cl_49963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49743 v h) (hints_cons _ _ _ (der_49963 v h) (by intro d hd; cases hd)))
def cl_50064 : CNF.NClause := [(98,true),(52,false),(53,false)]
theorem der_50064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50064 :=
  CNF.rup_sound cl_50064 [cl_49747,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49747 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50065 : CNF.NClause := [(26,false),(8,false),(79,true),(2,true)]
theorem der_50065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50065 :=
  CNF.rup_sound cl_50065 [cl_29950,cl_49988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29950 v h) (hints_cons _ _ _ (der_49988 v h) (by intro d hd; cases hd)))
def cl_50066 : CNF.NClause := [(8,false),(21,false),(79,true),(14,true)]
theorem der_50066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50066 :=
  CNF.rup_sound cl_50066 [cl_29953,cl_37816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29953 v h) (hints_cons _ _ _ (der_37816 v h) (by intro d hd; cases hd)))
def cl_50067 : CNF.NClause := [(15,true),(79,true),(14,false),(8,false)]
theorem der_50067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50067 :=
  CNF.rup_sound cl_50067 [cl_29955,cl_37816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29955 v h) (hints_cons _ _ _ (der_37816 v h) (by intro d hd; cases hd)))
def cl_50068 : CNF.NClause := [(7,false),(73,true),(21,true),(28,false)]
theorem der_50068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50068 :=
  CNF.rup_sound cl_50068 [cl_29970,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29970 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_50070 : CNF.NClause := [(73,true),(7,false),(28,true),(10,false)]
theorem der_50070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50070 :=
  CNF.rup_sound cl_50070 [cl_29976,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29976 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_50071 : CNF.NClause := [(68,true),(4,false),(8,false),(16,true)]
theorem der_50071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50071 :=
  CNF.rup_sound cl_50071 [cl_29983,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29983 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd)))
def cl_50073 : CNF.NClause := [(28,true),(11,false),(19,false),(90,true)]
theorem der_50073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50073 :=
  CNF.rup_sound cl_50073 [cl_23211,cl_49821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23211 v h) (hints_cons _ _ _ (der_49821 v h) (by intro d hd; cases hd)))
def cl_50074 : CNF.NClause := [(7,false),(16,true),(27,false),(89,true)]
theorem der_50074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50074 :=
  CNF.rup_sound cl_50074 [cl_23215,cl_37439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23215 v h) (hints_cons _ _ _ (der_37439 v h) (by intro d hd; cases hd)))
def cl_50076 : CNF.NClause := [(89,true),(16,false),(7,false),(14,true)]
theorem der_50076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50076 :=
  CNF.rup_sound cl_50076 [cl_23218,cl_49761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23218 v h) (hints_cons _ _ _ (der_49761 v h) (by intro d hd; cases hd)))
def cl_50077 : CNF.NClause := [(23,false),(27,false),(7,true),(89,true)]
theorem der_50077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50077 :=
  CNF.rup_sound cl_50077 [cl_23220,cl_49783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23220 v h) (hints_cons _ _ _ (der_49783 v h) (by intro d hd; cases hd)))
def cl_50078 : CNF.NClause := [(18,false),(65,true),(8,true),(13,false)]
theorem der_50078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50078 :=
  CNF.rup_sound cl_50078 [cl_23236,cl_49765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23236 v h) (hints_cons _ _ _ (der_49765 v h) (by intro d hd; cases hd)))
def cl_50079 : CNF.NClause := [(16,true),(84,true),(13,false),(5,false)]
theorem der_50079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50079 :=
  CNF.rup_sound cl_50079 [cl_30021,cl_43180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30021 v h) (hints_cons _ _ _ (der_43180 v h) (by intro d hd; cases hd)))
def cl_50080 : CNF.NClause := [(67,true),(22,true),(20,false),(24,false)]
theorem der_50080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50080 :=
  CNF.rup_sound cl_50080 [cl_23253,cl_49834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23253 v h) (hints_cons _ _ _ (der_49834 v h) (by intro d hd; cases hd)))
def cl_50081 : CNF.NClause := [(73,true),(4,false),(10,false),(21,true)]
theorem der_50081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50081 :=
  CNF.rup_sound cl_50081 [cl_30034,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30034 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_50082 : CNF.NClause := [(21,true),(29,false),(13,false),(88,true)]
theorem der_50082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50082 :=
  CNF.rup_sound cl_50082 [cl_30037,cl_49837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30037 v h) (hints_cons _ _ _ (der_49837 v h) (by intro d hd; cases hd)))
def cl_50083 : CNF.NClause := [(29,false),(17,false),(13,true),(88,true)]
theorem der_50083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50083 :=
  CNF.rup_sound cl_50083 [cl_30038,cl_29943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30038 v h) (hints_cons _ _ _ (der_29943 v h) (by intro d hd; cases hd)))
def cl_50085 : CNF.NClause := [(111,true),(42,true),(34,false),(60,false)]
theorem der_50085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50085 :=
  CNF.rup_sound cl_50085 [cl_30057,cl_49842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30057 v h) (hints_cons _ _ _ (der_49842 v h) (by intro d hd; cases hd)))
def cl_50086 : CNF.NClause := [(111,true),(55,true),(42,false),(34,false)]
theorem der_50086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50086 :=
  CNF.rup_sound cl_50086 [cl_30058,cl_42523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30058 v h) (hints_cons _ _ _ (der_42523 v h) (by intro d hd; cases hd)))
def cl_50087 : CNF.NClause := [(98,true),(51,false),(54,true),(52,false)]
theorem der_50087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50087 :=
  CNF.rup_sound cl_50087 [cl_30062,cl_50064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30062 v h) (hints_cons _ _ _ (der_50064 v h) (by intro d hd; cases hd)))
def cl_50088 : CNF.NClause := [(121,true),(31,true),(42,false),(59,false)]
theorem der_50088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50088 :=
  CNF.rup_sound cl_50088 [cl_30074,cl_42429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30074 v h) (hints_cons _ _ _ (der_42429 v h) (by intro d hd; cases hd)))
def cl_50089 : CNF.NClause := [(121,true),(42,false),(31,true),(39,false)]
theorem der_50089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50089 :=
  CNF.rup_sound cl_50089 [cl_30075,cl_47827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30075 v h) (hints_cons _ _ _ (der_47827 v h) (by intro d hd; cases hd)))
def cl_50091 : CNF.NClause := [(119,true),(52,false),(40,false),(31,true)]
theorem der_50091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50091 :=
  CNF.rup_sound cl_50091 [cl_42448,cl_49745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42448 v h) (hints_cons _ _ _ (der_49745 v h) (by intro d hd; cases hd)))
def cl_50092 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true)]
theorem der_50092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50092 :=
  CNF.rup_sound cl_50092 [cl_30126,cl_49619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30126 v h) (hints_cons _ _ _ (der_49619 v h) (by intro d hd; cases hd)))
def cl_50093 : CNF.NClause := [(102,true),(32,false),(38,true),(50,false)]
theorem der_50093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50093 :=
  CNF.rup_sound cl_50093 [cl_30131,cl_38847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30131 v h) (hints_cons _ _ _ (der_38847 v h) (by intro d hd; cases hd)))
def cl_50094 : CNF.NClause := [(2,false),(79,true),(8,true),(21,false)]
theorem der_50094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50094 :=
  CNF.rup_sound cl_50094 [cl_30137,cl_47967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30137 v h) (hints_cons _ _ _ (der_47967 v h) (by intro d hd; cases hd)))
def cl_50096 : CNF.NClause := [(8,true),(16,false),(68,true),(20,false)]
theorem der_50096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50096 :=
  CNF.rup_sound cl_50096 [cl_30159,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30159 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd)))
def cl_50097 : CNF.NClause := [(29,false),(2,false),(19,true),(74,true)]
theorem der_50097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50097 :=
  CNF.rup_sound cl_50097 [cl_30165,cl_42426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30165 v h) (hints_cons _ _ _ (der_42426 v h) (by intro d hd; cases hd)))
def cl_50098 : CNF.NClause := [(19,false),(2,false),(74,true),(10,true)]
theorem der_50098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50098 :=
  CNF.rup_sound cl_50098 [cl_30170,cl_42426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30170 v h) (hints_cons _ _ _ (der_42426 v h) (by intro d hd; cases hd)))
def cl_50099 : CNF.NClause := [(17,true),(3,false),(70,true),(28,false)]
theorem der_50099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50099 :=
  CNF.rup_sound cl_50099 [cl_30175,cl_49562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30175 v h) (hints_cons _ _ _ (der_49562 v h) (by intro d hd; cases hd)))
def cl_50100 : CNF.NClause := [(17,false),(70,true),(14,true),(3,false)]
theorem der_50100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50100 :=
  CNF.rup_sound cl_50100 [cl_30179,cl_49686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30179 v h) (hints_cons _ _ _ (der_49686 v h) (by intro d hd; cases hd)))
def cl_50101 : CNF.NClause := [(7,false),(82,true),(9,true),(5,false)]
theorem der_50101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50101 :=
  CNF.rup_sound cl_50101 [cl_23292,cl_49775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23292 v h) (hints_cons _ _ _ (der_49775 v h) (by intro d hd; cases hd)))
def cl_50102 : CNF.NClause := [(12,false),(6,true),(26,false),(91,true)]
theorem der_50102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50102 :=
  CNF.rup_sound cl_50102 [cl_23295,cl_49974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23295 v h) (hints_cons _ _ _ (der_49974 v h) (by intro d hd; cases hd)))
def cl_50104 : CNF.NClause := [(29,false),(10,false),(74,true),(19,true)]
theorem der_50104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50104 :=
  CNF.rup_sound cl_50104 [cl_30188,cl_41212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30188 v h) (hints_cons _ _ _ (der_41212 v h) (by intro d hd; cases hd)))
def cl_50105 : CNF.NClause := [(29,true),(74,true),(23,false),(10,false)]
theorem der_50105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50105 :=
  CNF.rup_sound cl_50105 [cl_30189,cl_44863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30189 v h) (hints_cons _ _ _ (der_44863 v h) (by intro d hd; cases hd)))
def cl_50106 : CNF.NClause := [(19,false),(29,true),(10,false),(74,true)]
theorem der_50106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50106 :=
  CNF.rup_sound cl_50106 [cl_30190,cl_41212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30190 v h) (hints_cons _ _ _ (der_41212 v h) (by intro d hd; cases hd)))
def cl_50107 : CNF.NClause := [(27,false),(22,false),(78,true),(6,true)]
theorem der_50107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50107 :=
  CNF.rup_sound cl_50107 [cl_30192,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30192 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50109 : CNF.NClause := [(18,false),(86,true),(1,false),(5,true)]
theorem der_50109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50109 :=
  CNF.rup_sound cl_50109 [cl_30204,cl_50005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30204 v h) (hints_cons _ _ _ (der_50005 v h) (by intro d hd; cases hd)))
def cl_50110 : CNF.NClause := [(2,false),(5,true),(28,false),(84,true)]
theorem der_50110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50110 :=
  CNF.rup_sound cl_50110 [cl_30210,cl_48778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30210 v h) (hints_cons _ _ _ (der_48778 v h) (by intro d hd; cases hd)))
def cl_50111 : CNF.NClause := [(24,false),(2,false),(5,true),(84,true)]
theorem der_50111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50111 :=
  CNF.rup_sound cl_50111 [cl_30213,cl_49973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30213 v h) (hints_cons _ _ _ (der_49973 v h) (by intro d hd; cases hd)))
def cl_50112 : CNF.NClause := [(16,false),(2,false),(84,true),(5,true)]
theorem der_50112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50112 :=
  CNF.rup_sound cl_50112 [cl_30215,cl_42738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30215 v h) (hints_cons _ _ _ (der_42738 v h) (by intro d hd; cases hd)))
def cl_50113 : CNF.NClause := [(85,true),(21,false),(12,true),(3,false)]
theorem der_50113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50113 :=
  CNF.rup_sound cl_50113 [cl_30220,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30220 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_50114 : CNF.NClause := [(19,false),(3,false),(12,true),(85,true)]
theorem der_50114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50114 :=
  CNF.rup_sound cl_50114 [cl_30222,cl_50113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30222 v h) (hints_cons _ _ _ (der_50113 v h) (by intro d hd; cases hd)))
def cl_50116 : CNF.NClause := [(16,false),(2,true),(84,true),(13,false)]
theorem der_50116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50116 :=
  CNF.rup_sound cl_50116 [cl_30230,cl_42738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30230 v h) (hints_cons _ _ _ (der_42738 v h) (by intro d hd; cases hd)))
def cl_50117 : CNF.NClause := [(29,false),(22,false),(86,true),(14,true)]
theorem der_50117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50117 :=
  CNF.rup_sound cl_50117 [cl_30250,cl_42488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30250 v h) (hints_cons _ _ _ (der_42488 v h) (by intro d hd; cases hd)))
def cl_50118 : CNF.NClause := [(19,false),(7,true),(13,false),(71,true)]
theorem der_50118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50118 :=
  CNF.rup_sound cl_50118 [cl_30267,cl_43349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30267 v h) (hints_cons _ _ _ (der_43349 v h) (by intro d hd; cases hd)))
def cl_50119 : CNF.NClause := [(8,true),(29,false),(68,true),(16,false)]
theorem der_50119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50119 :=
  CNF.rup_sound cl_50119 [cl_30280,cl_49530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30280 v h) (hints_cons _ _ _ (der_49530 v h) (by intro d hd; cases hd)))
def cl_50120 : CNF.NClause := [(26,false),(7,true),(13,false),(71,true)]
theorem der_50120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50120 :=
  CNF.rup_sound cl_50120 [cl_48544,cl_42754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48544 v h) (hints_cons _ _ _ (der_42754 v h) (by intro d hd; cases hd)))
def cl_50121 : CNF.NClause := [(8,false),(17,false),(76,true),(1,true)]
theorem der_50121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50121 :=
  CNF.rup_sound cl_50121 [cl_30299,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30299 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50122 : CNF.NClause := [(17,true),(8,false),(76,true),(10,false)]
theorem der_50122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50122 :=
  CNF.rup_sound cl_50122 [cl_30300,cl_49531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30300 v h) (hints_cons _ _ _ (der_49531 v h) (by intro d hd; cases hd)))
def cl_50123 : CNF.NClause := [(7,false),(20,false),(71,true),(1,true)]
theorem der_50123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50123 :=
  CNF.rup_sound cl_50123 [cl_30311,cl_42754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30311 v h) (hints_cons _ _ _ (der_42754 v h) (by intro d hd; cases hd)))
def cl_50124 : CNF.NClause := [(7,false),(71,true),(1,true),(19,false)]
theorem der_50124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50124 :=
  CNF.rup_sound cl_50124 [cl_30313,cl_43719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30313 v h) (hints_cons _ _ _ (der_43719 v h) (by intro d hd; cases hd)))
def cl_50125 : CNF.NClause := [(29,false),(86,true),(14,true),(5,false)]
theorem der_50125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50125 :=
  CNF.rup_sound cl_50125 [cl_30318,cl_43136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30318 v h) (hints_cons _ _ _ (der_43136 v h) (by intro d hd; cases hd)))
def cl_50127 : CNF.NClause := [(76,true),(17,false),(24,false),(1,true)]
theorem der_50127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50127 :=
  CNF.rup_sound cl_50127 [cl_30330,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30330 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50128 : CNF.NClause := [(71,true),(20,false),(1,true),(13,false)]
theorem der_50128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50128 :=
  CNF.rup_sound cl_50128 [cl_30333,cl_42754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30333 v h) (hints_cons _ _ _ (der_42754 v h) (by intro d hd; cases hd)))
def cl_50129 : CNF.NClause := [(89,true),(14,false),(16,false),(7,true)]
theorem der_50129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50129 :=
  CNF.rup_sound cl_50129 [cl_23343,cl_49901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23343 v h) (hints_cons _ _ _ (der_49901 v h) (by intro d hd; cases hd)))
def cl_50131 : CNF.NClause := [(19,false),(27,false),(85,true),(3,true)]
theorem der_50131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50131 :=
  CNF.rup_sound cl_50131 [cl_30358,cl_49887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30358 v h) (hints_cons _ _ _ (der_49887 v h) (by intro d hd; cases hd)))
def cl_50133 : CNF.NClause := [(26,false),(79,true),(2,true),(14,false)]
theorem der_50133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50133 :=
  CNF.rup_sound cl_50133 [cl_30364,cl_49988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30364 v h) (hints_cons _ _ _ (der_49988 v h) (by intro d hd; cases hd)))
def cl_50134 : CNF.NClause := [(12,false),(26,true),(18,false),(91,true)]
theorem der_50134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50134 :=
  CNF.rup_sound cl_50134 [cl_23368,cl_49974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23368 v h) (hints_cons _ _ _ (der_49974 v h) (by intro d hd; cases hd)))
def cl_50135 : CNF.NClause := [(17,false),(76,true),(10,false),(8,true)]
theorem der_50135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50135 :=
  CNF.rup_sound cl_50135 [cl_30385,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30385 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50136 : CNF.NClause := [(15,true),(12,false),(28,false),(81,true)]
theorem der_50136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50136 :=
  CNF.rup_sound cl_50136 [cl_30391,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30391 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_50137 : CNF.NClause := [(9,false),(12,false),(28,true),(81,true)]
theorem der_50137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50137 :=
  CNF.rup_sound cl_50137 [cl_30393,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30393 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_50138 : CNF.NClause := [(14,false),(79,true),(2,false),(26,true)]
theorem der_50138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50138 :=
  CNF.rup_sound cl_50138 [cl_30405,cl_49770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30405 v h) (hints_cons _ _ _ (der_49770 v h) (by intro d hd; cases hd)))
def cl_50139 : CNF.NClause := [(9,false),(81,true),(28,true),(23,false)]
theorem der_50139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50139 :=
  CNF.rup_sound cl_50139 [cl_30407,cl_47347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30407 v h) (hints_cons _ _ _ (der_47347 v h) (by intro d hd; cases hd)))
def cl_50140 : CNF.NClause := [(81,true),(9,false),(12,true),(28,false)]
theorem der_50140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50140 :=
  CNF.rup_sound cl_50140 [cl_30411,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30411 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_50141 : CNF.NClause := [(79,true),(21,false),(2,true),(26,false)]
theorem der_50141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50141 :=
  CNF.rup_sound cl_50141 [cl_30412,cl_50133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30412 v h) (hints_cons _ _ _ (der_50133 v h) (by intro d hd; cases hd)))
def cl_50142 : CNF.NClause := [(18,false),(17,false),(19,true),(77,true)]
theorem der_50142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50142 :=
  CNF.rup_sound cl_50142 [cl_23380,cl_37432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23380 v h) (hints_cons _ _ _ (der_37432 v h) (by intro d hd; cases hd)))
def cl_50143 : CNF.NClause := [(14,false),(21,false),(79,true),(26,true)]
theorem der_50143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50143 :=
  CNF.rup_sound cl_50143 [cl_30416,cl_50138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30416 v h) (hints_cons _ _ _ (der_50138 v h) (by intro d hd; cases hd)))
def cl_50144 : CNF.NClause := [(15,true),(27,false),(78,true),(13,false)]
theorem der_50144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50144 :=
  CNF.rup_sound cl_50144 [cl_30418,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30418 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50145 : CNF.NClause := [(15,true),(81,true),(28,false),(1,false)]
theorem der_50145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50145 :=
  CNF.rup_sound cl_50145 [cl_30421,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30421 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_50146 : CNF.NClause := [(81,true),(28,true),(1,false),(23,false)]
theorem der_50146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50146 :=
  CNF.rup_sound cl_50146 [cl_30422,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30422 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_50148 : CNF.NClause := [(90,true),(28,true),(8,false),(19,false)]
theorem der_50148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50148 :=
  CNF.rup_sound cl_50148 [cl_23391,cl_49801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23391 v h) (hints_cons _ _ _ (der_49801 v h) (by intro d hd; cases hd)))
def cl_50149 : CNF.NClause := [(27,false),(18,true),(69,true),(9,false)]
theorem der_50149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50149 :=
  CNF.rup_sound cl_50149 [cl_30440,cl_47172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30440 v h) (hints_cons _ _ _ (der_47172 v h) (by intro d hd; cases hd)))
def cl_50150 : CNF.NClause := [(27,true),(9,false),(69,true),(2,false)]
theorem der_50150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50150 :=
  CNF.rup_sound cl_50150 [cl_30444,cl_39879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30444 v h) (hints_cons _ _ _ (der_39879 v h) (by intro d hd; cases hd)))
def cl_50152 : CNF.NClause := [(69,true),(18,false),(20,false),(2,true)]
theorem der_50152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50152 :=
  CNF.rup_sound cl_50152 [cl_30453,cl_47172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30453 v h) (hints_cons _ _ _ (der_47172 v h) (by intro d hd; cases hd)))
def cl_50153 : CNF.NClause := [(20,true),(70,true),(6,false),(28,false)]
theorem der_50153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50153 :=
  CNF.rup_sound cl_50153 [cl_30474,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30474 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_50154 : CNF.NClause := [(28,true),(6,false),(70,true),(17,false)]
theorem der_50154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50154 :=
  CNF.rup_sound cl_50154 [cl_30479,cl_49809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30479 v h) (hints_cons _ _ _ (der_49809 v h) (by intro d hd; cases hd)))
def cl_50155 : CNF.NClause := [(85,true),(3,true),(12,false),(27,false)]
theorem der_50155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50155 :=
  CNF.rup_sound cl_50155 [cl_30486,cl_49138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30486 v h) (hints_cons _ _ _ (der_49138 v h) (by intro d hd; cases hd)))
def cl_50156 : CNF.NClause := [(27,false),(21,true),(5,false),(85,true)]
theorem der_50156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50156 :=
  CNF.rup_sound cl_50156 [cl_30487,cl_49888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30487 v h) (hints_cons _ _ _ (der_49888 v h) (by intro d hd; cases hd)))
def cl_50157 : CNF.NClause := [(19,false),(21,false),(85,true),(12,true)]
theorem der_50157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50157 :=
  CNF.rup_sound cl_50157 [cl_30489,cl_50114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30489 v h) (hints_cons _ _ _ (der_50114 v h) (by intro d hd; cases hd)))
def cl_50158 : CNF.NClause := [(3,true),(12,false),(21,false),(85,true)]
theorem der_50158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50158 :=
  CNF.rup_sound cl_50158 [cl_30490,cl_49138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30490 v h) (hints_cons _ _ _ (der_49138 v h) (by intro d hd; cases hd)))
def cl_50159 : CNF.NClause := [(85,true),(12,true),(5,false),(21,false)]
theorem der_50159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50159 :=
  CNF.rup_sound cl_50159 [cl_30491,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30491 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_50160 : CNF.NClause := [(21,true),(12,false),(5,false),(85,true)]
theorem der_50160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50160 :=
  CNF.rup_sound cl_50160 [cl_30494,cl_50156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30494 v h) (hints_cons _ _ _ (der_50156 v h) (by intro d hd; cases hd)))
def cl_50161 : CNF.NClause := [(10,false),(75,true),(22,false),(16,true)]
theorem der_50161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50161 :=
  CNF.rup_sound cl_50161 [cl_30502,cl_40899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30502 v h) (hints_cons _ _ _ (der_40899 v h) (by intro d hd; cases hd)))
def cl_50162 : CNF.NClause := [(10,false),(75,true),(16,false),(3,true)]
theorem der_50162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50162 :=
  CNF.rup_sound cl_50162 [cl_30503,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30503 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_50163 : CNF.NClause := [(14,false),(17,false),(70,true),(6,true)]
theorem der_50163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50163 :=
  CNF.rup_sound cl_50163 [cl_30505,cl_49773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30505 v h) (hints_cons _ _ _ (der_49773 v h) (by intro d hd; cases hd)))
def cl_50164 : CNF.NClause := [(14,false),(18,false),(86,true),(5,true)]
theorem der_50164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50164 :=
  CNF.rup_sound cl_50164 [cl_30510,cl_49968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30510 v h) (hints_cons _ _ _ (der_49968 v h) (by intro d hd; cases hd)))
def cl_50165 : CNF.NClause := [(28,true),(73,true),(7,false),(18,false)]
theorem der_50165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50165 :=
  CNF.rup_sound cl_50165 [cl_30526,cl_50010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30526 v h) (hints_cons _ _ _ (der_50010 v h) (by intro d hd; cases hd)))
def cl_50166 : CNF.NClause := [(8,false),(76,true),(27,false),(10,true)]
theorem der_50166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50166 :=
  CNF.rup_sound cl_50166 [cl_30531,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30531 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50167 : CNF.NClause := [(76,true),(24,false),(17,true),(8,false)]
theorem der_50167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50167 :=
  CNF.rup_sound cl_50167 [cl_30533,cl_50122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30533 v h) (hints_cons _ _ _ (der_50122 v h) (by intro d hd; cases hd)))
def cl_50168 : CNF.NClause := [(76,true),(1,false),(10,true),(17,false)]
theorem der_50168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50168 :=
  CNF.rup_sound cl_50168 [cl_30534,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30534 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50169 : CNF.NClause := [(74,true),(19,false),(29,true),(23,false)]
theorem der_50169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50169 :=
  CNF.rup_sound cl_50169 [cl_30544,cl_44863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30544 v h) (hints_cons _ _ _ (der_44863 v h) (by intro d hd; cases hd)))
def cl_50170 : CNF.NClause := [(73,true),(4,false),(21,true),(18,false)]
theorem der_50170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50170 :=
  CNF.rup_sound cl_50170 [cl_30548,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30548 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_50171 : CNF.NClause := [(29,false),(23,false),(6,true),(74,true)]
theorem der_50171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50171 :=
  CNF.rup_sound cl_50171 [cl_30552,cl_45005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30552 v h) (hints_cons _ _ _ (der_45005 v h) (by intro d hd; cases hd)))
def cl_50172 : CNF.NClause := [(73,true),(21,false),(10,true),(28,false)]
theorem der_50172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50172 :=
  CNF.rup_sound cl_50172 [cl_30554,cl_49923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30554 v h) (hints_cons _ _ _ (der_49923 v h) (by intro d hd; cases hd)))
def cl_50173 : CNF.NClause := [(18,false),(73,true),(10,true),(28,false)]
theorem der_50173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50173 :=
  CNF.rup_sound cl_50173 [cl_30555,cl_49960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30555 v h) (hints_cons _ _ _ (der_49960 v h) (by intro d hd; cases hd)))
def cl_50174 : CNF.NClause := [(18,false),(10,true),(73,true),(21,false)]
theorem der_50174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50174 :=
  CNF.rup_sound cl_50174 [cl_30556,cl_50010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30556 v h) (hints_cons _ _ _ (der_50010 v h) (by intro d hd; cases hd)))
def cl_50175 : CNF.NClause := [(26,false),(22,false),(75,true),(10,true)]
theorem der_50175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50175 :=
  CNF.rup_sound cl_50175 [cl_30557,cl_49815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30557 v h) (hints_cons _ _ _ (der_49815 v h) (by intro d hd; cases hd)))
def cl_50176 : CNF.NClause := [(26,false),(16,false),(75,true),(10,true)]
theorem der_50176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50176 :=
  CNF.rup_sound cl_50176 [cl_30558,cl_50012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30558 v h) (hints_cons _ _ _ (der_50012 v h) (by intro d hd; cases hd)))
def cl_50177 : CNF.NClause := [(16,false),(22,false),(75,true),(10,true)]
theorem der_50177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50177 :=
  CNF.rup_sound cl_50177 [cl_30559,cl_49815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30559 v h) (hints_cons _ _ _ (der_49815 v h) (by intro d hd; cases hd)))
def cl_50178 : CNF.NClause := [(22,false),(3,false),(26,true),(75,true)]
theorem der_50178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50178 :=
  CNF.rup_sound cl_50178 [cl_30560,cl_49972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30560 v h) (hints_cons _ _ _ (der_49972 v h) (by intro d hd; cases hd)))
def cl_50179 : CNF.NClause := [(29,false),(74,true),(2,true),(6,false)]
theorem der_50179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50179 :=
  CNF.rup_sound cl_50179 [cl_30563,cl_42451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30563 v h) (hints_cons _ _ _ (der_42451 v h) (by intro d hd; cases hd)))
def cl_50180 : CNF.NClause := [(9,false),(63,true),(19,true),(14,false)]
theorem der_50180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50180 :=
  CNF.rup_sound cl_50180 [cl_23433,cl_42527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23433 v h) (hints_cons _ _ _ (der_42527 v h) (by intro d hd; cases hd)))
def cl_50181 : CNF.NClause := [(27,true),(15,false),(78,true),(13,false)]
theorem der_50181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50181 :=
  CNF.rup_sound cl_50181 [cl_30568,cl_49545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30568 v h) (hints_cons _ _ _ (der_49545 v h) (by intro d hd; cases hd)))
def cl_50182 : CNF.NClause := [(20,true),(29,false),(68,true),(8,false)]
theorem der_50182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50182 :=
  CNF.rup_sound cl_50182 [cl_30576,cl_49820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30576 v h) (hints_cons _ _ _ (der_49820 v h) (by intro d hd; cases hd)))
def cl_50184 : CNF.NClause := [(20,true),(12,false),(68,true),(16,false)]
theorem der_50184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50184 :=
  CNF.rup_sound cl_50184 [cl_30581,cl_49820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30581 v h) (hints_cons _ _ _ (der_49820 v h) (by intro d hd; cases hd)))
def cl_50185 : CNF.NClause := [(20,true),(8,false),(68,true),(16,false)]
theorem der_50185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50185 :=
  CNF.rup_sound cl_50185 [cl_30582,cl_50182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30582 v h) (hints_cons _ _ _ (der_50182 v h) (by intro d hd; cases hd)))
def cl_50186 : CNF.NClause := [(8,false),(12,false),(16,true),(68,true)]
theorem der_50186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50186 :=
  CNF.rup_sound cl_50186 [cl_30583,cl_49989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30583 v h) (hints_cons _ _ _ (der_49989 v h) (by intro d hd; cases hd)))
def cl_50187 : CNF.NClause := [(20,true),(14,false),(70,true),(28,false)]
theorem der_50187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50187 :=
  CNF.rup_sound cl_50187 [cl_30592,cl_49686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30592 v h) (hints_cons _ _ _ (der_49686 v h) (by intro d hd; cases hd)))
def cl_50188 : CNF.NClause := [(17,true),(14,false),(20,false),(70,true)]
theorem der_50188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50188 :=
  CNF.rup_sound cl_50188 [cl_30593,cl_49810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30593 v h) (hints_cons _ _ _ (der_49810 v h) (by intro d hd; cases hd)))
def cl_50190 : CNF.NClause := [(24,false),(76,true),(27,false),(10,true)]
theorem der_50190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50190 :=
  CNF.rup_sound cl_50190 [cl_30602,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30602 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50191 : CNF.NClause := [(27,false),(10,false),(76,true),(1,true)]
theorem der_50191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50191 :=
  CNF.rup_sound cl_50191 [cl_30619,cl_42519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30619 v h) (hints_cons _ _ _ (der_42519 v h) (by intro d hd; cases hd)))
def cl_50192 : CNF.NClause := [(77,true),(19,false),(17,true),(18,false)]
theorem der_50192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50192 :=
  CNF.rup_sound cl_50192 [cl_23450,cl_36157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23450 v h) (hints_cons _ _ _ (der_36157 v h) (by intro d hd; cases hd)))
def cl_50193 : CNF.NClause := [(27,true),(4,false),(78,true),(22,false)]
theorem der_50193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50193 :=
  CNF.rup_sound cl_50193 [cl_30637,cl_49545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30637 v h) (hints_cons _ _ _ (der_49545 v h) (by intro d hd; cases hd)))
def cl_50194 : CNF.NClause := [(27,true),(78,true),(6,false),(15,false)]
theorem der_50194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50194 :=
  CNF.rup_sound cl_50194 [cl_30638,cl_49545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30638 v h) (hints_cons _ _ _ (der_49545 v h) (by intro d hd; cases hd)))
def cl_50195 : CNF.NClause := [(16,false),(5,true),(84,true),(24,false)]
theorem der_50195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50195 :=
  CNF.rup_sound cl_50195 [cl_30645,cl_49979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30645 v h) (hints_cons _ _ _ (der_49979 v h) (by intro d hd; cases hd)))
def cl_50196 : CNF.NClause := [(78,true),(15,false),(6,true),(4,false)]
theorem der_50196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50196 :=
  CNF.rup_sound cl_50196 [cl_30649,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30649 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50198 : CNF.NClause := [(28,true),(84,true),(24,false),(5,false)]
theorem der_50198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50198 :=
  CNF.rup_sound cl_50198 [cl_30656,cl_37830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30656 v h) (hints_cons _ _ _ (der_37830 v h) (by intro d hd; cases hd)))
def cl_50199 : CNF.NClause := [(16,false),(24,true),(84,true),(5,false)]
theorem der_50199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50199 :=
  CNF.rup_sound cl_50199 [cl_30657,cl_42738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30657 v h) (hints_cons _ _ _ (der_42738 v h) (by intro d hd; cases hd)))
def cl_50200 : CNF.NClause := [(27,false),(22,true),(78,true),(15,false)]
theorem der_50200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50200 :=
  CNF.rup_sound cl_50200 [cl_30660,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30660 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50201 : CNF.NClause := [(15,true),(78,true),(27,false),(6,false)]
theorem der_50201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50201 :=
  CNF.rup_sound cl_50201 [cl_30661,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30661 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50202 : CNF.NClause := [(6,false),(78,true),(13,true),(22,false)]
theorem der_50202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50202 :=
  CNF.rup_sound cl_50202 [cl_30663,cl_50060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30663 v h) (hints_cons _ _ _ (der_50060 v h) (by intro d hd; cases hd)))
def cl_50203 : CNF.NClause := [(71,true),(1,false),(19,true),(7,false)]
theorem der_50203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50203 :=
  CNF.rup_sound cl_50203 [cl_30671,cl_42582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30671 v h) (hints_cons _ _ _ (der_42582 v h) (by intro d hd; cases hd)))
def cl_50205 : CNF.NClause := [(69,true),(9,true),(20,false),(18,false)]
theorem der_50205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50205 :=
  CNF.rup_sound cl_50205 [cl_30682,cl_47172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30682 v h) (hints_cons _ _ _ (der_47172 v h) (by intro d hd; cases hd)))
def cl_50206 : CNF.NClause := [(9,true),(18,false),(69,true),(11,false)]
theorem der_50206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50206 :=
  CNF.rup_sound cl_50206 [cl_30685,cl_50011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30685 v h) (hints_cons _ _ _ (der_50011 v h) (by intro d hd; cases hd)))
def cl_50207 : CNF.NClause := [(20,true),(18,false),(69,true),(2,false)]
theorem der_50207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50207 :=
  CNF.rup_sound cl_50207 [cl_30686,cl_39879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30686 v h) (hints_cons _ _ _ (der_39879 v h) (by intro d hd; cases hd)))
def cl_50208 : CNF.NClause := [(81,true),(23,true),(28,false),(15,false)]
theorem der_50208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50208 :=
  CNF.rup_sound cl_50208 [cl_30688,cl_50006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30688 v h) (hints_cons _ _ _ (der_50006 v h) (by intro d hd; cases hd)))
def cl_50209 : CNF.NClause := [(81,true),(28,true),(1,false),(15,false)]
theorem der_50209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50209 :=
  CNF.rup_sound cl_50209 [cl_30689,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30689 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_50210 : CNF.NClause := [(10,false),(75,true),(16,true),(26,false)]
theorem der_50210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50210 :=
  CNF.rup_sound cl_50210 [cl_30695,cl_50161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30695 v h) (hints_cons _ _ _ (der_50161 v h) (by intro d hd; cases hd)))
def cl_50211 : CNF.NClause := [(67,true),(22,true),(24,false),(21,false)]
theorem der_50211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50211 :=
  CNF.rup_sound cl_50211 [cl_23479,cl_35216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23479 v h) (hints_cons _ _ _ (der_35216 v h) (by intro d hd; cases hd)))
def cl_50212 : CNF.NClause := [(27,false),(21,false),(85,true),(12,true)]
theorem der_50212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50212 :=
  CNF.rup_sound cl_50212 [cl_30696,cl_50159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30696 v h) (hints_cons _ _ _ (der_50159 v h) (by intro d hd; cases hd)))
def cl_50213 : CNF.NClause := [(9,true),(13,false),(21,false),(88,true)]
theorem der_50213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50213 :=
  CNF.rup_sound cl_50213 [cl_23489,cl_49839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23489 v h) (hints_cons _ _ _ (der_49839 v h) (by intro d hd; cases hd)))
def cl_50215 : CNF.NClause := [(28,true),(21,false),(73,true),(10,false)]
theorem der_50215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50215 :=
  CNF.rup_sound cl_50215 [cl_30706,cl_49967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30706 v h) (hints_cons _ _ _ (der_49967 v h) (by intro d hd; cases hd)))
def cl_50216 : CNF.NClause := [(110,true),(45,true),(57,false),(33,false)]
theorem der_50216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50216 :=
  CNF.rup_sound cl_50216 [cl_30727,cl_49840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30727 v h) (hints_cons _ _ _ (der_49840 v h) (by intro d hd; cases hd)))
def cl_50217 : CNF.NClause := [(58,false),(35,false),(109,true),(46,true)]
theorem der_50217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50217 :=
  CNF.rup_sound cl_50217 [cl_30780,cl_35634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30780 v h) (hints_cons _ _ _ (der_35634 v h) (by intro d hd; cases hd)))
def cl_50218 : CNF.NClause := [(44,true),(109,true),(46,false),(35,false)]
theorem der_50218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50218 :=
  CNF.rup_sound cl_50218 [cl_30785,cl_37286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30785 v h) (hints_cons _ _ _ (der_37286 v h) (by intro d hd; cases hd)))
def cl_50219 : CNF.NClause := [(122,true),(57,false),(43,false),(31,true)]
theorem der_50219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50219 :=
  CNF.rup_sound cl_50219 [cl_30811,cl_50048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30811 v h) (hints_cons _ _ _ (der_50048 v h) (by intro d hd; cases hd)))
def cl_50220 : CNF.NClause := [(122,true),(31,true),(43,false),(55,false)]
theorem der_50220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50220 :=
  CNF.rup_sound cl_50220 [cl_37736,cl_48925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37736 v h) (hints_cons _ _ _ (der_48925 v h) (by intro d hd; cases hd)))
def cl_50221 : CNF.NClause := [(59,false),(44,true),(33,false),(115,true)]
theorem der_50221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50221 :=
  CNF.rup_sound cl_50221 [cl_30839,cl_49911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30839 v h) (hints_cons _ _ _ (der_49911 v h) (by intro d hd; cases hd)))
def cl_50222 : CNF.NClause := [(115,true),(55,false),(33,false),(47,true)]
theorem der_50222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50222 :=
  CNF.rup_sound cl_50222 [cl_30842,cl_37418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30842 v h) (hints_cons _ _ _ (der_37418 v h) (by intro d hd; cases hd)))
def cl_50225 : CNF.NClause := [(36,true),(60,false),(32,false),(117,true)]
theorem der_50225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50225 :=
  CNF.rup_sound cl_50225 [cl_30847,cl_49632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30847 v h) (hints_cons _ _ _ (der_49632 v h) (by intro d hd; cases hd)))
def cl_50226 : CNF.NClause := [(36,true),(57,false),(35,false),(114,true)]
theorem der_50226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50226 :=
  CNF.rup_sound cl_50226 [cl_30858,cl_49585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30858 v h) (hints_cons _ _ _ (der_49585 v h) (by intro d hd; cases hd)))
def cl_50229 : CNF.NClause := [(116,true),(50,false),(36,true),(34,false)]
theorem der_50229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50229 :=
  CNF.rup_sound cl_50229 [cl_30871,cl_49956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30871 v h) (hints_cons _ _ _ (der_49956 v h) (by intro d hd; cases hd)))
def cl_50230 : CNF.NClause := [(98,true),(51,false),(55,false),(61,true)]
theorem der_50230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50230 :=
  CNF.rup_sound cl_50230 [cl_30971,cl_43460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30971 v h) (hints_cons _ _ _ (der_43460 v h) (by intro d hd; cases hd)))
def cl_50231 : CNF.NClause := [(98,true),(51,false),(61,true),(53,false)]
theorem der_50231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50231 :=
  CNF.rup_sound cl_50231 [cl_30972,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30972 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50232 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false)]
theorem der_50232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50232 :=
  CNF.rup_sound cl_50232 [cl_30978,cl_48868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30978 v h) (hints_cons _ _ _ (der_48868 v h) (by intro d hd; cases hd)))
def cl_50233 : CNF.NClause := [(120,true),(31,true),(54,false),(38,false)]
theorem der_50233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50233 :=
  CNF.rup_sound cl_50233 [cl_30985,cl_44945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30985 v h) (hints_cons _ _ _ (der_44945 v h) (by intro d hd; cases hd)))
def cl_50237 : CNF.NClause := [(119,true),(52,false),(31,false),(48,true)]
theorem der_50237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50237 :=
  CNF.rup_sound cl_50237 [cl_31023,cl_49672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31023 v h) (hints_cons _ _ _ (der_49672 v h) (by intro d hd; cases hd)))
def cl_50240 : CNF.NClause := [(120,true),(54,false),(58,false),(45,false)]
theorem der_50240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50240 :=
  CNF.rup_sound cl_50240 [cl_31034,cl_45954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31034 v h) (hints_cons _ _ _ (der_45954 v h) (by intro d hd; cases hd)))
def cl_50241 : CNF.NClause := [(120,true),(38,true),(45,false),(58,false)]
theorem der_50241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50241 :=
  CNF.rup_sound cl_50241 [cl_31042,cl_50240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31042 v h) (hints_cons _ _ _ (der_50240 v h) (by intro d hd; cases hd)))
def cl_50244 : CNF.NClause := [(120,true),(54,false),(45,false),(38,false)]
theorem der_50244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50244 :=
  CNF.rup_sound cl_50244 [cl_31049,cl_50240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31049 v h) (hints_cons _ _ _ (der_50240 v h) (by intro d hd; cases hd)))
def cl_50247 : CNF.NClause := [(120,true),(45,false),(38,false),(47,false)]
theorem der_50247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50247 :=
  CNF.rup_sound cl_50247 [cl_31053,cl_50244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31053 v h) (hints_cons _ _ _ (der_50244 v h) (by intro d hd; cases hd)))
def cl_50248 : CNF.NClause := [(120,true),(54,true),(47,false),(45,false)]
theorem der_50248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50248 :=
  CNF.rup_sound cl_50248 [cl_31054,cl_50247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31054 v h) (hints_cons _ _ _ (der_50247 v h) (by intro d hd; cases hd)))
def cl_50249 : CNF.NClause := [(120,true),(54,true),(47,false),(38,false)]
theorem der_50249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50249 :=
  CNF.rup_sound cl_50249 [cl_31055,cl_50247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31055 v h) (hints_cons _ _ _ (der_50247 v h) (by intro d hd; cases hd)))
def cl_50250 : CNF.NClause := [(120,true),(54,true),(38,false),(45,false)]
theorem der_50250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50250 :=
  CNF.rup_sound cl_50250 [cl_31057,cl_50247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31057 v h) (hints_cons _ _ _ (der_50247 v h) (by intro d hd; cases hd)))
def cl_50257 : CNF.NClause := [(57,false),(122,true),(55,false),(49,true)]
theorem der_50257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50257 :=
  CNF.rup_sound cl_50257 [cl_31087,cl_50053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31087 v h) (hints_cons _ _ _ (der_50053 v h) (by intro d hd; cases hd)))
def cl_50265 : CNF.NClause := [(108,true),(50,false),(47,false),(46,true)]
theorem der_50265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50265 :=
  CNF.rup_sound cl_50265 [cl_31168,cl_35584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31168 v h) (hints_cons _ _ _ (der_35584 v h) (by intro d hd; cases hd)))
def cl_50266 : CNF.NClause := [(108,true),(47,false),(49,false),(46,true)]
theorem der_50266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50266 :=
  CNF.rup_sound cl_50266 [cl_31170,cl_35584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31170 v h) (hints_cons _ _ _ (der_35584 v h) (by intro d hd; cases hd)))
def cl_50267 : CNF.NClause := [(40,false),(33,false),(49,true),(100,true)]
theorem der_50267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50267 :=
  CNF.rup_sound cl_50267 [cl_31180,cl_37499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31180 v h) (hints_cons _ _ _ (der_37499 v h) (by intro d hd; cases hd)))
def cl_50268 : CNF.NClause := [(114,true),(36,false),(35,false),(42,true)]
theorem der_50268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50268 :=
  CNF.rup_sound cl_50268 [cl_31201,cl_50024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31201 v h) (hints_cons _ _ _ (der_50024 v h) (by intro d hd; cases hd)))
def cl_50269 : CNF.NClause := [(121,true),(50,false),(31,true),(39,false)]
theorem der_50269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50269 :=
  CNF.rup_sound cl_50269 [cl_31207,cl_47827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31207 v h) (hints_cons _ _ _ (der_47827 v h) (by intro d hd; cases hd)))
def cl_50270 : CNF.NClause := [(49,true),(51,false),(100,true),(33,false)]
theorem der_50270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50270 :=
  CNF.rup_sound cl_50270 [cl_31213,cl_43615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31213 v h) (hints_cons _ _ _ (der_43615 v h) (by intro d hd; cases hd)))
def cl_50271 : CNF.NClause := [(111,true),(34,false),(55,false),(38,true)]
theorem der_50271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50271 :=
  CNF.rup_sound cl_50271 [cl_31219,cl_42523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31219 v h) (hints_cons _ _ _ (der_42523 v h) (by intro d hd; cases hd)))
def cl_50272 : CNF.NClause := [(96,true),(34,true),(49,false),(39,false)]
theorem der_50272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50272 :=
  CNF.rup_sound cl_50272 [cl_31235,cl_49744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31235 v h) (hints_cons _ _ _ (der_49744 v h) (by intro d hd; cases hd)))
def cl_50273 : CNF.NClause := [(59,false),(101,true),(48,true),(51,false)]
theorem der_50273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50273 :=
  CNF.rup_sound cl_50273 [cl_31242,cl_49950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31242 v h) (hints_cons _ _ _ (der_49950 v h) (by intro d hd; cases hd)))
def cl_50274 : CNF.NClause := [(101,true),(59,false),(48,false),(37,true)]
theorem der_50274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50274 :=
  CNF.rup_sound cl_50274 [cl_31245,cl_49844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31245 v h) (hints_cons _ _ _ (der_49844 v h) (by intro d hd; cases hd)))
def cl_50275 : CNF.NClause := [(101,true),(59,false),(37,false),(34,true)]
theorem der_50275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50275 :=
  CNF.rup_sound cl_50275 [cl_31248,cl_49892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31248 v h) (hints_cons _ _ _ (der_49892 v h) (by intro d hd; cases hd)))
def cl_50276 : CNF.NClause := [(101,true),(48,false),(51,false),(45,true)]
theorem der_50276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50276 :=
  CNF.rup_sound cl_50276 [cl_31251,cl_49950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31251 v h) (hints_cons _ _ _ (der_49950 v h) (by intro d hd; cases hd)))
def cl_50277 : CNF.NClause := [(48,true),(101,true),(37,false),(51,false)]
theorem der_50277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50277 :=
  CNF.rup_sound cl_50277 [cl_31254,cl_42870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31254 v h) (hints_cons _ _ _ (der_42870 v h) (by intro d hd; cases hd)))
def cl_50279 : CNF.NClause := [(101,true),(48,true),(37,false),(45,false)]
theorem der_50279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50279 :=
  CNF.rup_sound cl_50279 [cl_31258,cl_42866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31258 v h) (hints_cons _ _ _ (der_42866 v h) (by intro d hd; cases hd)))
def cl_50280 : CNF.NClause := [(57,false),(47,false),(106,true),(34,true)]
theorem der_50280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50280 :=
  CNF.rup_sound cl_50280 [cl_31268,cl_41690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31268 v h) (hints_cons _ _ _ (der_41690 v h) (by intro d hd; cases hd)))
def cl_50281 : CNF.NClause := [(41,false),(57,false),(106,true),(47,true)]
theorem der_50281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50281 :=
  CNF.rup_sound cl_50281 [cl_31270,cl_49893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31270 v h) (hints_cons _ _ _ (der_49893 v h) (by intro d hd; cases hd)))
def cl_50282 : CNF.NClause := [(40,false),(57,false),(34,true),(106,true)]
theorem der_50282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50282 :=
  CNF.rup_sound cl_50282 [cl_31271,cl_49893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31271 v h) (hints_cons _ _ _ (der_49893 v h) (by intro d hd; cases hd)))
def cl_50283 : CNF.NClause := [(40,true),(106,true),(53,false),(47,false)]
theorem der_50283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50283 :=
  CNF.rup_sound cl_50283 [cl_31274,cl_43027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31274 v h) (hints_cons _ _ _ (der_43027 v h) (by intro d hd; cases hd)))
def cl_50284 : CNF.NClause := [(41,false),(53,false),(106,true),(34,true)]
theorem der_50284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50284 :=
  CNF.rup_sound cl_50284 [cl_31276,cl_49910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31276 v h) (hints_cons _ _ _ (der_49910 v h) (by intro d hd; cases hd)))
def cl_50285 : CNF.NClause := [(41,false),(106,true),(53,true),(47,false)]
theorem der_50285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50285 :=
  CNF.rup_sound cl_50285 [cl_31279,cl_49893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31279 v h) (hints_cons _ _ _ (der_49893 v h) (by intro d hd; cases hd)))
def cl_50286 : CNF.NClause := [(60,false),(111,true),(42,true),(55,false)]
theorem der_50286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50286 :=
  CNF.rup_sound cl_50286 [cl_31288,cl_49969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31288 v h) (hints_cons _ _ _ (der_49969 v h) (by intro d hd; cases hd)))
def cl_50288 : CNF.NClause := [(60,false),(111,true),(38,false),(42,true)]
theorem der_50288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50288 :=
  CNF.rup_sound cl_50288 [cl_31295,cl_49842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31295 v h) (hints_cons _ _ _ (der_49842 v h) (by intro d hd; cases hd)))
def cl_50289 : CNF.NClause := [(111,true),(55,false),(46,false),(42,true)]
theorem der_50289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50289 :=
  CNF.rup_sound cl_50289 [cl_31299,cl_42523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31299 v h) (hints_cons _ _ _ (der_42523 v h) (by intro d hd; cases hd)))
def cl_50290 : CNF.NClause := [(111,true),(38,true),(42,false),(55,false)]
theorem der_50290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50290 :=
  CNF.rup_sound cl_50290 [cl_31301,cl_49969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31301 v h) (hints_cons _ _ _ (der_49969 v h) (by intro d hd; cases hd)))
def cl_50291 : CNF.NClause := [(111,true),(55,false),(38,false),(42,true)]
theorem der_50291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50291 :=
  CNF.rup_sound cl_50291 [cl_31302,cl_49842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31302 v h) (hints_cons _ _ _ (der_49842 v h) (by intro d hd; cases hd)))
def cl_50293 : CNF.NClause := [(116,true),(43,true),(50,false),(58,false)]
theorem der_50293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50293 :=
  CNF.rup_sound cl_50293 [cl_31312,cl_47407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31312 v h) (hints_cons _ _ _ (der_47407 v h) (by intro d hd; cases hd)))
def cl_50294 : CNF.NClause := [(116,true),(36,true),(43,false),(50,false)]
theorem der_50294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50294 :=
  CNF.rup_sound cl_50294 [cl_31323,cl_49847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31323 v h) (hints_cons _ _ _ (der_49847 v h) (by intro d hd; cases hd)))
def cl_50295 : CNF.NClause := [(116,true),(36,false),(43,true),(50,false)]
theorem der_50295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50295 :=
  CNF.rup_sound cl_50295 [cl_31324,cl_49981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31324 v h) (hints_cons _ _ _ (der_49981 v h) (by intro d hd; cases hd)))
def cl_50297 : CNF.NClause := [(118,true),(32,false),(35,false),(34,true)]
theorem der_50297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50297 :=
  CNF.rup_sound cl_50297 [cl_31331,cl_49736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31331 v h) (hints_cons _ _ _ (der_49736 v h) (by intro d hd; cases hd)))
def cl_50298 : CNF.NClause := [(118,true),(34,true),(32,false),(33,false)]
theorem der_50298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50298 :=
  CNF.rup_sound cl_50298 [cl_31333,cl_49736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31333 v h) (hints_cons _ _ _ (der_49736 v h) (by intro d hd; cases hd)))
def cl_50299 : CNF.NClause := [(31,true),(123,true),(51,false),(46,false)]
theorem der_50299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50299 :=
  CNF.rup_sound cl_50299 [cl_31383,cl_50050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31383 v h) (hints_cons _ _ _ (der_50050 v h) (by intro d hd; cases hd)))
def cl_50300 : CNF.NClause := [(108,true),(50,false),(49,true),(46,false)]
theorem der_50300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50300 :=
  CNF.rup_sound cl_50300 [cl_31405,cl_45747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31405 v h) (hints_cons _ _ _ (der_45747 v h) (by intro d hd; cases hd)))
def cl_50301 : CNF.NClause := [(48,true),(33,false),(95,true),(38,false)]
theorem der_50301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50301 :=
  CNF.rup_sound cl_50301 [cl_31415,cl_42910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31415 v h) (hints_cons _ _ _ (der_42910 v h) (by intro d hd; cases hd)))
def cl_50302 : CNF.NClause := [(54,true),(32,false),(40,false),(112,true)]
theorem der_50302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50302 :=
  CNF.rup_sound cl_50302 [cl_31421,cl_47068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31421 v h) (hints_cons _ _ _ (der_47068 v h) (by intro d hd; cases hd)))
def cl_50305 : CNF.NClause := [(32,false),(54,true),(112,true),(59,false)]
theorem der_50305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50305 :=
  CNF.rup_sound cl_50305 [cl_31441,cl_47068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31441 v h) (hints_cons _ _ _ (der_47068 v h) (by intro d hd; cases hd)))
def cl_50306 : CNF.NClause := [(122,true),(31,true),(57,false),(37,false)]
theorem der_50306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50306 :=
  CNF.rup_sound cl_50306 [cl_31445,cl_42474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31445 v h) (hints_cons _ _ _ (der_42474 v h) (by intro d hd; cases hd)))
def cl_50309 : CNF.NClause := [(95,true),(48,false),(38,false),(53,true)]
theorem der_50309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50309 :=
  CNF.rup_sound cl_50309 [cl_31474,cl_37429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31474 v h) (hints_cons _ _ _ (der_37429 v h) (by intro d hd; cases hd)))
def cl_50310 : CNF.NClause := [(40,false),(49,true),(100,true),(58,false)]
theorem der_50310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50310 :=
  CNF.rup_sound cl_50310 [cl_31483,cl_49914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31483 v h) (hints_cons _ _ _ (der_49914 v h) (by intro d hd; cases hd)))
def cl_50313 : CNF.NClause := [(40,false),(100,true),(49,false),(33,true)]
theorem der_50313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50313 :=
  CNF.rup_sound cl_50313 [cl_31491,cl_49914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31491 v h) (hints_cons _ _ _ (der_49914 v h) (by intro d hd; cases hd)))
def cl_50316 : CNF.NClause := [(50,false),(105,true),(60,false),(37,true)]
theorem der_50316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50316 :=
  CNF.rup_sound cl_50316 [cl_31501,cl_49917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31501 v h) (hints_cons _ _ _ (der_49917 v h) (by intro d hd; cases hd)))
def cl_50317 : CNF.NClause := [(105,true),(60,false),(37,false),(54,true)]
theorem der_50317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50317 :=
  CNF.rup_sound cl_50317 [cl_31504,cl_50043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31504 v h) (hints_cons _ _ _ (der_50043 v h) (by intro d hd; cases hd)))
def cl_50320 : CNF.NClause := [(50,false),(37,false),(41,true),(105,true)]
theorem der_50320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50320 :=
  CNF.rup_sound cl_50320 [cl_31514,cl_49916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31514 v h) (hints_cons _ _ _ (der_49916 v h) (by intro d hd; cases hd)))
def cl_50321 : CNF.NClause := [(52,false),(110,true),(57,false),(39,true)]
theorem der_50321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50321 :=
  CNF.rup_sound cl_50321 [cl_31519,cl_49850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31519 v h) (hints_cons _ _ _ (der_49850 v h) (by intro d hd; cases hd)))
def cl_50322 : CNF.NClause := [(57,false),(110,true),(33,true),(46,false)]
theorem der_50322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50322 :=
  CNF.rup_sound cl_50322 [cl_31521,cl_42630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31521 v h) (hints_cons _ _ _ (der_42630 v h) (by intro d hd; cases hd)))
def cl_50323 : CNF.NClause := [(110,true),(45,false),(46,true),(57,false)]
theorem der_50323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50323 :=
  CNF.rup_sound cl_50323 [cl_31523,cl_49850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31523 v h) (hints_cons _ _ _ (der_49850 v h) (by intro d hd; cases hd)))
def cl_50324 : CNF.NClause := [(110,true),(39,false),(57,false),(52,true)]
theorem der_50324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50324 :=
  CNF.rup_sound cl_50324 [cl_31524,cl_42630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31524 v h) (hints_cons _ _ _ (der_42630 v h) (by intro d hd; cases hd)))
def cl_50325 : CNF.NClause := [(110,true),(33,true),(46,false),(39,false)]
theorem der_50325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50325 :=
  CNF.rup_sound cl_50325 [cl_31533,cl_42462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31533 v h) (hints_cons _ _ _ (der_42462 v h) (by intro d hd; cases hd)))
def cl_50326 : CNF.NClause := [(59,false),(47,true),(115,true),(55,false)]
theorem der_50326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50326 :=
  CNF.rup_sound cl_50326 [cl_31538,cl_49911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31538 v h) (hints_cons _ _ _ (der_49911 v h) (by intro d hd; cases hd)))
def cl_50327 : CNF.NClause := [(44,true),(115,true),(59,false),(47,false)]
theorem der_50327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50327 :=
  CNF.rup_sound cl_50327 [cl_31541,cl_50055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31541 v h) (hints_cons _ _ _ (der_50055 v h) (by intro d hd; cases hd)))
def cl_50328 : CNF.NClause := [(115,true),(47,true),(59,false),(44,false)]
theorem der_50328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50328 :=
  CNF.rup_sound cl_50328 [cl_31543,cl_49900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31543 v h) (hints_cons _ _ _ (der_49900 v h) (by intro d hd; cases hd)))
def cl_50329 : CNF.NClause := [(115,true),(47,true),(44,false),(36,false)]
theorem der_50329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50329 :=
  CNF.rup_sound cl_50329 [cl_31553,cl_49852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31553 v h) (hints_cons _ _ _ (der_49852 v h) (by intro d hd; cases hd)))
def cl_50330 : CNF.NClause := [(101,true),(51,false),(48,true),(34,false)]
theorem der_50330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50330 :=
  CNF.rup_sound cl_50330 [cl_31569,cl_42866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31569 v h) (hints_cons _ _ _ (der_42866 v h) (by intro d hd; cases hd)))
def cl_50331 : CNF.NClause := [(110,true),(45,true),(39,false),(52,false)]
theorem der_50331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50331 :=
  CNF.rup_sound cl_50331 [cl_35478,cl_42462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35478 v h) (hints_cons _ _ _ (der_42462 v h) (by intro d hd; cases hd)))
def cl_50332 : CNF.NClause := [(60,false),(105,true),(33,false),(54,true)]
theorem der_50332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50332 :=
  CNF.rup_sound cl_50332 [cl_31646,cl_49849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31646 v h) (hints_cons _ _ _ (der_49849 v h) (by intro d hd; cases hd)))
def cl_50333 : CNF.NClause := [(57,false),(41,true),(106,true),(53,false)]
theorem der_50333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50333 :=
  CNF.rup_sound cl_50333 [cl_31657,cl_42818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31657 v h) (hints_cons _ _ _ (der_42818 v h) (by intro d hd; cases hd)))
def cl_50334 : CNF.NClause := [(40,true),(57,false),(34,false),(106,true)]
theorem der_50334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50334 :=
  CNF.rup_sound cl_50334 [cl_31661,cl_42819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31661 v h) (hints_cons _ _ _ (der_42819 v h) (by intro d hd; cases hd)))
def cl_50335 : CNF.NClause := [(41,true),(34,false),(53,false),(106,true)]
theorem der_50335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50335 :=
  CNF.rup_sound cl_50335 [cl_31665,cl_42818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31665 v h) (hints_cons _ _ _ (der_42818 v h) (by intro d hd; cases hd)))
def cl_50336 : CNF.NClause := [(40,false),(106,true),(47,false),(53,true)]
theorem der_50336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50336 :=
  CNF.rup_sound cl_50336 [cl_31666,cl_49893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31666 v h) (hints_cons _ _ _ (der_49893 v h) (by intro d hd; cases hd)))
def cl_50337 : CNF.NClause := [(40,true),(34,false),(47,false),(106,true)]
theorem der_50337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50337 :=
  CNF.rup_sound cl_50337 [cl_31667,cl_50283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31667 v h) (hints_cons _ _ _ (der_50283 v h) (by intro d hd; cases hd)))
def cl_50338 : CNF.NClause := [(59,false),(104,true),(35,false),(52,true)]
theorem der_50338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50338 :=
  CNF.rup_sound cl_50338 [cl_31671,cl_49859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31671 v h) (hints_cons _ _ _ (der_49859 v h) (by intro d hd; cases hd)))
def cl_50339 : CNF.NClause := [(60,false),(99,true),(43,true),(51,false)]
theorem der_50339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50339 :=
  CNF.rup_sound cl_50339 [cl_31702,cl_49857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31702 v h) (hints_cons _ _ _ (der_49857 v h) (by intro d hd; cases hd)))
def cl_50340 : CNF.NClause := [(43,false),(99,true),(51,false),(47,true)]
theorem der_50340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50340 :=
  CNF.rup_sound cl_50340 [cl_31712,cl_47215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31712 v h) (hints_cons _ _ _ (der_47215 v h) (by intro d hd; cases hd)))
def cl_50341 : CNF.NClause := [(99,true),(39,false),(51,false),(43,true)]
theorem der_50341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50341 :=
  CNF.rup_sound cl_50341 [cl_31713,cl_49857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31713 v h) (hints_cons _ _ _ (der_49857 v h) (by intro d hd; cases hd)))
def cl_50342 : CNF.NClause := [(104,true),(59,false),(52,false),(41,true)]
theorem der_50342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50342 :=
  CNF.rup_sound cl_50342 [cl_31723,cl_50036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31723 v h) (hints_cons _ _ _ (der_50036 v h) (by intro d hd; cases hd)))
def cl_50343 : CNF.NClause := [(59,false),(104,true),(49,false),(52,true)]
theorem der_50343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50343 :=
  CNF.rup_sound cl_50343 [cl_31727,cl_49859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31727 v h) (hints_cons _ _ _ (der_49859 v h) (by intro d hd; cases hd)))
def cl_50345 : CNF.NClause := [(104,true),(41,false),(49,false),(35,true)]
theorem der_50345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50345 :=
  CNF.rup_sound cl_50345 [cl_31738,cl_40813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31738 v h) (hints_cons _ _ _ (der_40813 v h) (by intro d hd; cases hd)))
def cl_50346 : CNF.NClause := [(104,true),(38,false),(35,true),(49,false)]
theorem der_50346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50346 :=
  CNF.rup_sound cl_50346 [cl_31739,cl_40813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31739 v h) (hints_cons _ _ _ (der_40813 v h) (by intro d hd; cases hd)))
def cl_50348 : CNF.NClause := [(37,true),(58,false),(46,false),(109,true)]
theorem der_50348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50348 :=
  CNF.rup_sound cl_50348 [cl_31744,cl_49722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31744 v h) (hints_cons _ _ _ (der_49722 v h) (by intro d hd; cases hd)))
def cl_50349 : CNF.NClause := [(58,false),(37,true),(109,true),(44,false)]
theorem der_50349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50349 :=
  CNF.rup_sound cl_50349 [cl_31746,cl_43179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31746 v h) (hints_cons _ _ _ (der_43179 v h) (by intro d hd; cases hd)))
def cl_50350 : CNF.NClause := [(37,false),(109,true),(44,true),(58,false)]
theorem der_50350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50350 :=
  CNF.rup_sound cl_50350 [cl_31747,cl_37286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31747 v h) (hints_cons _ _ _ (der_37286 v h) (by intro d hd; cases hd)))
def cl_50351 : CNF.NClause := [(35,true),(53,false),(44,false),(109,true)]
theorem der_50351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50351 :=
  CNF.rup_sound cl_50351 [cl_31752,cl_49996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31752 v h) (hints_cons _ _ _ (der_49996 v h) (by intro d hd; cases hd)))
def cl_50352 : CNF.NClause := [(44,true),(37,false),(109,true),(53,false)]
theorem der_50352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50352 :=
  CNF.rup_sound cl_50352 [cl_31753,cl_49889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31753 v h) (hints_cons _ _ _ (der_49889 v h) (by intro d hd; cases hd)))
def cl_50353 : CNF.NClause := [(35,true),(44,false),(46,false),(109,true)]
theorem der_50353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50353 :=
  CNF.rup_sound cl_50353 [cl_31755,cl_49996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31755 v h) (hints_cons _ _ _ (der_49996 v h) (by intro d hd; cases hd)))
def cl_50354 : CNF.NClause := [(53,true),(44,false),(37,false),(109,true)]
theorem der_50354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50354 :=
  CNF.rup_sound cl_50354 [cl_31756,cl_49957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31756 v h) (hints_cons _ _ _ (der_49957 v h) (by intro d hd; cases hd)))
def cl_50356 : CNF.NClause := [(57,false),(42,false),(114,true),(36,true)]
theorem der_50356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50356 :=
  CNF.rup_sound cl_50356 [cl_31769,cl_49862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31769 v h) (hints_cons _ _ _ (der_49862 v h) (by intro d hd; cases hd)))
def cl_50357 : CNF.NClause := [(57,false),(114,true),(36,false),(42,true)]
theorem der_50357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50357 :=
  CNF.rup_sound cl_50357 [cl_31770,cl_50024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31770 v h) (hints_cons _ _ _ (der_50024 v h) (by intro d hd; cases hd)))
def cl_50359 : CNF.NClause := [(114,true),(42,false),(36,false),(54,true)]
theorem der_50359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50359 :=
  CNF.rup_sound cl_50359 [cl_31780,cl_49862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31780 v h) (hints_cons _ _ _ (der_49862 v h) (by intro d hd; cases hd)))
def cl_50361 : CNF.NClause := [(110,true),(33,false),(46,true),(45,false)]
theorem der_50361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50361 :=
  CNF.rup_sound cl_50361 [cl_31800,cl_49850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31800 v h) (hints_cons _ _ _ (der_49850 v h) (by intro d hd; cases hd)))
def cl_50364 : CNF.NClause := [(98,true),(52,false),(54,false),(55,false)]
theorem der_50364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50364 :=
  CNF.rup_sound cl_50364 [cl_31823,cl_50025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31823 v h) (hints_cons _ _ _ (der_50025 v h) (by intro d hd; cases hd)))
def cl_50365 : CNF.NClause := [(98,true),(55,false),(54,false),(52,true)]
theorem der_50365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50365 :=
  CNF.rup_sound cl_50365 [cl_31824,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31824 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50366 : CNF.NClause := [(98,true),(55,false),(61,true),(53,false)]
theorem der_50366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50366 :=
  CNF.rup_sound cl_50366 [cl_31826,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31826 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50367 : CNF.NClause := [(98,true),(54,true),(52,false),(55,false)]
theorem der_50367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50367 :=
  CNF.rup_sound cl_50367 [cl_31827,cl_50064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31827 v h) (hints_cons _ _ _ (der_50064 v h) (by intro d hd; cases hd)))
def cl_50368 : CNF.NClause := [(98,true),(55,true),(52,false),(54,false)]
theorem der_50368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50368 :=
  CNF.rup_sound cl_50368 [cl_31830,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31830 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50369 : CNF.NClause := [(98,true),(52,false),(53,false),(61,true)]
theorem der_50369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50369 :=
  CNF.rup_sound cl_50369 [cl_31831,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31831 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50370 : CNF.NClause := [(100,true),(42,false),(33,false),(58,true)]
theorem der_50370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50370 :=
  CNF.rup_sound cl_50370 [cl_31853,cl_49863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31853 v h) (hints_cons _ _ _ (der_49863 v h) (by intro d hd; cases hd)))
def cl_50371 : CNF.NClause := [(101,true),(34,false),(45,true),(37,false)]
theorem der_50371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50371 :=
  CNF.rup_sound cl_50371 [cl_31856,cl_43208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31856 v h) (hints_cons _ _ _ (der_43208 v h) (by intro d hd; cases hd)))
def cl_50372 : CNF.NClause := [(108,true),(49,true),(46,false),(47,false)]
theorem der_50372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50372 :=
  CNF.rup_sound cl_50372 [cl_31873,cl_50300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31873 v h) (hints_cons _ _ _ (der_50300 v h) (by intro d hd; cases hd)))
def cl_50373 : CNF.NClause := [(119,true),(31,true),(48,false),(44,false)]
theorem der_50373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50373 :=
  CNF.rup_sound cl_50373 [cl_35388,cl_49745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35388 v h) (hints_cons _ _ _ (der_49745 v h) (by intro d hd; cases hd)))
def cl_50374 : CNF.NClause := [(119,true),(31,true),(48,false),(40,false)]
theorem der_50374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50374 :=
  CNF.rup_sound cl_50374 [cl_31893,cl_49584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31893 v h) (hints_cons _ _ _ (der_49584 v h) (by intro d hd; cases hd)))
def cl_50375 : CNF.NClause := [(102,true),(38,true),(44,false),(57,false)]
theorem der_50375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50375 :=
  CNF.rup_sound cl_50375 [cl_31933,cl_38847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31933 v h) (hints_cons _ _ _ (der_38847 v h) (by intro d hd; cases hd)))
def cl_50376 : CNF.NClause := [(102,true),(51,false),(44,false),(32,true)]
theorem der_50376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50376 :=
  CNF.rup_sound cl_50376 [cl_31940,cl_35307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31940 v h) (hints_cons _ _ _ (der_35307 v h) (by intro d hd; cases hd)))
def cl_50377 : CNF.NClause := [(102,true),(50,false),(38,false),(44,true)]
theorem der_50377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50377 :=
  CNF.rup_sound cl_50377 [cl_31944,cl_49619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31944 v h) (hints_cons _ _ _ (der_49619 v h) (by intro d hd; cases hd)))
def cl_50378 : CNF.NClause := [(50,true),(38,false),(102,true),(44,false)]
theorem der_50378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50378 :=
  CNF.rup_sound cl_50378 [cl_31945,cl_42952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31945 v h) (hints_cons _ _ _ (der_42952 v h) (by intro d hd; cases hd)))
def cl_50381 : CNF.NClause := [(59,false),(112,true),(43,false),(40,true)]
theorem der_50381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50381 :=
  CNF.rup_sound cl_50381 [cl_31982,cl_49939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31982 v h) (hints_cons _ _ _ (der_49939 v h) (by intro d hd; cases hd)))
def cl_50382 : CNF.NClause := [(59,false),(40,false),(54,true),(112,true)]
theorem der_50382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50382 :=
  CNF.rup_sound cl_50382 [cl_31983,cl_43031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31983 v h) (hints_cons _ _ _ (der_43031 v h) (by intro d hd; cases hd)))
def cl_50383 : CNF.NClause := [(112,true),(46,true),(43,false),(40,false)]
theorem der_50383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50383 :=
  CNF.rup_sound cl_50383 [cl_31994,cl_47374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31994 v h) (hints_cons _ _ _ (der_47374 v h) (by intro d hd; cases hd)))
def cl_50384 : CNF.NClause := [(60,false),(36,true),(53,false),(117,true)]
theorem der_50384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50384 :=
  CNF.rup_sound cl_50384 [cl_32001,cl_49632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32001 v h) (hints_cons _ _ _ (der_49632 v h) (by intro d hd; cases hd)))
def cl_50385 : CNF.NClause := [(60,false),(36,true),(49,false),(117,true)]
theorem der_50385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50385 :=
  CNF.rup_sound cl_50385 [cl_32005,cl_49632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32005 v h) (hints_cons _ _ _ (der_49632 v h) (by intro d hd; cases hd)))
def cl_50386 : CNF.NClause := [(36,true),(45,false),(117,true),(49,false)]
theorem der_50386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50386 :=
  CNF.rup_sound cl_50386 [cl_32017,cl_42478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32017 v h) (hints_cons _ _ _ (der_42478 v h) (by intro d hd; cases hd)))
def cl_50387 : CNF.NClause := [(45,true),(36,false),(49,false),(117,true)]
theorem der_50387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50387 :=
  CNF.rup_sound cl_50387 [cl_32018,cl_49528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32018 v h) (hints_cons _ _ _ (der_49528 v h) (by intro d hd; cases hd)))
def cl_50388 : CNF.NClause := [(26,false),(15,false),(2,true),(79,true)]
theorem der_50388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50388 :=
  CNF.rup_sound cl_50388 [cl_29816,cl_50133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29816 v h) (hints_cons _ _ _ (der_50133 v h) (by intro d hd; cases hd)))
def cl_50389 : CNF.NClause := [(7,true),(71,true),(13,false),(26,false)]
theorem der_50389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50389 :=
  CNF.rup_sound cl_50389 [cl_35242,cl_39345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35242 v h) (hints_cons _ _ _ (der_39345 v h) (by intro d hd; cases hd)))
def cl_50391 : CNF.NClause := [(5,false),(12,true),(27,false),(85,true)]
theorem der_50391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50391 :=
  CNF.rup_sound cl_50391 [cl_35468,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35468 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_50392 : CNF.NClause := [(5,false),(86,true),(1,true),(22,false)]
theorem der_50392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50392 :=
  CNF.rup_sound cl_50392 [cl_35196,cl_45685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35196 v h) (hints_cons _ _ _ (der_45685 v h) (by intro d hd; cases hd)))
def cl_50393 : CNF.NClause := [(8,false),(15,false),(79,true),(21,true)]
theorem der_50393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50393 :=
  CNF.rup_sound cl_50393 [cl_29819,cl_49770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29819 v h) (hints_cons _ _ _ (der_49770 v h) (by intro d hd; cases hd)))
def cl_50394 : CNF.NClause := [(16,false),(9,false),(10,true),(75,true)]
theorem der_50394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50394 :=
  CNF.rup_sound cl_50394 [cl_35222,cl_49972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35222 v h) (hints_cons _ _ _ (der_49972 v h) (by intro d hd; cases hd)))
def cl_50395 : CNF.NClause := [(6,false),(14,true),(17,false),(70,true)]
theorem der_50395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50395 :=
  CNF.rup_sound cl_50395 [cl_35154,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35154 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_50397 : CNF.NClause := [(4,false),(28,false),(73,true),(7,true)]
theorem der_50397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50397 :=
  CNF.rup_sound cl_50397 [cl_35728,cl_49883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35728 v h) (hints_cons _ _ _ (der_49883 v h) (by intro d hd; cases hd)))
def cl_50398 : CNF.NClause := [(4,false),(18,false),(73,true),(7,true)]
theorem der_50398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50398 :=
  CNF.rup_sound cl_50398 [cl_35816,cl_49883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35816 v h) (hints_cons _ _ _ (der_49883 v h) (by intro d hd; cases hd)))
def cl_50399 : CNF.NClause := [(23,false),(9,false),(1,true),(81,true)]
theorem der_50399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50399 :=
  CNF.rup_sound cl_50399 [cl_35421,cl_50008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35421 v h) (hints_cons _ _ _ (der_50008 v h) (by intro d hd; cases hd)))
def cl_50400 : CNF.NClause := [(96,true),(34,true),(44,false),(39,false)]
theorem der_50400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50400 :=
  CNF.rup_sound cl_50400 [cl_35481,cl_35627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35481 v h) (hints_cons _ _ _ (der_35627 v h) (by intro d hd; cases hd)))
def cl_50402 : CNF.NClause := [(33,true),(55,false),(115,true),(44,false)]
theorem der_50402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50402 :=
  CNF.rup_sound cl_50402 [cl_35237,cl_49853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35237 v h) (hints_cons _ _ _ (der_49853 v h) (by intro d hd; cases hd)))
def cl_50404 : CNF.NClause := [(58,true),(53,false),(109,true),(44,false)]
theorem der_50404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50404 :=
  CNF.rup_sound cl_50404 [cl_35752,cl_35634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35752 v h) (hints_cons _ _ _ (der_35634 v h) (by intro d hd; cases hd)))
def cl_50405 : CNF.NClause := [(42,false),(53,false),(39,true),(121,true)]
theorem der_50405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50405 :=
  CNF.rup_sound cl_50405 [cl_35316,cl_50056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35316 v h) (hints_cons _ _ _ (der_50056 v h) (by intro d hd; cases hd)))
def cl_50406 : CNF.NClause := [(117,true),(36,false),(53,false),(45,true)]
theorem der_50406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50406 :=
  CNF.rup_sound cl_50406 [cl_35317,cl_42478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35317 v h) (hints_cons _ _ _ (der_42478 v h) (by intro d hd; cases hd)))
def cl_50408 : CNF.NClause := [(31,true),(52,false),(44,false),(119,true)]
theorem der_50408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50408 :=
  CNF.rup_sound cl_50408 [cl_35449,cl_49745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35449 v h) (hints_cons _ _ _ (der_49745 v h) (by intro d hd; cases hd)))
def cl_50409 : CNF.NClause := [(17,true),(70,true),(20,false),(3,false)]
theorem der_50409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50409 :=
  CNF.rup_sound cl_50409 [cl_29832,cl_50188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29832 v h) (hints_cons _ _ _ (der_50188 v h) (by intro d hd; cases hd)))
def cl_50410 : CNF.NClause := [(1,true),(20,false),(71,true),(13,false)]
theorem der_50410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50410 :=
  CNF.rup_sound cl_50410 [cl_35094,cl_50123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35094 v h) (hints_cons _ _ _ (der_50123 v h) (by intro d hd; cases hd)))
def cl_50412 : CNF.NClause := [(78,true),(6,false),(22,true),(4,false)]
theorem der_50412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50412 :=
  CNF.rup_sound cl_50412 [cl_35810,cl_37513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35810 v h) (hints_cons _ _ _ (der_37513 v h) (by intro d hd; cases hd)))
def cl_50413 : CNF.NClause := [(8,false),(21,false),(79,true),(14,true)]
theorem der_50413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50413 :=
  CNF.rup_sound cl_50413 [cl_29828,cl_42466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29828 v h) (hints_cons _ _ _ (der_42466 v h) (by intro d hd; cases hd)))
def cl_50417 : CNF.NClause := [(67,true),(146,true),(23,false),(147,false)]
theorem der_50417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50417 :=
  CNF.rup_sound cl_50417 [cl_35510,cl_49785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35510 v h) (hints_cons _ _ _ (der_49785 v h) (by intro d hd; cases hd)))
def cl_50418 : CNF.NClause := [(23,false),(7,true),(16,false),(89,true)]
theorem der_50418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50418 :=
  CNF.rup_sound cl_50418 [cl_36337,cl_49783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36337 v h) (hints_cons _ _ _ (der_49783 v h) (by intro d hd; cases hd)))
def cl_50419 : CNF.NClause := [(15,true),(9,false),(12,false),(81,true)]
theorem der_50419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50419 :=
  CNF.rup_sound cl_50419 [cl_37243,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37243 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_50421 : CNF.NClause := [(78,true),(15,false),(4,false),(6,false)]
theorem der_50421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50421 :=
  CNF.rup_sound cl_50421 [cl_36189,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36189 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50423 : CNF.NClause := [(5,false),(1,true),(14,false),(86,true)]
theorem der_50423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50423 :=
  CNF.rup_sound cl_50423 [cl_36496,cl_43136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36496 v h) (hints_cons _ _ _ (der_43136 v h) (by intro d hd; cases hd)))
def cl_50424 : CNF.NClause := [(7,true),(19,false),(71,true),(20,false)]
theorem der_50424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50424 :=
  CNF.rup_sound cl_50424 [cl_36056,cl_39541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36056 v h) (hints_cons _ _ _ (der_39541 v h) (by intro d hd; cases hd)))
def cl_50425 : CNF.NClause := [(3,true),(70,false),(87,false),(34,false)]
theorem der_50425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50425 :=
  CNF.rup_sound cl_50425 [cl_39286,cl_49393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39286 v h) (hints_cons _ _ _ (der_49393 v h) (by intro d hd; cases hd)))
def cl_50426 : CNF.NClause := [(77,true),(15,false),(17,true),(914,false)]
theorem der_50426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50426 :=
  CNF.rup_sound cl_50426 [cl_36511,cl_36157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36511 v h) (hints_cons _ _ _ (der_36157 v h) (by intro d hd; cases hd)))
def cl_50427 : CNF.NClause := [(67,true),(24,false),(23,true),(923,false)]
theorem der_50427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50427 :=
  CNF.rup_sound cl_50427 [cl_36595,cl_49891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36595 v h) (hints_cons _ _ _ (der_49891 v h) (by intro d hd; cases hd)))
def cl_50428 : CNF.NClause := [(67,true),(146,false),(145,true),(22,false)]
theorem der_50428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50428 :=
  CNF.rup_sound cl_50428 [cl_36648,cl_35629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36648 v h) (hints_cons _ _ _ (der_35629 v h) (by intro d hd; cases hd)))
def cl_50429 : CNF.NClause := [(32,false),(112,true),(40,false),(43,true)]
theorem der_50429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50429 :=
  CNF.rup_sound cl_50429 [cl_37949,cl_48868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37949 v h) (hints_cons _ _ _ (der_48868 v h) (by intro d hd; cases hd)))
def cl_50430 : CNF.NClause := [(105,true),(54,true),(41,false),(37,false)]
theorem der_50430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50430 :=
  CNF.rup_sound cl_50430 [cl_38175,cl_37492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38175 v h) (hints_cons _ _ _ (der_37492 v h) (by intro d hd; cases hd)))
def cl_50431 : CNF.NClause := [(36,false),(43,false),(116,true),(52,true)]
theorem der_50431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50431 :=
  CNF.rup_sound cl_50431 [cl_37691,cl_49955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37691 v h) (hints_cons _ _ _ (der_49955 v h) (by intro d hd; cases hd)))
def cl_50432 : CNF.NClause := [(57,true),(45,false),(110,true),(33,false)]
theorem der_50432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50432 :=
  CNF.rup_sound cl_50432 [cl_37163,cl_49894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37163 v h) (hints_cons _ _ _ (der_49894 v h) (by intro d hd; cases hd)))
def cl_50434 : CNF.NClause := [(98,true),(55,false),(52,true),(53,false)]
theorem der_50434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50434 :=
  CNF.rup_sound cl_50434 [cl_36882,cl_49522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36882 v h) (hints_cons _ _ _ (der_49522 v h) (by intro d hd; cases hd)))
def cl_50435 : CNF.NClause := [(36,false),(49,true),(117,true),(45,false)]
theorem der_50435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50435 :=
  CNF.rup_sound cl_50435 [cl_36498,cl_49528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36498 v h) (hints_cons _ _ _ (der_49528 v h) (by intro d hd; cases hd)))
def cl_50438 : CNF.NClause := [(48,true),(40,false),(52,false),(119,true)]
theorem der_50438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50438 :=
  CNF.rup_sound cl_50438 [cl_36256,cl_50237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36256 v h) (hints_cons _ _ _ (der_50237 v h) (by intro d hd; cases hd)))
def cl_50440 : CNF.NClause := [(91,true),(1060,false),(18,true),(6,false)]
theorem der_50440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50440 :=
  CNF.rup_sound cl_50440 [cl_36043,cl_37342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36043 v h) (hints_cons _ _ _ (der_37342 v h) (by intro d hd; cases hd)))
def cl_50441 : CNF.NClause := [(60,false),(111,true),(42,false),(55,true)]
theorem der_50441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50441 :=
  CNF.rup_sound cl_50441 [cl_36887,cl_49846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36887 v h) (hints_cons _ _ _ (der_49846 v h) (by intro d hd; cases hd)))
def cl_50442 : CNF.NClause := [(76,true),(17,false),(8,false),(10,true)]
theorem der_50442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50442 :=
  CNF.rup_sound cl_50442 [cl_36480,cl_50168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36480 v h) (hints_cons _ _ _ (der_50168 v h) (by intro d hd; cases hd)))
def cl_50447 : CNF.NClause := [(14,false),(7,true),(89,true),(138,true)]
theorem der_50447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50447 :=
  CNF.rup_sound cl_50447 [cl_36725,cl_49783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36725 v h) (hints_cons _ _ _ (der_49783 v h) (by intro d hd; cases hd)))
def cl_50448 : CNF.NClause := [(88,true),(133,true),(137,true),(9,false)]
theorem der_50448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50448 :=
  CNF.rup_sound cl_50448 [cl_36238,cl_49835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36238 v h) (hints_cons _ _ _ (der_49835 v h) (by intro d hd; cases hd)))
def cl_50451 : CNF.NClause := [(37,false),(53,false),(46,true),(109,true)]
theorem der_50451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50451 :=
  CNF.rup_sound cl_50451 [cl_37303,cl_37286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37303 v h) (hints_cons _ _ _ (der_37286 v h) (by intro d hd; cases hd)))
def cl_50452 : CNF.NClause := [(114,true),(48,false),(54,true),(35,false)]
theorem der_50452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50452 :=
  CNF.rup_sound cl_50452 [cl_36098,cl_37440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36098 v h) (hints_cons _ _ _ (der_37440 v h) (by intro d hd; cases hd)))
def cl_50453 : CNF.NClause := [(59,false),(104,true),(35,false),(41,true)]
theorem der_50453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50453 :=
  CNF.rup_sound cl_50453 [cl_35860,cl_49859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35860 v h) (hints_cons _ _ _ (der_49859 v h) (by intro d hd; cases hd)))
def cl_50454 : CNF.NClause := [(26,false),(91,true),(12,true),(24,false)]
theorem der_50454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50454 :=
  CNF.rup_sound cl_50454 [cl_38897,cl_49760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38897 v h) (hints_cons _ _ _ (der_49760 v h) (by intro d hd; cases hd)))
def cl_50455 : CNF.NClause := [(89,true),(14,false),(16,false),(7,true)]
theorem der_50455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50455 :=
  CNF.rup_sound cl_50455 [cl_39039,cl_49762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39039 v h) (hints_cons _ _ _ (der_49762 v h) (by intro d hd; cases hd)))
def cl_50456 : CNF.NClause := [(15,true),(81,true),(1,false),(23,false)]
theorem der_50456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50456 :=
  CNF.rup_sound cl_50456 [cl_38927,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38927 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_50457 : CNF.NClause := [(70,true),(6,true),(28,false),(14,false)]
theorem der_50457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50457 :=
  CNF.rup_sound cl_50457 [cl_38544,cl_49686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38544 v h) (hints_cons _ _ _ (der_49686 v h) (by intro d hd; cases hd)))
def cl_50458 : CNF.NClause := [(88,true),(29,false),(13,false),(17,true)]
theorem der_50458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50458 :=
  CNF.rup_sound cl_50458 [cl_38848,cl_35284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38848 v h) (hints_cons _ _ _ (der_35284 v h) (by intro d hd; cases hd)))
def cl_50459 : CNF.NClause := [(5,false),(12,true),(85,true),(1059,false)]
theorem der_50459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50459 :=
  CNF.rup_sound cl_50459 [cl_38628,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38628 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_50460 : CNF.NClause := [(128,false),(63,true),(138,true),(133,true)]
theorem der_50460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50460 :=
  CNF.rup_sound cl_50460 [cl_40213,cl_15770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40213 v h) (hints_cons _ _ _ (der_15770 v h) (by intro d hd; cases hd)))
def cl_50462 : CNF.NClause := [(106,true),(41,false),(40,true),(57,false)]
theorem der_50462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50462 :=
  CNF.rup_sound cl_50462 [cl_38657,cl_50017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38657 v h) (hints_cons _ _ _ (der_50017 v h) (by intro d hd; cases hd)))
def cl_50463 : CNF.NClause := [(32,false),(112,true),(43,true),(54,false)]
theorem der_50463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50463 :=
  CNF.rup_sound cl_50463 [cl_38459,cl_47068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38459 v h) (hints_cons _ _ _ (der_47068 v h) (by intro d hd; cases hd)))
def cl_50464 : CNF.NClause := [(2,false),(64,true),(126,false),(131,true)]
theorem der_50464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50464 :=
  CNF.rup_sound cl_50464 [cl_40347,cl_37368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40347 v h) (hints_cons _ _ _ (der_37368 v h) (by intro d hd; cases hd)))
def cl_50465 : CNF.NClause := [(36,false),(34,false),(116,true),(43,true)]
theorem der_50465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50465 :=
  CNF.rup_sound cl_50465 [cl_39379,cl_49848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39379 v h) (hints_cons _ _ _ (der_49848 v h) (by intro d hd; cases hd)))
def cl_50466 : CNF.NClause := [(17,false),(6,true),(3,false),(70,true)]
theorem der_50466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50466 :=
  CNF.rup_sound cl_50466 [cl_40130,cl_50163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40130 v h) (hints_cons _ _ _ (der_50163 v h) (by intro d hd; cases hd)))
def cl_50467 : CNF.NClause := [(9,true),(15,false),(1,false),(81,true)]
theorem der_50467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50467 :=
  CNF.rup_sound cl_50467 [cl_38718,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38718 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_50468 : CNF.NClause := [(3,true),(22,false),(10,false),(75,true)]
theorem der_50468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50468 :=
  CNF.rup_sound cl_50468 [cl_39331,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39331 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_50469 : CNF.NClause := [(138,false),(6,true),(70,true),(14,false)]
theorem der_50469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50469 :=
  CNF.rup_sound cl_50469 [cl_38706,cl_49773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38706 v h) (hints_cons _ _ _ (der_49773 v h) (by intro d hd; cases hd)))
def cl_50470 : CNF.NClause := [(88,true),(908,false),(912,true),(9,false)]
theorem der_50470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50470 :=
  CNF.rup_sound cl_50470 [cl_40896,cl_49835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40896 v h) (hints_cons _ _ _ (der_49835 v h) (by intro d hd; cases hd)))
def cl_50472 : CNF.NClause := [(45,false),(53,true),(117,true),(36,false)]
theorem der_50472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50472 :=
  CNF.rup_sound cl_50472 [cl_38322,cl_49896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38322 v h) (hints_cons _ _ _ (der_49896 v h) (by intro d hd; cases hd)))
def cl_50473 : CNF.NClause := [(147,true),(23,false),(89,true),(7,true)]
theorem der_50473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50473 :=
  CNF.rup_sound cl_50473 [cl_41905,cl_49783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41905 v h) (hints_cons _ _ _ (der_49783 v h) (by intro d hd; cases hd)))
def cl_50474 : CNF.NClause := [(54,false),(58,false),(31,true),(120,true)]
theorem der_50474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50474 :=
  CNF.rup_sound cl_50474 [cl_42719,cl_44945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42719 v h) (hints_cons _ _ _ (der_44945 v h) (by intro d hd; cases hd)))
def cl_50478 : CNF.NClause := [(75,true),(10,false),(26,false),(9,true)]
theorem der_50478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50478 :=
  CNF.rup_sound cl_50478 [cl_41214,cl_40899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41214 v h) (hints_cons _ _ _ (der_40899 v h) (by intro d hd; cases hd)))
def cl_50479 : CNF.NClause := [(81,true),(23,false),(9,true),(1,false)]
theorem der_50479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50479 :=
  CNF.rup_sound cl_50479 [cl_41143,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41143 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_50480 : CNF.NClause := [(136,false),(135,true),(72,true),(13,true)]
theorem der_50480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50480 :=
  CNF.rup_sound cl_50480 [cl_43330,cl_48382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43330 v h) (hints_cons _ _ _ (der_48382 v h) (by intro d hd; cases hd)))
def cl_50482 : CNF.NClause := [(146,true),(17,false),(64,true),(141,false)]
theorem der_50482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50482 :=
  CNF.rup_sound cl_50482 [cl_43755,cl_49782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43755 v h) (hints_cons _ _ _ (der_49782 v h) (by intro d hd; cases hd)))
def cl_50485 : CNF.NClause := [(58,false),(100,true),(51,false),(40,true)]
theorem der_50485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50485 :=
  CNF.rup_sound cl_50485 [cl_43086,cl_43017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43086 v h) (hints_cons _ _ _ (der_43017 v h) (by intro d hd; cases hd)))
def cl_50486 : CNF.NClause := [(4,false),(6,true),(78,true),(22,false)]
theorem der_50486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50486 :=
  CNF.rup_sound cl_50486 [cl_41219,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41219 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_50488 : CNF.NClause := [(58,false),(44,false),(109,true),(53,true)]
theorem der_50488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50488 :=
  CNF.rup_sound cl_50488 [cl_43350,cl_43179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43350 v h) (hints_cons _ _ _ (der_43179 v h) (by intro d hd; cases hd)))
def cl_50489 : CNF.NClause := [(74,true),(10,false),(23,false),(19,true)]
theorem der_50489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50489 :=
  CNF.rup_sound cl_50489 [cl_42843,cl_44863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42843 v h) (hints_cons _ _ _ (der_44863 v h) (by intro d hd; cases hd)))
def cl_50490 : CNF.NClause := [(112,true),(43,false),(59,false),(40,true)]
theorem der_50490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50490 :=
  CNF.rup_sound cl_50490 [cl_41360,cl_49940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41360 v h) (hints_cons _ _ _ (der_49940 v h) (by intro d hd; cases hd)))
def cl_50491 : CNF.NClause := [(59,false),(52,true),(104,true),(35,false)]
theorem der_50491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50491 :=
  CNF.rup_sound cl_50491 [cl_42986,cl_40814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42986 v h) (hints_cons _ _ _ (der_40814 v h) (by intro d hd; cases hd)))
def cl_50492 : CNF.NClause := [(120,true),(58,false),(31,true),(47,false)]
theorem der_50492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50492 :=
  CNF.rup_sound cl_50492 [cl_43640,cl_44945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43640 v h) (hints_cons _ _ _ (der_44945 v h) (by intro d hd; cases hd)))
def cl_50493 : CNF.NClause := [(141,true),(145,true),(17,false),(88,true)]
theorem der_50493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50493 :=
  CNF.rup_sound cl_50493 [cl_43232,cl_49835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43232 v h) (hints_cons _ _ _ (der_49835 v h) (by intro d hd; cases hd)))
def cl_50495 : CNF.NClause := [(52,false),(54,false),(53,true),(98,true)]
theorem der_50495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50495 :=
  CNF.rup_sound cl_50495 [cl_42491,cl_50025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42491 v h) (hints_cons _ _ _ (der_50025 v h) (by intro d hd; cases hd)))
def cl_50496 : CNF.NClause := [(98,true),(54,false),(61,true),(52,false)]
theorem der_50496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50496 :=
  CNF.rup_sound cl_50496 [cl_43695,cl_50364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43695 v h) (hints_cons _ _ _ (der_50364 v h) (by intro d hd; cases hd)))
def cl_50497 : CNF.NClause := [(4,false),(16,false),(68,true),(8,true)]
theorem der_50497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50497 :=
  CNF.rup_sound cl_50497 [cl_41565,cl_49989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41565 v h) (hints_cons _ _ _ (der_49989 v h) (by intro d hd; cases hd)))
def cl_50499 : CNF.NClause := [(75,true),(9,true),(3,false),(26,false)]
theorem der_50499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50499 :=
  CNF.rup_sound cl_50499 [cl_44988,cl_40899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44988 v h) (hints_cons _ _ _ (der_40899 v h) (by intro d hd; cases hd)))
def cl_50500 : CNF.NClause := [(136,false),(12,false),(72,true),(13,true)]
theorem der_50500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50500 :=
  CNF.rup_sound cl_50500 [cl_44869,cl_46318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44869 v h) (hints_cons _ _ _ (der_46318 v h) (by intro d hd; cases hd)))
def cl_50501 : CNF.NClause := [(37,false),(46,false),(53,true),(109,true)]
theorem der_50501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50501 :=
  CNF.rup_sound cl_50501 [cl_46743,cl_49996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46743 v h) (hints_cons _ _ _ (der_49996 v h) (by intro d hd; cases hd)))
def cl_50502 : CNF.NClause := [(138,false),(29,true),(129,true),(86,true)]
theorem der_50502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50502 :=
  CNF.rup_sound cl_50502 [cl_45961,cl_15780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45961 v h) (hints_cons _ _ _ (der_15780 v h) (by intro d hd; cases hd)))
def cl_50503 : CNF.NClause := [(116,true),(36,false),(50,false),(52,true)]
theorem der_50503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50503 :=
  CNF.rup_sound cl_50503 [cl_46881,cl_49981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46881 v h) (hints_cons _ _ _ (der_49981 v h) (by intro d hd; cases hd)))
def cl_50504 : CNF.NClause := [(24,true),(84,true),(16,false),(2,false)]
theorem der_50504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50504 :=
  CNF.rup_sound cl_50504 [cl_44944,cl_42738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44944 v h) (hints_cons _ _ _ (der_42738 v h) (by intro d hd; cases hd)))
def cl_50506 : CNF.NClause := [(29,false),(86,true),(14,false),(1,true)]
theorem der_50506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50506 :=
  CNF.rup_sound cl_50506 [cl_44199,cl_42713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44199 v h) (hints_cons _ _ _ (der_42713 v h) (by intro d hd; cases hd)))
def cl_50507 : CNF.NClause := [(53,true),(109,true),(44,false),(46,false)]
theorem der_50507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50507 :=
  CNF.rup_sound cl_50507 [cl_46346,cl_49725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46346 v h) (hints_cons _ _ _ (der_49725 v h) (by intro d hd; cases hd)))
def cl_50508 : CNF.NClause := [(84,true),(28,true),(1067,false),(13,false)]
theorem der_50508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50508 :=
  CNF.rup_sound cl_50508 [cl_45474,cl_48778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45474 v h) (hints_cons _ _ _ (der_48778 v h) (by intro d hd; cases hd)))
def cl_50509 : CNF.NClause := [(22,true),(1068,false),(14,false),(86,true)]
theorem der_50509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50509 :=
  CNF.rup_sound cl_50509 [cl_44296,cl_44225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44296 v h) (hints_cons _ _ _ (der_44225 v h) (by intro d hd; cases hd)))
def cl_50510 : CNF.NClause := [(99,true),(51,true),(47,false),(43,false)]
theorem der_50510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50510 :=
  CNF.rup_sound cl_50510 [cl_46526,cl_47014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46526 v h) (hints_cons _ _ _ (der_47014 v h) (by intro d hd; cases hd)))
def cl_50511 : CNF.NClause := [(579,false),(66,true),(21,false),(14,true)]
theorem der_50511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50511 :=
  CNF.rup_sound cl_50511 [cl_45221,cl_43827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45221 v h) (hints_cons _ _ _ (der_43827 v h) (by intro d hd; cases hd)))
def cl_50513 : CNF.NClause := [(31,true),(38,false),(47,false),(120,true)]
theorem der_50513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50513 :=
  CNF.rup_sound cl_50513 [cl_47306,cl_50247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47306 v h) (hints_cons _ _ _ (der_50247 v h) (by intro d hd; cases hd)))
def cl_50514 : CNF.NClause := [(135,false),(11,false),(72,true),(137,true)]
theorem der_50514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50514 :=
  CNF.rup_sound cl_50514 [cl_47308,cl_49816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47308 v h) (hints_cons _ _ _ (der_49816 v h) (by intro d hd; cases hd)))
def cl_50515 : CNF.NClause := [(16,false),(2,true),(5,false),(84,true)]
theorem der_50515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50515 :=
  CNF.rup_sound cl_50515 [cl_47336,cl_42738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47336 v h) (hints_cons _ _ _ (der_42738 v h) (by intro d hd; cases hd)))
def cl_50516 : CNF.NClause := [(60,false),(36,false),(117,true),(32,true)]
theorem der_50516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50516 :=
  CNF.rup_sound cl_50516 [cl_47403,cl_49528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47403 v h) (hints_cons _ _ _ (der_49528 v h) (by intro d hd; cases hd)))
def cl_50517 : CNF.NClause := [(60,false),(105,true),(33,true),(54,false)]
theorem der_50517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50517 :=
  CNF.rup_sound cl_50517 [cl_47463,cl_49849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47463 v h) (hints_cons _ _ _ (der_49849 v h) (by intro d hd; cases hd)))
def cl_50518 : CNF.NClause := [(57,true),(38,false),(102,true),(51,false)]
theorem der_50518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50518 :=
  CNF.rup_sound cl_50518 [cl_47714,cl_44369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47714 v h) (hints_cons _ _ _ (der_44369 v h) (by intro d hd; cases hd)))
def cl_50521 : CNF.NClause := [(22,false),(90,true),(146,true),(143,true)]
theorem der_50521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50521 :=
  CNF.rup_sound cl_50521 [cl_48251,cl_49805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48251 v h) (hints_cons _ _ _ (der_49805 v h) (by intro d hd; cases hd)))
def cl_50523 : CNF.NClause := [(83,true),(128,false),(26,true),(11,true)]
theorem der_50523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50523 :=
  CNF.rup_sound cl_50523 [cl_48562,cl_15770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48562 v h) (hints_cons _ _ _ (der_15770 v h) (by intro d hd; cases hd)))
def cl_50524 : CNF.NClause := [(24,false),(10,false),(1,true),(76,true)]
theorem der_50524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50524 :=
  CNF.rup_sound cl_50524 [cl_48594,cl_50191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48594 v h) (hints_cons _ _ _ (der_50191 v h) (by intro d hd; cases hd)))
def cl_50525 : CNF.NClause := [(65,true),(13,false),(912,true),(917,true)]
theorem der_50525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50525 :=
  CNF.rup_sound cl_50525 [cl_48617,cl_49766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48617 v h) (hints_cons _ _ _ (der_49766 v h) (by intro d hd; cases hd)))
def cl_50526 : CNF.NClause := [(64,true),(2,false),(906,true),(901,true)]
theorem der_50526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50526 :=
  CNF.rup_sound cl_50526 [cl_48663,cl_48797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48663 v h) (hints_cons _ _ _ (der_48797 v h) (by intro d hd; cases hd)))
def cl_50529 : CNF.NClause := [(17,false),(10,false),(1,true),(76,true)]
theorem der_50529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50529 :=
  CNF.rup_sound cl_50529 [cl_48807,cl_50191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48807 v h) (hints_cons _ _ _ (der_50191 v h) (by intro d hd; cases hd)))
def cl_50530 : CNF.NClause := [(73,true),(28,false),(21,false),(18,true)]
theorem der_50530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50530 :=
  CNF.rup_sound cl_50530 [cl_48844,cl_50010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48844 v h) (hints_cons _ _ _ (der_50010 v h) (by intro d hd; cases hd)))
def cl_50531 : CNF.NClause := [(70,true),(17,false),(6,false),(20,true)]
theorem der_50531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50531 :=
  CNF.rup_sound cl_50531 [cl_48873,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48873 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_50532 : CNF.NClause := [(3,true),(19,false),(21,false),(85,true)]
theorem der_50532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50532 :=
  CNF.rup_sound cl_50532 [cl_48875,cl_50131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48875 v h) (hints_cons _ _ _ (der_50131 v h) (by intro d hd; cases hd)))
def cl_50533 : CNF.NClause := [(73,true),(10,false),(21,false),(18,true)]
theorem der_50533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50533 :=
  CNF.rup_sound cl_50533 [cl_48876,cl_50010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48876 v h) (hints_cons _ _ _ (der_50010 v h) (by intro d hd; cases hd)))
def cl_50535 : CNF.NClause := [(1,false),(8,false),(10,true),(76,true)]
theorem der_50535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50535 :=
  CNF.rup_sound cl_50535 [cl_48906,cl_50166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48906 v h) (hints_cons _ _ _ (der_50166 v h) (by intro d hd; cases hd)))
def cl_50536 : CNF.NClause := [(20,true),(8,false),(12,false),(68,true)]
theorem der_50536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50536 :=
  CNF.rup_sound cl_50536 [cl_48921,cl_37249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48921 v h) (hints_cons _ _ _ (der_37249 v h) (by intro d hd; cases hd)))
def cl_50537 : CNF.NClause := [(85,true),(5,false),(926,true),(904,false)]
theorem der_50537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50537 :=
  CNF.rup_sound cl_50537 [cl_48994,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48994 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_50539 : CNF.NClause := [(90,true),(22,false),(1073,true),(1076,false)]
theorem der_50539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50539 :=
  CNF.rup_sound cl_50539 [cl_49107,cl_49813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49107 v h) (hints_cons _ _ _ (der_49813 v h) (by intro d hd; cases hd)))
def cl_50541 : CNF.NClause := [(70,true),(17,false),(28,false),(20,true)]
theorem der_50541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50541 :=
  CNF.rup_sound cl_50541 [cl_49408,cl_49686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49408 v h) (hints_cons _ _ _ (der_49686 v h) (by intro d hd; cases hd)))
def cl_50542 : CNF.NClause := [(73,true),(18,true),(28,false),(7,false)]
theorem der_50542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50542 :=
  CNF.rup_sound cl_50542 [cl_49409,cl_49532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49409 v h) (hints_cons _ _ _ (der_49532 v h) (by intro d hd; cases hd)))
def cl_50543 : CNF.NClause := [(3,true),(27,true),(85,true),(143,false)]
theorem der_50543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50543 :=
  CNF.rup_sound cl_50543 [cl_49500,cl_15792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49500 v h) (hints_cons _ _ _ (der_15792 v h) (by intro d hd; cases hd)))
def cl_50544 : CNF.NClause := [(79,false),(33,false),(69,true),(74,true)]
theorem der_50544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50544 :=
  CNF.rup_sound cl_50544 [cl_49692,cl_48905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49692 v h) (hints_cons _ _ _ (der_48905 v h) (by intro d hd; cases hd)))
def cl_50545 : CNF.NClause := [(84,false),(33,false),(69,true),(74,true)]
theorem der_50545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50545 :=
  CNF.rup_sound cl_50545 [cl_49693,cl_48905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49693 v h) (hints_cons _ _ _ (der_48905 v h) (by intro d hd; cases hd)))
def cl_50546 : CNF.NClause := [(64,false),(79,true),(69,true),(33,false)]
theorem der_50546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50546 :=
  CNF.rup_sound cl_50546 [cl_49696,cl_49995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49696 v h) (hints_cons _ _ _ (der_49995 v h) (by intro d hd; cases hd)))
def cl_50547 : CNF.NClause := [(37,false),(82,false),(78,false),(6,true)]
theorem der_50547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50547 :=
  CNF.rup_sound cl_50547 [cl_49704,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49704 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def chunk046 : List CNF.NClause := [cl_49913,cl_49914,cl_49915,cl_49916,cl_49917,cl_49918,cl_49920,cl_49921,cl_49922,cl_49923,cl_49924,cl_49926,cl_49927,cl_49928,cl_49930,cl_49931,cl_49932,cl_49933,cl_49934,cl_49935,cl_49936,cl_49938,cl_49939,cl_49940,cl_49943,cl_49945,cl_49946,cl_49947,cl_49949,cl_49950,cl_49951,cl_49952,cl_49953,cl_49954,cl_49955,cl_49956,cl_49957,cl_49958,cl_49960,cl_49961,cl_49962,cl_49963,cl_49964,cl_49965,cl_49966,cl_49967,cl_49968,cl_49969,cl_49970,cl_49971,cl_49972,cl_49973,cl_49974,cl_49975,cl_49976,cl_49977,cl_49978,cl_49979,cl_49980,cl_49981,cl_49982,cl_49983,cl_49984,cl_49986,cl_49987,cl_49988,cl_49989,cl_49990,cl_49991,cl_49992,cl_49993,cl_49994,cl_49995,cl_49996,cl_49997,cl_49998,cl_49999,cl_50000,cl_50001,cl_50002,cl_50003,cl_50005,cl_50006,cl_50008,cl_50009,cl_50010,cl_50011,cl_50012,cl_50015,cl_50016,cl_50017,cl_50020,cl_50021,cl_50022,cl_50024,cl_50025,cl_50026,cl_50027,cl_50028,cl_50029,cl_50031,cl_50032,cl_50033,cl_50034,cl_50035,cl_50036,cl_50037,cl_50040,cl_50041,cl_50042,cl_50043,cl_50044,cl_50046,cl_50047,cl_50048,cl_50049,cl_50050,cl_50051,cl_50052,cl_50053,cl_50055,cl_50056,cl_50057,cl_50059,cl_50060,cl_50063,cl_50064,cl_50065,cl_50066,cl_50067,cl_50068,cl_50070,cl_50071,cl_50073,cl_50074,cl_50076,cl_50077,cl_50078,cl_50079,cl_50080,cl_50081,cl_50082,cl_50083,cl_50085,cl_50086,cl_50087,cl_50088,cl_50089,cl_50091,cl_50092,cl_50093,cl_50094,cl_50096,cl_50097,cl_50098,cl_50099,cl_50100,cl_50101,cl_50102,cl_50104,cl_50105,cl_50106,cl_50107,cl_50109,cl_50110,cl_50111,cl_50112,cl_50113,cl_50114,cl_50116,cl_50117,cl_50118,cl_50119,cl_50120,cl_50121,cl_50122,cl_50123,cl_50124,cl_50125,cl_50127,cl_50128,cl_50129,cl_50131,cl_50133,cl_50134,cl_50135,cl_50136,cl_50137,cl_50138,cl_50139,cl_50140,cl_50141,cl_50142,cl_50143,cl_50144,cl_50145,cl_50146,cl_50148,cl_50149,cl_50150,cl_50152,cl_50153,cl_50154,cl_50155,cl_50156,cl_50157,cl_50158,cl_50159,cl_50160,cl_50161,cl_50162,cl_50163,cl_50164,cl_50165,cl_50166,cl_50167,cl_50168,cl_50169,cl_50170,cl_50171,cl_50172,cl_50173,cl_50174,cl_50175,cl_50176,cl_50177,cl_50178,cl_50179,cl_50180,cl_50181,cl_50182,cl_50184,cl_50185,cl_50186,cl_50187,cl_50188,cl_50190,cl_50191,cl_50192,cl_50193,cl_50194,cl_50195,cl_50196,cl_50198,cl_50199,cl_50200,cl_50201,cl_50202,cl_50203,cl_50205,cl_50206,cl_50207,cl_50208,cl_50209,cl_50210,cl_50211,cl_50212,cl_50213,cl_50215,cl_50216,cl_50217,cl_50218,cl_50219,cl_50220,cl_50221,cl_50222,cl_50225,cl_50226,cl_50229,cl_50230,cl_50231,cl_50232,cl_50233,cl_50237,cl_50240,cl_50241,cl_50244,cl_50247,cl_50248,cl_50249,cl_50250,cl_50257,cl_50265,cl_50266,cl_50267,cl_50268,cl_50269,cl_50270,cl_50271,cl_50272,cl_50273,cl_50274,cl_50275,cl_50276,cl_50277,cl_50279,cl_50280,cl_50281,cl_50282,cl_50283,cl_50284,cl_50285,cl_50286,cl_50288,cl_50289,cl_50290,cl_50291,cl_50293,cl_50294,cl_50295,cl_50297,cl_50298,cl_50299,cl_50300,cl_50301,cl_50302,cl_50305,cl_50306,cl_50309,cl_50310,cl_50313,cl_50316,cl_50317,cl_50320,cl_50321,cl_50322,cl_50323,cl_50324,cl_50325,cl_50326,cl_50327,cl_50328,cl_50329,cl_50330,cl_50331,cl_50332,cl_50333,cl_50334,cl_50335,cl_50336,cl_50337,cl_50338,cl_50339,cl_50340,cl_50341,cl_50342,cl_50343,cl_50345,cl_50346,cl_50348,cl_50349,cl_50350,cl_50351,cl_50352,cl_50353,cl_50354,cl_50356,cl_50357,cl_50359,cl_50361,cl_50364,cl_50365,cl_50366,cl_50367,cl_50368,cl_50369,cl_50370,cl_50371,cl_50372,cl_50373,cl_50374,cl_50375,cl_50376,cl_50377,cl_50378,cl_50381,cl_50382,cl_50383,cl_50384,cl_50385,cl_50386,cl_50387,cl_50388,cl_50389,cl_50391,cl_50392,cl_50393,cl_50394,cl_50395,cl_50397,cl_50398,cl_50399,cl_50400,cl_50402,cl_50404,cl_50405,cl_50406,cl_50408,cl_50409,cl_50410,cl_50412,cl_50413,cl_50417,cl_50418,cl_50419,cl_50421,cl_50423,cl_50424,cl_50425,cl_50426,cl_50427,cl_50428,cl_50429,cl_50430,cl_50431,cl_50432,cl_50434,cl_50435,cl_50438,cl_50440,cl_50441,cl_50442,cl_50447,cl_50448,cl_50451,cl_50452,cl_50453,cl_50454,cl_50455,cl_50456,cl_50457,cl_50458,cl_50459,cl_50460,cl_50462,cl_50463,cl_50464,cl_50465,cl_50466,cl_50467,cl_50468,cl_50469,cl_50470,cl_50472,cl_50473,cl_50474,cl_50478,cl_50479,cl_50480,cl_50482,cl_50485,cl_50486,cl_50488,cl_50489,cl_50490,cl_50491,cl_50492,cl_50493,cl_50495,cl_50496,cl_50497,cl_50499,cl_50500,cl_50501,cl_50502,cl_50503,cl_50504,cl_50506,cl_50507,cl_50508,cl_50509,cl_50510,cl_50511,cl_50513,cl_50514,cl_50515,cl_50516,cl_50517,cl_50518,cl_50521,cl_50523,cl_50524,cl_50525,cl_50526,cl_50529,cl_50530,cl_50531,cl_50532,cl_50533,cl_50535,cl_50536,cl_50537,cl_50539,cl_50541,cl_50542,cl_50543,cl_50544,cl_50545,cl_50546,cl_50547]
theorem chunk_sound046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk046, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_49913 v h) (hints_cons _ _ _ (der_49914 v h) (hints_cons _ _ _ (der_49915 v h) (hints_cons _ _ _ (der_49916 v h) (hints_cons _ _ _ (der_49917 v h) (hints_cons _ _ _ (der_49918 v h) (hints_cons _ _ _ (der_49920 v h) (hints_cons _ _ _ (der_49921 v h) (hints_cons _ _ _ (der_49922 v h) (hints_cons _ _ _ (der_49923 v h) (hints_cons _ _ _ (der_49924 v h) (hints_cons _ _ _ (der_49926 v h) (hints_cons _ _ _ (der_49927 v h) (hints_cons _ _ _ (der_49928 v h) (hints_cons _ _ _ (der_49930 v h) (hints_cons _ _ _ (der_49931 v h) (hints_cons _ _ _ (der_49932 v h) (hints_cons _ _ _ (der_49933 v h) (hints_cons _ _ _ (der_49934 v h) (hints_cons _ _ _ (der_49935 v h) (hints_cons _ _ _ (der_49936 v h) (hints_cons _ _ _ (der_49938 v h) (hints_cons _ _ _ (der_49939 v h) (hints_cons _ _ _ (der_49940 v h) (hints_cons _ _ _ (der_49943 v h) (hints_cons _ _ _ (der_49945 v h) (hints_cons _ _ _ (der_49946 v h) (hints_cons _ _ _ (der_49947 v h) (hints_cons _ _ _ (der_49949 v h) (hints_cons _ _ _ (der_49950 v h) (hints_cons _ _ _ (der_49951 v h) (hints_cons _ _ _ (der_49952 v h) (hints_cons _ _ _ (der_49953 v h) (hints_cons _ _ _ (der_49954 v h) (hints_cons _ _ _ (der_49955 v h) (hints_cons _ _ _ (der_49956 v h) (hints_cons _ _ _ (der_49957 v h) (hints_cons _ _ _ (der_49958 v h) (hints_cons _ _ _ (der_49960 v h) (hints_cons _ _ _ (der_49961 v h) (hints_cons _ _ _ (der_49962 v h) (hints_cons _ _ _ (der_49963 v h) (hints_cons _ _ _ (der_49964 v h) (hints_cons _ _ _ (der_49965 v h) (hints_cons _ _ _ (der_49966 v h) (hints_cons _ _ _ (der_49967 v h) (hints_cons _ _ _ (der_49968 v h) (hints_cons _ _ _ (der_49969 v h) (hints_cons _ _ _ (der_49970 v h) (hints_cons _ _ _ (der_49971 v h) (hints_cons _ _ _ (der_49972 v h) (hints_cons _ _ _ (der_49973 v h) (hints_cons _ _ _ (der_49974 v h) (hints_cons _ _ _ (der_49975 v h) (hints_cons _ _ _ (der_49976 v h) (hints_cons _ _ _ (der_49977 v h) (hints_cons _ _ _ (der_49978 v h) (hints_cons _ _ _ (der_49979 v h) (hints_cons _ _ _ (der_49980 v h) (hints_cons _ _ _ (der_49981 v h) (hints_cons _ _ _ (der_49982 v h) (hints_cons _ _ _ (der_49983 v h) (hints_cons _ _ _ (der_49984 v h) (hints_cons _ _ _ (der_49986 v h) (hints_cons _ _ _ (der_49987 v h) (hints_cons _ _ _ (der_49988 v h) (hints_cons _ _ _ (der_49989 v h) (hints_cons _ _ _ (der_49990 v h) (hints_cons _ _ _ (der_49991 v h) (hints_cons _ _ _ (der_49992 v h) (hints_cons _ _ _ (der_49993 v h) (hints_cons _ _ _ (der_49994 v h) (hints_cons _ _ _ (der_49995 v h) (hints_cons _ _ _ (der_49996 v h) (hints_cons _ _ _ (der_49997 v h) (hints_cons _ _ _ (der_49998 v h) (hints_cons _ _ _ (der_49999 v h) (hints_cons _ _ _ (der_50000 v h) (hints_cons _ _ _ (der_50001 v h) (hints_cons _ _ _ (der_50002 v h) (hints_cons _ _ _ (der_50003 v h) (hints_cons _ _ _ (der_50005 v h) (hints_cons _ _ _ (der_50006 v h) (hints_cons _ _ _ (der_50008 v h) (hints_cons _ _ _ (der_50009 v h) (hints_cons _ _ _ (der_50010 v h) (hints_cons _ _ _ (der_50011 v h) (hints_cons _ _ _ (der_50012 v h) (hints_cons _ _ _ (der_50015 v h) (hints_cons _ _ _ (der_50016 v h) (hints_cons _ _ _ (der_50017 v h) (hints_cons _ _ _ (der_50020 v h) (hints_cons _ _ _ (der_50021 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_50024 v h) (hints_cons _ _ _ (der_50025 v h) (hints_cons _ _ _ (der_50026 v h) (hints_cons _ _ _ (der_50027 v h) (hints_cons _ _ _ (der_50028 v h) (hints_cons _ _ _ (der_50029 v h) (hints_cons _ _ _ (der_50031 v h) (hints_cons _ _ _ (der_50032 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_50034 v h) (hints_cons _ _ _ (der_50035 v h) (hints_cons _ _ _ (der_50036 v h) (hints_cons _ _ _ (der_50037 v h) (hints_cons _ _ _ (der_50040 v h) (hints_cons _ _ _ (der_50041 v h) (hints_cons _ _ _ (der_50042 v h) (hints_cons _ _ _ (der_50043 v h) (hints_cons _ _ _ (der_50044 v h) (hints_cons _ _ _ (der_50046 v h) (hints_cons _ _ _ (der_50047 v h) (hints_cons _ _ _ (der_50048 v h) (hints_cons _ _ _ (der_50049 v h) (hints_cons _ _ _ (der_50050 v h) (hints_cons _ _ _ (der_50051 v h) (hints_cons _ _ _ (der_50052 v h) (hints_cons _ _ _ (der_50053 v h) (hints_cons _ _ _ (der_50055 v h) (hints_cons _ _ _ (der_50056 v h) (hints_cons _ _ _ (der_50057 v h) (hints_cons _ _ _ (der_50059 v h) (hints_cons _ _ _ (der_50060 v h) (hints_cons _ _ _ (der_50063 v h) (hints_cons _ _ _ (der_50064 v h) (hints_cons _ _ _ (der_50065 v h) (hints_cons _ _ _ (der_50066 v h) (hints_cons _ _ _ (der_50067 v h) (hints_cons _ _ _ (der_50068 v h) (hints_cons _ _ _ (der_50070 v h) (hints_cons _ _ _ (der_50071 v h) (hints_cons _ _ _ (der_50073 v h) (hints_cons _ _ _ (der_50074 v h) (hints_cons _ _ _ (der_50076 v h) (hints_cons _ _ _ (der_50077 v h) (hints_cons _ _ _ (der_50078 v h) (hints_cons _ _ _ (der_50079 v h) (hints_cons _ _ _ (der_50080 v h) (hints_cons _ _ _ (der_50081 v h) (hints_cons _ _ _ (der_50082 v h) (hints_cons _ _ _ (der_50083 v h) (hints_cons _ _ _ (der_50085 v h) (hints_cons _ _ _ (der_50086 v h) (hints_cons _ _ _ (der_50087 v h) (hints_cons _ _ _ (der_50088 v h) (hints_cons _ _ _ (der_50089 v h) (hints_cons _ _ _ (der_50091 v h) (hints_cons _ _ _ (der_50092 v h) (hints_cons _ _ _ (der_50093 v h) (hints_cons _ _ _ (der_50094 v h) (hints_cons _ _ _ (der_50096 v h) (hints_cons _ _ _ (der_50097 v h) (hints_cons _ _ _ (der_50098 v h) (hints_cons _ _ _ (der_50099 v h) (hints_cons _ _ _ (der_50100 v h) (hints_cons _ _ _ (der_50101 v h) (hints_cons _ _ _ (der_50102 v h) (hints_cons _ _ _ (der_50104 v h) (hints_cons _ _ _ (der_50105 v h) (hints_cons _ _ _ (der_50106 v h) (hints_cons _ _ _ (der_50107 v h) (hints_cons _ _ _ (der_50109 v h) (hints_cons _ _ _ (der_50110 v h) (hints_cons _ _ _ (der_50111 v h) (hints_cons _ _ _ (der_50112 v h) (hints_cons _ _ _ (der_50113 v h) (hints_cons _ _ _ (der_50114 v h) (hints_cons _ _ _ (der_50116 v h) (hints_cons _ _ _ (der_50117 v h) (hints_cons _ _ _ (der_50118 v h) (hints_cons _ _ _ (der_50119 v h) (hints_cons _ _ _ (der_50120 v h) (hints_cons _ _ _ (der_50121 v h) (hints_cons _ _ _ (der_50122 v h) (hints_cons _ _ _ (der_50123 v h) (hints_cons _ _ _ (der_50124 v h) (hints_cons _ _ _ (der_50125 v h) (hints_cons _ _ _ (der_50127 v h) (hints_cons _ _ _ (der_50128 v h) (hints_cons _ _ _ (der_50129 v h) (hints_cons _ _ _ (der_50131 v h) (hints_cons _ _ _ (der_50133 v h) (hints_cons _ _ _ (der_50134 v h) (hints_cons _ _ _ (der_50135 v h) (hints_cons _ _ _ (der_50136 v h) (hints_cons _ _ _ (der_50137 v h) (hints_cons _ _ _ (der_50138 v h) (hints_cons _ _ _ (der_50139 v h) (hints_cons _ _ _ (der_50140 v h) (hints_cons _ _ _ (der_50141 v h) (hints_cons _ _ _ (der_50142 v h) (hints_cons _ _ _ (der_50143 v h) (hints_cons _ _ _ (der_50144 v h) (hints_cons _ _ _ (der_50145 v h) (hints_cons _ _ _ (der_50146 v h) (hints_cons _ _ _ (der_50148 v h) (hints_cons _ _ _ (der_50149 v h) (hints_cons _ _ _ (der_50150 v h) (hints_cons _ _ _ (der_50152 v h) (hints_cons _ _ _ (der_50153 v h) (hints_cons _ _ _ (der_50154 v h) (hints_cons _ _ _ (der_50155 v h) (hints_cons _ _ _ (der_50156 v h) (hints_cons _ _ _ (der_50157 v h) (hints_cons _ _ _ (der_50158 v h) (hints_cons _ _ _ (der_50159 v h) (hints_cons _ _ _ (der_50160 v h) (hints_cons _ _ _ (der_50161 v h) (hints_cons _ _ _ (der_50162 v h) (hints_cons _ _ _ (der_50163 v h) (hints_cons _ _ _ (der_50164 v h) (hints_cons _ _ _ (der_50165 v h) (hints_cons _ _ _ (der_50166 v h) (hints_cons _ _ _ (der_50167 v h) (hints_cons _ _ _ (der_50168 v h) (hints_cons _ _ _ (der_50169 v h) (hints_cons _ _ _ (der_50170 v h) (hints_cons _ _ _ (der_50171 v h) (hints_cons _ _ _ (der_50172 v h) (hints_cons _ _ _ (der_50173 v h) (hints_cons _ _ _ (der_50174 v h) (hints_cons _ _ _ (der_50175 v h) (hints_cons _ _ _ (der_50176 v h) (hints_cons _ _ _ (der_50177 v h) (hints_cons _ _ _ (der_50178 v h) (hints_cons _ _ _ (der_50179 v h) (hints_cons _ _ _ (der_50180 v h) (hints_cons _ _ _ (der_50181 v h) (hints_cons _ _ _ (der_50182 v h) (hints_cons _ _ _ (der_50184 v h) (hints_cons _ _ _ (der_50185 v h) (hints_cons _ _ _ (der_50186 v h) (hints_cons _ _ _ (der_50187 v h) (hints_cons _ _ _ (der_50188 v h) (hints_cons _ _ _ (der_50190 v h) (hints_cons _ _ _ (der_50191 v h) (hints_cons _ _ _ (der_50192 v h) (hints_cons _ _ _ (der_50193 v h) (hints_cons _ _ _ (der_50194 v h) (hints_cons _ _ _ (der_50195 v h) (hints_cons _ _ _ (der_50196 v h) (hints_cons _ _ _ (der_50198 v h) (hints_cons _ _ _ (der_50199 v h) (hints_cons _ _ _ (der_50200 v h) (hints_cons _ _ _ (der_50201 v h) (hints_cons _ _ _ (der_50202 v h) (hints_cons _ _ _ (der_50203 v h) (hints_cons _ _ _ (der_50205 v h) (hints_cons _ _ _ (der_50206 v h) (hints_cons _ _ _ (der_50207 v h) (hints_cons _ _ _ (der_50208 v h) (hints_cons _ _ _ (der_50209 v h) (hints_cons _ _ _ (der_50210 v h) (hints_cons _ _ _ (der_50211 v h) (hints_cons _ _ _ (der_50212 v h) (hints_cons _ _ _ (der_50213 v h) (hints_cons _ _ _ (der_50215 v h) (hints_cons _ _ _ (der_50216 v h) (hints_cons _ _ _ (der_50217 v h) (hints_cons _ _ _ (der_50218 v h) (hints_cons _ _ _ (der_50219 v h) (hints_cons _ _ _ (der_50220 v h) (hints_cons _ _ _ (der_50221 v h) (hints_cons _ _ _ (der_50222 v h) (hints_cons _ _ _ (der_50225 v h) (hints_cons _ _ _ (der_50226 v h) (hints_cons _ _ _ (der_50229 v h) (hints_cons _ _ _ (der_50230 v h) (hints_cons _ _ _ (der_50231 v h) (hints_cons _ _ _ (der_50232 v h) (hints_cons _ _ _ (der_50233 v h) (hints_cons _ _ _ (der_50237 v h) (hints_cons _ _ _ (der_50240 v h) (hints_cons _ _ _ (der_50241 v h) (hints_cons _ _ _ (der_50244 v h) (hints_cons _ _ _ (der_50247 v h) (hints_cons _ _ _ (der_50248 v h) (hints_cons _ _ _ (der_50249 v h) (hints_cons _ _ _ (der_50250 v h) (hints_cons _ _ _ (der_50257 v h) (hints_cons _ _ _ (der_50265 v h) (hints_cons _ _ _ (der_50266 v h) (hints_cons _ _ _ (der_50267 v h) (hints_cons _ _ _ (der_50268 v h) (hints_cons _ _ _ (der_50269 v h) (hints_cons _ _ _ (der_50270 v h) (hints_cons _ _ _ (der_50271 v h) (hints_cons _ _ _ (der_50272 v h) (hints_cons _ _ _ (der_50273 v h) (hints_cons _ _ _ (der_50274 v h) (hints_cons _ _ _ (der_50275 v h) (hints_cons _ _ _ (der_50276 v h) (hints_cons _ _ _ (der_50277 v h) (hints_cons _ _ _ (der_50279 v h) (hints_cons _ _ _ (der_50280 v h) (hints_cons _ _ _ (der_50281 v h) (hints_cons _ _ _ (der_50282 v h) (hints_cons _ _ _ (der_50283 v h) (hints_cons _ _ _ (der_50284 v h) (hints_cons _ _ _ (der_50285 v h) (hints_cons _ _ _ (der_50286 v h) (hints_cons _ _ _ (der_50288 v h) (hints_cons _ _ _ (der_50289 v h) (hints_cons _ _ _ (der_50290 v h) (hints_cons _ _ _ (der_50291 v h) (hints_cons _ _ _ (der_50293 v h) (hints_cons _ _ _ (der_50294 v h) (hints_cons _ _ _ (der_50295 v h) (hints_cons _ _ _ (der_50297 v h) (hints_cons _ _ _ (der_50298 v h) (hints_cons _ _ _ (der_50299 v h) (hints_cons _ _ _ (der_50300 v h) (hints_cons _ _ _ (der_50301 v h) (hints_cons _ _ _ (der_50302 v h) (hints_cons _ _ _ (der_50305 v h) (hints_cons _ _ _ (der_50306 v h) (hints_cons _ _ _ (der_50309 v h) (hints_cons _ _ _ (der_50310 v h) (hints_cons _ _ _ (der_50313 v h) (hints_cons _ _ _ (der_50316 v h) (hints_cons _ _ _ (der_50317 v h) (hints_cons _ _ _ (der_50320 v h) (hints_cons _ _ _ (der_50321 v h) (hints_cons _ _ _ (der_50322 v h) (hints_cons _ _ _ (der_50323 v h) (hints_cons _ _ _ (der_50324 v h) (hints_cons _ _ _ (der_50325 v h) (hints_cons _ _ _ (der_50326 v h) (hints_cons _ _ _ (der_50327 v h) (hints_cons _ _ _ (der_50328 v h) (hints_cons _ _ _ (der_50329 v h) (hints_cons _ _ _ (der_50330 v h) (hints_cons _ _ _ (der_50331 v h) (hints_cons _ _ _ (der_50332 v h) (hints_cons _ _ _ (der_50333 v h) (hints_cons _ _ _ (der_50334 v h) (hints_cons _ _ _ (der_50335 v h) (hints_cons _ _ _ (der_50336 v h) (hints_cons _ _ _ (der_50337 v h) (hints_cons _ _ _ (der_50338 v h) (hints_cons _ _ _ (der_50339 v h) (hints_cons _ _ _ (der_50340 v h) (hints_cons _ _ _ (der_50341 v h) (hints_cons _ _ _ (der_50342 v h) (hints_cons _ _ _ (der_50343 v h) (hints_cons _ _ _ (der_50345 v h) (hints_cons _ _ _ (der_50346 v h) (hints_cons _ _ _ (der_50348 v h) (hints_cons _ _ _ (der_50349 v h) (hints_cons _ _ _ (der_50350 v h) (hints_cons _ _ _ (der_50351 v h) (hints_cons _ _ _ (der_50352 v h) (hints_cons _ _ _ (der_50353 v h) (hints_cons _ _ _ (der_50354 v h) (hints_cons _ _ _ (der_50356 v h) (hints_cons _ _ _ (der_50357 v h) (hints_cons _ _ _ (der_50359 v h) (hints_cons _ _ _ (der_50361 v h) (hints_cons _ _ _ (der_50364 v h) (hints_cons _ _ _ (der_50365 v h) (hints_cons _ _ _ (der_50366 v h) (hints_cons _ _ _ (der_50367 v h) (hints_cons _ _ _ (der_50368 v h) (hints_cons _ _ _ (der_50369 v h) (hints_cons _ _ _ (der_50370 v h) (hints_cons _ _ _ (der_50371 v h) (hints_cons _ _ _ (der_50372 v h) (hints_cons _ _ _ (der_50373 v h) (hints_cons _ _ _ (der_50374 v h) (hints_cons _ _ _ (der_50375 v h) (hints_cons _ _ _ (der_50376 v h) (hints_cons _ _ _ (der_50377 v h) (hints_cons _ _ _ (der_50378 v h) (hints_cons _ _ _ (der_50381 v h) (hints_cons _ _ _ (der_50382 v h) (hints_cons _ _ _ (der_50383 v h) (hints_cons _ _ _ (der_50384 v h) (hints_cons _ _ _ (der_50385 v h) (hints_cons _ _ _ (der_50386 v h) (hints_cons _ _ _ (der_50387 v h) (hints_cons _ _ _ (der_50388 v h) (hints_cons _ _ _ (der_50389 v h) (hints_cons _ _ _ (der_50391 v h) (hints_cons _ _ _ (der_50392 v h) (hints_cons _ _ _ (der_50393 v h) (hints_cons _ _ _ (der_50394 v h) (hints_cons _ _ _ (der_50395 v h) (hints_cons _ _ _ (der_50397 v h) (hints_cons _ _ _ (der_50398 v h) (hints_cons _ _ _ (der_50399 v h) (hints_cons _ _ _ (der_50400 v h) (hints_cons _ _ _ (der_50402 v h) (hints_cons _ _ _ (der_50404 v h) (hints_cons _ _ _ (der_50405 v h) (hints_cons _ _ _ (der_50406 v h) (hints_cons _ _ _ (der_50408 v h) (hints_cons _ _ _ (der_50409 v h) (hints_cons _ _ _ (der_50410 v h) (hints_cons _ _ _ (der_50412 v h) (hints_cons _ _ _ (der_50413 v h) (hints_cons _ _ _ (der_50417 v h) (hints_cons _ _ _ (der_50418 v h) (hints_cons _ _ _ (der_50419 v h) (hints_cons _ _ _ (der_50421 v h) (hints_cons _ _ _ (der_50423 v h) (hints_cons _ _ _ (der_50424 v h) (hints_cons _ _ _ (der_50425 v h) (hints_cons _ _ _ (der_50426 v h) (hints_cons _ _ _ (der_50427 v h) (hints_cons _ _ _ (der_50428 v h) (hints_cons _ _ _ (der_50429 v h) (hints_cons _ _ _ (der_50430 v h) (hints_cons _ _ _ (der_50431 v h) (hints_cons _ _ _ (der_50432 v h) (hints_cons _ _ _ (der_50434 v h) (hints_cons _ _ _ (der_50435 v h) (hints_cons _ _ _ (der_50438 v h) (hints_cons _ _ _ (der_50440 v h) (hints_cons _ _ _ (der_50441 v h) (hints_cons _ _ _ (der_50442 v h) (hints_cons _ _ _ (der_50447 v h) (hints_cons _ _ _ (der_50448 v h) (hints_cons _ _ _ (der_50451 v h) (hints_cons _ _ _ (der_50452 v h) (hints_cons _ _ _ (der_50453 v h) (hints_cons _ _ _ (der_50454 v h) (hints_cons _ _ _ (der_50455 v h) (hints_cons _ _ _ (der_50456 v h) (hints_cons _ _ _ (der_50457 v h) (hints_cons _ _ _ (der_50458 v h) (hints_cons _ _ _ (der_50459 v h) (hints_cons _ _ _ (der_50460 v h) (hints_cons _ _ _ (der_50462 v h) (hints_cons _ _ _ (der_50463 v h) (hints_cons _ _ _ (der_50464 v h) (hints_cons _ _ _ (der_50465 v h) (hints_cons _ _ _ (der_50466 v h) (hints_cons _ _ _ (der_50467 v h) (hints_cons _ _ _ (der_50468 v h) (hints_cons _ _ _ (der_50469 v h) (hints_cons _ _ _ (der_50470 v h) (hints_cons _ _ _ (der_50472 v h) (hints_cons _ _ _ (der_50473 v h) (hints_cons _ _ _ (der_50474 v h) (hints_cons _ _ _ (der_50478 v h) (hints_cons _ _ _ (der_50479 v h) (hints_cons _ _ _ (der_50480 v h) (hints_cons _ _ _ (der_50482 v h) (hints_cons _ _ _ (der_50485 v h) (hints_cons _ _ _ (der_50486 v h) (hints_cons _ _ _ (der_50488 v h) (hints_cons _ _ _ (der_50489 v h) (hints_cons _ _ _ (der_50490 v h) (hints_cons _ _ _ (der_50491 v h) (hints_cons _ _ _ (der_50492 v h) (hints_cons _ _ _ (der_50493 v h) (hints_cons _ _ _ (der_50495 v h) (hints_cons _ _ _ (der_50496 v h) (hints_cons _ _ _ (der_50497 v h) (hints_cons _ _ _ (der_50499 v h) (hints_cons _ _ _ (der_50500 v h) (hints_cons _ _ _ (der_50501 v h) (hints_cons _ _ _ (der_50502 v h) (hints_cons _ _ _ (der_50503 v h) (hints_cons _ _ _ (der_50504 v h) (hints_cons _ _ _ (der_50506 v h) (hints_cons _ _ _ (der_50507 v h) (hints_cons _ _ _ (der_50508 v h) (hints_cons _ _ _ (der_50509 v h) (hints_cons _ _ _ (der_50510 v h) (hints_cons _ _ _ (der_50511 v h) (hints_cons _ _ _ (der_50513 v h) (hints_cons _ _ _ (der_50514 v h) (hints_cons _ _ _ (der_50515 v h) (hints_cons _ _ _ (der_50516 v h) (hints_cons _ _ _ (der_50517 v h) (hints_cons _ _ _ (der_50518 v h) (hints_cons _ _ _ (der_50521 v h) (hints_cons _ _ _ (der_50523 v h) (hints_cons _ _ _ (der_50524 v h) (hints_cons _ _ _ (der_50525 v h) (hints_cons _ _ _ (der_50526 v h) (hints_cons _ _ _ (der_50529 v h) (hints_cons _ _ _ (der_50530 v h) (hints_cons _ _ _ (der_50531 v h) (hints_cons _ _ _ (der_50532 v h) (hints_cons _ _ _ (der_50533 v h) (hints_cons _ _ _ (der_50535 v h) (hints_cons _ _ _ (der_50536 v h) (hints_cons _ _ _ (der_50537 v h) (hints_cons _ _ _ (der_50539 v h) (hints_cons _ _ _ (der_50541 v h) (hints_cons _ _ _ (der_50542 v h) (hints_cons _ _ _ (der_50543 v h) (hints_cons _ _ _ (der_50544 v h) (hints_cons _ _ _ (der_50545 v h) (hints_cons _ _ _ (der_50546 v h) (hints_cons _ _ _ (der_50547 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix046 := prefix045 ++ chunk046
theorem prefix_sound046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix046, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound045 v h c hc
  · exact chunk_sound046 v h c hc
end Percolation.NReplay
