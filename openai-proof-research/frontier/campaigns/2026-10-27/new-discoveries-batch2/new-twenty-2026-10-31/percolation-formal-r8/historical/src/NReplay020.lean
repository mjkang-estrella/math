import NReplay019
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_32862 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(84,false),(91,true)]
theorem der_32862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32862 :=
  CNF.rup_sound cl_32862 [cl_27364,cl_32855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27364 v h) (hints_cons _ _ _ (der_32855 v h) (by intro d hd; cases hd)))
def cl_32863 : CNF.NClause := [(55,false),(84,false),(80,true),(63,true),(24,true),(67,false)]
theorem der_32863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32863 :=
  CNF.rup_sound cl_32863 [cl_27365,cl_32856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27365 v h) (hints_cons _ _ _ (der_32856 v h) (by intro d hd; cases hd)))
def cl_32864 : CNF.NClause := [(55,false),(76,true),(63,false),(84,false),(24,false),(67,true)]
theorem der_32864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32864 :=
  CNF.rup_sound cl_32864 [cl_27366,cl_32817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27366 v h) (hints_cons _ _ _ (der_32817 v h) (by intro d hd; cases hd)))
def cl_32865 : CNF.NClause := [(55,false),(84,false),(76,true),(80,true),(63,false),(67,true)]
theorem der_32865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32865 :=
  CNF.rup_sound cl_32865 [cl_27367,cl_32864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27367 v h) (hints_cons _ _ _ (der_32864 v h) (by intro d hd; cases hd)))
def cl_32866 : CNF.NClause := [(55,false),(91,true),(76,true),(84,false),(24,false),(67,true)]
theorem der_32866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32866 :=
  CNF.rup_sound cl_32866 [cl_27368,cl_32852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27368 v h) (hints_cons _ _ _ (der_32852 v h) (by intro d hd; cases hd)))
def cl_32867 : CNF.NClause := [(55,false),(91,true),(76,true),(80,true),(84,false),(67,true)]
theorem der_32867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32867 :=
  CNF.rup_sound cl_32867 [cl_27369,cl_32866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27369 v h) (hints_cons _ _ _ (der_32866 v h) (by intro d hd; cases hd)))
def cl_32868 : CNF.NClause := [(55,false),(84,true),(63,false),(67,false),(76,false),(80,false)]
theorem der_32868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32868 :=
  CNF.rup_sound cl_32868 [cl_27371,cl_27370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27371 v h) (hints_cons _ _ _ (der_27370 v h) (by intro d hd; cases hd)))
def cl_32869 : CNF.NClause := [(55,false),(80,false),(63,true),(67,false),(76,false),(24,false)]
theorem der_32869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32869 :=
  CNF.rup_sound cl_32869 [cl_27372,cl_32855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27372 v h) (hints_cons _ _ _ (der_32855 v h) (by intro d hd; cases hd)))
def cl_32870 : CNF.NClause := [(55,false),(91,true),(63,true),(67,false),(76,false),(80,false)]
theorem der_32870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32870 :=
  CNF.rup_sound cl_32870 [cl_27373,cl_32869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27373 v h) (hints_cons _ _ _ (der_32869 v h) (by intro d hd; cases hd)))
def cl_32871 : CNF.NClause := [(55,false),(84,true),(24,false),(63,false),(76,false),(80,false)]
theorem der_32871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32871 :=
  CNF.rup_sound cl_32871 [cl_27374,cl_27311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27374 v h) (hints_cons _ _ _ (der_27311 v h) (by intro d hd; cases hd)))
def cl_32872 : CNF.NClause := [(55,false),(84,true),(63,false),(76,false),(80,false),(91,true)]
theorem der_32872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32872 :=
  CNF.rup_sound cl_32872 [cl_27375,cl_32871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27375 v h) (hints_cons _ _ _ (der_32871 v h) (by intro d hd; cases hd)))
def cl_32873 : CNF.NClause := [(55,false),(84,true),(24,false),(76,false),(80,false),(67,true)]
theorem der_32873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32873 :=
  CNF.rup_sound cl_32873 [cl_27376,cl_32871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27376 v h) (hints_cons _ _ _ (der_32871 v h) (by intro d hd; cases hd)))
def cl_32874 : CNF.NClause := [(55,false),(80,false),(63,true),(76,false),(24,true),(91,true)]
theorem der_32874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32874 :=
  CNF.rup_sound cl_32874 [cl_27377,cl_32870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27377 v h) (hints_cons _ _ _ (der_32870 v h) (by intro d hd; cases hd)))
def cl_32875 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(80,false),(91,true)]
theorem der_32875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32875 :=
  CNF.rup_sound cl_32875 [cl_27379,cl_32847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27379 v h) (hints_cons _ _ _ (der_32847 v h) (by intro d hd; cases hd)))
def cl_32876 : CNF.NClause := [(55,false),(91,true),(63,true),(67,false),(80,false),(24,false)]
theorem der_32876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32876 :=
  CNF.rup_sound cl_32876 [cl_27380,cl_32870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27380 v h) (hints_cons _ _ _ (der_32870 v h) (by intro d hd; cases hd)))
def cl_32877 : CNF.NClause := [(55,false),(80,false),(76,true),(63,true),(67,false),(24,true)]
theorem der_32877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32877 :=
  CNF.rup_sound cl_32877 [cl_27381,cl_32849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27381 v h) (hints_cons _ _ _ (der_32849 v h) (by intro d hd; cases hd)))
def cl_32878 : CNF.NClause := [(55,false),(76,true),(63,false),(80,false),(67,true),(24,false)]
theorem der_32878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32878 :=
  CNF.rup_sound cl_32878 [cl_27382,cl_32828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27382 v h) (hints_cons _ _ _ (der_32828 v h) (by intro d hd; cases hd)))
def cl_32879 : CNF.NClause := [(55,false),(76,true),(67,true),(63,false),(80,false),(24,true)]
theorem der_32879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32879 :=
  CNF.rup_sound cl_32879 [cl_27383,cl_32851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27383 v h) (hints_cons _ _ _ (der_32851 v h) (by intro d hd; cases hd)))
def cl_32880 : CNF.NClause := [(55,false),(91,true),(63,true),(80,false),(67,true),(24,false)]
theorem der_32880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32880 :=
  CNF.rup_sound cl_32880 [cl_27384,cl_32852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27384 v h) (hints_cons _ _ _ (der_32852 v h) (by intro d hd; cases hd)))
def cl_32881 : CNF.NClause := [(55,false),(84,true),(91,true),(63,false),(67,false),(76,false)]
theorem der_32881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32881 :=
  CNF.rup_sound cl_32881 [cl_27387,cl_27386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27387 v h) (hints_cons _ _ _ (der_27386 v h) (by intro d hd; cases hd)))
def cl_32882 : CNF.NClause := [(55,false),(76,false),(80,true),(63,true),(67,false),(24,false)]
theorem der_32882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32882 :=
  CNF.rup_sound cl_32882 [cl_27388,cl_32855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27388 v h) (hints_cons _ _ _ (der_32855 v h) (by intro d hd; cases hd)))
def cl_32883 : CNF.NClause := [(55,false),(80,true),(63,true),(67,false),(76,false),(91,true)]
theorem der_32883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32883 :=
  CNF.rup_sound cl_32883 [cl_27389,cl_32856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27389 v h) (hints_cons _ _ _ (der_32856 v h) (by intro d hd; cases hd)))
def cl_32886 : CNF.NClause := [(55,false),(91,true),(63,true),(76,false),(67,true),(24,true)]
theorem der_32886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32886 :=
  CNF.rup_sound cl_32886 [cl_27393,cl_32874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27393 v h) (hints_cons _ _ _ (der_32874 v h) (by intro d hd; cases hd)))
def cl_32887 : CNF.NClause := [(55,false),(76,true),(80,true),(63,false),(67,false),(24,false)]
theorem der_32887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32887 :=
  CNF.rup_sound cl_32887 [cl_27394,cl_32837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27394 v h) (hints_cons _ _ _ (der_32837 v h) (by intro d hd; cases hd)))
def cl_32888 : CNF.NClause := [(55,false),(80,true),(91,true),(63,false),(67,false),(24,true)]
theorem der_32888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32888 :=
  CNF.rup_sound cl_32888 [cl_27395,cl_32861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27395 v h) (hints_cons _ _ _ (der_32861 v h) (by intro d hd; cases hd)))
def cl_32889 : CNF.NClause := [(55,false),(80,true),(91,true),(63,true),(67,false),(24,false)]
theorem der_32889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32889 :=
  CNF.rup_sound cl_32889 [cl_27396,cl_32862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27396 v h) (hints_cons _ _ _ (der_32862 v h) (by intro d hd; cases hd)))
def cl_32890 : CNF.NClause := [(55,false),(76,true),(80,true),(63,true),(24,true),(67,false)]
theorem der_32890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32890 :=
  CNF.rup_sound cl_32890 [cl_27397,cl_32863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27397 v h) (hints_cons _ _ _ (der_32863 v h) (by intro d hd; cases hd)))
def cl_32891 : CNF.NClause := [(55,false),(91,true),(76,true),(80,true),(63,false),(24,false)]
theorem der_32891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32891 :=
  CNF.rup_sound cl_32891 [cl_27398,cl_32887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27398 v h) (hints_cons _ _ _ (der_32887 v h) (by intro d hd; cases hd)))
def cl_32892 : CNF.NClause := [(55,false),(91,true),(76,true),(63,false),(24,true),(67,true)]
theorem der_32892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32892 :=
  CNF.rup_sound cl_32892 [cl_27399,cl_32879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27399 v h) (hints_cons _ _ _ (der_32879 v h) (by intro d hd; cases hd)))
def cl_32894 : CNF.NClause := [(46,false),(77,true),(92,false),(79,false),(81,false),(80,false)]
theorem der_32894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32894 :=
  CNF.rup_sound cl_32894 [cl_27405,cl_27402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27405 v h) (hints_cons _ _ _ (der_27402 v h) (by intro d hd; cases hd)))
def cl_32895 : CNF.NClause := [(46,false),(78,false),(77,true),(92,false),(81,false),(80,false)]
theorem der_32895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32895 :=
  CNF.rup_sound cl_32895 [cl_27408,cl_27402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27408 v h) (hints_cons _ _ _ (der_27402 v h) (by intro d hd; cases hd)))
def cl_32896 : CNF.NClause := [(46,false),(81,false),(92,false),(15,true),(77,false),(80,false)]
theorem der_32896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32896 :=
  CNF.rup_sound cl_32896 [cl_27410,cl_27403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27410 v h) (hints_cons _ _ _ (der_27403 v h) (by intro d hd; cases hd)))
def cl_32897 : CNF.NClause := [(46,false),(78,true),(15,false),(92,false),(81,false),(80,false)]
theorem der_32897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32897 :=
  CNF.rup_sound cl_32897 [cl_27411,cl_27409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27411 v h) (hints_cons _ _ _ (der_27409 v h) (by intro d hd; cases hd)))
def cl_32898 : CNF.NClause := [(46,false),(78,true),(77,true),(92,false),(81,false),(80,false)]
theorem der_32898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32898 :=
  CNF.rup_sound cl_32898 [cl_27412,cl_32894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27412 v h) (hints_cons _ _ _ (der_32894 v h) (by intro d hd; cases hd)))
def cl_32899 : CNF.NClause := [(46,false),(81,false),(80,true),(92,false),(78,false),(79,false)]
theorem der_32899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32899 :=
  CNF.rup_sound cl_32899 [cl_27415,cl_27413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27415 v h) (hints_cons _ _ _ (der_27413 v h) (by intro d hd; cases hd)))
def cl_32900 : CNF.NClause := [(46,false),(79,false),(92,false),(77,false),(15,true),(81,false)]
theorem der_32900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32900 :=
  CNF.rup_sound cl_32900 [cl_27417,cl_27403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27417 v h) (hints_cons _ _ _ (der_27403 v h) (by intro d hd; cases hd)))
def cl_32901 : CNF.NClause := [(46,false),(92,false),(15,false),(77,true),(79,false),(81,false)]
theorem der_32901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32901 :=
  CNF.rup_sound cl_32901 [cl_27418,cl_32894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27418 v h) (hints_cons _ _ _ (der_32894 v h) (by intro d hd; cases hd)))
def cl_32902 : CNF.NClause := [(46,false),(92,false),(80,true),(15,true),(79,false),(81,false)]
theorem der_32902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32902 :=
  CNF.rup_sound cl_32902 [cl_27419,cl_32900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27419 v h) (hints_cons _ _ _ (der_32900 v h) (by intro d hd; cases hd)))
def cl_32903 : CNF.NClause := [(46,false),(78,false),(92,false),(77,false),(15,true),(81,false)]
theorem der_32903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32903 :=
  CNF.rup_sound cl_32903 [cl_27421,cl_32900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27421 v h) (hints_cons _ _ _ (der_32900 v h) (by intro d hd; cases hd)))
def cl_32904 : CNF.NClause := [(46,false),(78,false),(77,true),(15,false),(92,false),(81,false)]
theorem der_32904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32904 :=
  CNF.rup_sound cl_32904 [cl_27422,cl_27407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27422 v h) (hints_cons _ _ _ (der_27407 v h) (by intro d hd; cases hd)))
def cl_32905 : CNF.NClause := [(46,false),(78,false),(80,true),(15,true),(92,false),(81,false)]
theorem der_32905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32905 :=
  CNF.rup_sound cl_32905 [cl_27423,cl_32903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27423 v h) (hints_cons _ _ _ (der_32903 v h) (by intro d hd; cases hd)))
def cl_32906 : CNF.NClause := [(46,false),(78,true),(15,false),(92,false),(77,false),(81,false)]
theorem der_32906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32906 :=
  CNF.rup_sound cl_32906 [cl_27424,cl_27416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27424 v h) (hints_cons _ _ _ (der_27416 v h) (by intro d hd; cases hd)))
def cl_32907 : CNF.NClause := [(46,false),(77,false),(79,true),(15,true),(92,false),(81,false)]
theorem der_32907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32907 :=
  CNF.rup_sound cl_32907 [cl_27425,cl_32903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27425 v h) (hints_cons _ _ _ (der_32903 v h) (by intro d hd; cases hd)))
def cl_32908 : CNF.NClause := [(46,false),(78,true),(15,false),(79,true),(92,false),(81,false)]
theorem der_32908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32908 :=
  CNF.rup_sound cl_32908 [cl_27426,cl_32906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27426 v h) (hints_cons _ _ _ (der_32906 v h) (by intro d hd; cases hd)))
def cl_32909 : CNF.NClause := [(46,false),(78,true),(79,true),(77,true),(92,false),(81,false)]
theorem der_32909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32909 :=
  CNF.rup_sound cl_32909 [cl_27427,cl_32898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27427 v h) (hints_cons _ _ _ (der_32898 v h) (by intro d hd; cases hd)))
def cl_32910 : CNF.NClause := [(46,false),(78,false),(77,true),(15,false),(92,false),(79,false)]
theorem der_32910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32910 :=
  CNF.rup_sound cl_32910 [cl_27429,cl_26326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27429 v h) (hints_cons _ _ _ (der_26326 v h) (by intro d hd; cases hd)))
def cl_32911 : CNF.NClause := [(46,false),(80,false),(92,false),(78,false),(79,false),(77,true)]
theorem der_32911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32911 :=
  CNF.rup_sound cl_32911 [cl_27430,cl_27402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27430 v h) (hints_cons _ _ _ (der_27402 v h) (by intro d hd; cases hd)))
def cl_32912 : CNF.NClause := [(46,false),(15,true),(92,false),(77,false),(79,false),(80,false)]
theorem der_32912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32912 :=
  CNF.rup_sound cl_32912 [cl_27432,cl_32896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27432 v h) (hints_cons _ _ _ (der_32896 v h) (by intro d hd; cases hd)))
def cl_32913 : CNF.NClause := [(46,false),(15,false),(77,true),(92,false),(79,false),(80,false)]
theorem der_32913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32913 :=
  CNF.rup_sound cl_32913 [cl_27433,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27433 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_32914 : CNF.NClause := [(46,false),(77,true),(81,true),(92,false),(79,false),(80,false)]
theorem der_32914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32914 :=
  CNF.rup_sound cl_32914 [cl_27434,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27434 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_32916 : CNF.NClause := [(46,false),(92,false),(15,false),(77,true),(78,false),(80,false)]
theorem der_32916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32916 :=
  CNF.rup_sound cl_32916 [cl_27437,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27437 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_32917 : CNF.NClause := [(46,false),(78,false),(77,true),(81,true),(92,false),(80,false)]
theorem der_32917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32917 :=
  CNF.rup_sound cl_32917 [cl_27438,cl_32916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27438 v h) (hints_cons _ _ _ (der_32916 v h) (by intro d hd; cases hd)))
def cl_32918 : CNF.NClause := [(46,false),(15,false),(79,true),(77,true),(92,false),(80,false)]
theorem der_32918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32918 :=
  CNF.rup_sound cl_32918 [cl_27441,cl_32916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27441 v h) (hints_cons _ _ _ (der_32916 v h) (by intro d hd; cases hd)))
def cl_32919 : CNF.NClause := [(46,false),(78,true),(79,true),(81,true),(92,false),(80,false)]
theorem der_32919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32919 :=
  CNF.rup_sound cl_32919 [cl_27442,cl_27440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27442 v h) (hints_cons _ _ _ (der_27440 v h) (by intro d hd; cases hd)))
def cl_32921 : CNF.NClause := [(46,false),(15,true),(92,false),(77,false),(78,false),(79,false)]
theorem der_32921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32921 :=
  CNF.rup_sound cl_32921 [cl_27444,cl_32912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27444 v h) (hints_cons _ _ _ (der_32912 v h) (by intro d hd; cases hd)))
def cl_32922 : CNF.NClause := [(46,false),(79,false),(77,true),(92,false),(78,false),(15,true)]
theorem der_32922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32922 :=
  CNF.rup_sound cl_32922 [cl_27445,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27445 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_32923 : CNF.NClause := [(46,false),(78,true),(15,false),(92,false),(77,false),(79,false)]
theorem der_32923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32923 :=
  CNF.rup_sound cl_32923 [cl_27446,cl_27431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27446 v h) (hints_cons _ _ _ (der_27431 v h) (by intro d hd; cases hd)))
def cl_32924 : CNF.NClause := [(46,false),(78,true),(15,false),(81,true),(92,false),(79,false)]
theorem der_32924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32924 :=
  CNF.rup_sound cl_32924 [cl_27448,cl_32923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27448 v h) (hints_cons _ _ _ (der_32923 v h) (by intro d hd; cases hd)))
def cl_32926 : CNF.NClause := [(46,false),(80,true),(15,false),(92,false),(77,false),(78,false)]
theorem der_32926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32926 :=
  CNF.rup_sound cl_32926 [cl_27450,cl_27420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27450 v h) (hints_cons _ _ _ (der_27420 v h) (by intro d hd; cases hd)))
def cl_32927 : CNF.NClause := [(46,false),(15,false),(79,true),(77,true),(92,false),(78,false)]
theorem der_32927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32927 :=
  CNF.rup_sound cl_32927 [cl_27452,cl_32916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27452 v h) (hints_cons _ _ _ (der_32916 v h) (by intro d hd; cases hd)))
def cl_32928 : CNF.NClause := [(46,false),(81,true),(77,true),(15,true),(92,false),(78,false)]
theorem der_32928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32928 :=
  CNF.rup_sound cl_32928 [cl_27453,cl_32917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27453 v h) (hints_cons _ _ _ (der_32917 v h) (by intro d hd; cases hd)))
def cl_32929 : CNF.NClause := [(46,false),(78,true),(15,false),(81,true),(92,false),(77,false)]
theorem der_32929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32929 :=
  CNF.rup_sound cl_32929 [cl_27454,cl_32923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27454 v h) (hints_cons _ _ _ (der_32923 v h) (by intro d hd; cases hd)))
def cl_32930 : CNF.NClause := [(46,false),(81,true),(78,true),(80,true),(92,false),(77,false)]
theorem der_32930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32930 :=
  CNF.rup_sound cl_32930 [cl_27455,cl_32929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27455 v h) (hints_cons _ _ _ (der_32929 v h) (by intro d hd; cases hd)))
def cl_32931 : CNF.NClause := [(46,false),(78,true),(15,false),(79,true),(77,true),(92,false)]
theorem der_32931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32931 :=
  CNF.rup_sound cl_32931 [cl_27456,cl_32918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27456 v h) (hints_cons _ _ _ (der_32918 v h) (by intro d hd; cases hd)))
def cl_32933 : CNF.NClause := [(46,false),(80,false),(77,true),(78,false),(79,false),(81,false)]
theorem der_32933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32933 :=
  CNF.rup_sound cl_32933 [cl_27460,cl_26327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27460 v h) (hints_cons _ _ _ (der_26327 v h) (by intro d hd; cases hd)))
def cl_32934 : CNF.NClause := [(46,false),(77,false),(79,false),(81,false),(80,false),(92,true)]
theorem der_32934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32934 :=
  CNF.rup_sound cl_32934 [cl_27462,cl_27459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27462 v h) (hints_cons _ _ _ (der_27459 v h) (by intro d hd; cases hd)))
def cl_32935 : CNF.NClause := [(46,false),(15,false),(77,true),(79,false),(81,false),(80,false)]
theorem der_32935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32935 :=
  CNF.rup_sound cl_32935 [cl_27463,cl_32933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27463 v h) (hints_cons _ _ _ (der_32933 v h) (by intro d hd; cases hd)))
def cl_32936 : CNF.NClause := [(46,false),(77,true),(78,true),(79,false),(81,false),(80,false)]
theorem der_32936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32936 :=
  CNF.rup_sound cl_32936 [cl_27464,cl_32935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27464 v h) (hints_cons _ _ _ (der_32935 v h) (by intro d hd; cases hd)))
def cl_32937 : CNF.NClause := [(46,false),(81,false),(77,false),(78,false),(80,false),(92,true)]
theorem der_32937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32937 :=
  CNF.rup_sound cl_32937 [cl_27466,cl_27459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27466 v h) (hints_cons _ _ _ (der_27459 v h) (by intro d hd; cases hd)))
def cl_32938 : CNF.NClause := [(46,false),(81,false),(78,false),(15,false),(80,false),(92,true)]
theorem der_32938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32938 :=
  CNF.rup_sound cl_32938 [cl_27467,cl_27458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27467 v h) (hints_cons _ _ _ (der_27458 v h) (by intro d hd; cases hd)))
def cl_32939 : CNF.NClause := [(46,false),(81,false),(78,false),(15,true),(80,false),(92,true)]
theorem der_32939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32939 :=
  CNF.rup_sound cl_32939 [cl_27468,cl_32937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27468 v h) (hints_cons _ _ _ (der_32937 v h) (by intro d hd; cases hd)))
def cl_32940 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(81,false),(80,false)]
theorem der_32940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32940 :=
  CNF.rup_sound cl_32940 [cl_27469,cl_32897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27469 v h) (hints_cons _ _ _ (der_32897 v h) (by intro d hd; cases hd)))
def cl_32941 : CNF.NClause := [(46,false),(81,false),(78,true),(77,false),(80,false),(92,true)]
theorem der_32941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32941 :=
  CNF.rup_sound cl_32941 [cl_27470,cl_32940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27470 v h) (hints_cons _ _ _ (der_32940 v h) (by intro d hd; cases hd)))
def cl_32942 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(81,false),(80,false)]
theorem der_32942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32942 :=
  CNF.rup_sound cl_32942 [cl_27471,cl_32935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27471 v h) (hints_cons _ _ _ (der_32935 v h) (by intro d hd; cases hd)))
def cl_32943 : CNF.NClause := [(46,false),(78,false),(80,true),(15,false),(79,false),(81,false)]
theorem der_32943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32943 :=
  CNF.rup_sound cl_32943 [cl_27473,cl_32071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27473 v h) (hints_cons _ _ _ (der_32071 v h) (by intro d hd; cases hd)))
def cl_32944 : CNF.NClause := [(46,false),(78,false),(80,true),(77,false),(79,false),(81,false)]
theorem der_32944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32944 :=
  CNF.rup_sound cl_32944 [cl_27474,cl_32943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27474 v h) (hints_cons _ _ _ (der_32943 v h) (by intro d hd; cases hd)))
def cl_32945 : CNF.NClause := [(46,false),(77,true),(78,false),(79,false),(81,false),(15,true)]
theorem der_32945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32945 :=
  CNF.rup_sound cl_32945 [cl_27475,cl_32922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27475 v h) (hints_cons _ _ _ (der_32922 v h) (by intro d hd; cases hd)))
def cl_32947 : CNF.NClause := [(46,false),(80,true),(77,false),(79,false),(81,false),(92,true)]
theorem der_32947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32947 :=
  CNF.rup_sound cl_32947 [cl_27477,cl_32944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27477 v h) (hints_cons _ _ _ (der_32944 v h) (by intro d hd; cases hd)))
def cl_32948 : CNF.NClause := [(46,false),(15,false),(80,true),(79,false),(81,false),(92,true)]
theorem der_32948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32948 :=
  CNF.rup_sound cl_32948 [cl_27478,cl_32943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27478 v h) (hints_cons _ _ _ (der_32943 v h) (by intro d hd; cases hd)))
def cl_32949 : CNF.NClause := [(46,false),(77,true),(80,true),(15,true),(79,false),(81,false)]
theorem der_32949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32949 :=
  CNF.rup_sound cl_32949 [cl_27479,cl_32902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27479 v h) (hints_cons _ _ _ (der_32902 v h) (by intro d hd; cases hd)))
def cl_32950 : CNF.NClause := [(46,false),(78,false),(80,true),(77,false),(15,true),(81,false)]
theorem der_32950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32950 :=
  CNF.rup_sound cl_32950 [cl_27481,cl_32903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27481 v h) (hints_cons _ _ _ (der_32903 v h) (by intro d hd; cases hd)))
def cl_32951 : CNF.NClause := [(46,false),(78,false),(80,true),(77,true),(15,false),(81,false)]
theorem der_32951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32951 :=
  CNF.rup_sound cl_32951 [cl_27482,cl_32904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27482 v h) (hints_cons _ _ _ (der_32904 v h) (by intro d hd; cases hd)))
def cl_32952 : CNF.NClause := [(46,false),(78,false),(77,true),(15,true),(81,false),(92,true)]
theorem der_32952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32952 :=
  CNF.rup_sound cl_32952 [cl_27483,cl_32945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27483 v h) (hints_cons _ _ _ (der_32945 v h) (by intro d hd; cases hd)))
def cl_32953 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(81,false),(92,true)]
theorem der_32953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32953 :=
  CNF.rup_sound cl_32953 [cl_27484,cl_32940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27484 v h) (hints_cons _ _ _ (der_32940 v h) (by intro d hd; cases hd)))
def cl_32954 : CNF.NClause := [(46,false),(81,false),(78,true),(79,true),(77,false),(92,true)]
theorem der_32954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32954 :=
  CNF.rup_sound cl_32954 [cl_27485,cl_32953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27485 v h) (hints_cons _ _ _ (der_32953 v h) (by intro d hd; cases hd)))
def cl_32955 : CNF.NClause := [(46,false),(15,false),(80,true),(79,true),(77,true),(81,false)]
theorem der_32955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32955 :=
  CNF.rup_sound cl_32955 [cl_27486,cl_32951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27486 v h) (hints_cons _ _ _ (der_32951 v h) (by intro d hd; cases hd)))
def cl_32956 : CNF.NClause := [(46,false),(81,true),(77,false),(78,false),(79,false),(80,false)]
theorem der_32956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32956 :=
  CNF.rup_sound cl_32956 [cl_27489,cl_27488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27489 v h) (hints_cons _ _ _ (der_27488 v h) (by intro d hd; cases hd)))
def cl_32957 : CNF.NClause := [(46,false),(78,false),(15,false),(77,true),(79,false),(80,false)]
theorem der_32957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32957 :=
  CNF.rup_sound cl_32957 [cl_27490,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27490 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_32958 : CNF.NClause := [(46,false),(77,true),(78,false),(79,false),(80,false),(15,true)]
theorem der_32958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32958 :=
  CNF.rup_sound cl_32958 [cl_27491,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27491 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_32959 : CNF.NClause := [(46,false),(78,true),(15,false),(77,false),(79,false),(80,false)]
theorem der_32959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32959 :=
  CNF.rup_sound cl_32959 [cl_27492,cl_32923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27492 v h) (hints_cons _ _ _ (der_32923 v h) (by intro d hd; cases hd)))
def cl_32960 : CNF.NClause := [(46,false),(80,false),(78,true),(77,false),(79,false),(92,true)]
theorem der_32960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32960 :=
  CNF.rup_sound cl_32960 [cl_27493,cl_32959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27493 v h) (hints_cons _ _ _ (der_32959 v h) (by intro d hd; cases hd)))
def cl_32961 : CNF.NClause := [(46,false),(78,true),(15,false),(77,true),(79,false),(80,false)]
theorem der_32961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32961 :=
  CNF.rup_sound cl_32961 [cl_27494,cl_32935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27494 v h) (hints_cons _ _ _ (der_32935 v h) (by intro d hd; cases hd)))
def cl_32962 : CNF.NClause := [(46,false),(81,true),(77,true),(15,true),(79,false),(80,false)]
theorem der_32962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32962 :=
  CNF.rup_sound cl_32962 [cl_27495,cl_32914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27495 v h) (hints_cons _ _ _ (der_32914 v h) (by intro d hd; cases hd)))
def cl_32963 : CNF.NClause := [(46,false),(78,false),(77,false),(15,false),(80,false),(92,true)]
theorem der_32963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32963 :=
  CNF.rup_sound cl_32963 [cl_27496,cl_32937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27496 v h) (hints_cons _ _ _ (der_32937 v h) (by intro d hd; cases hd)))
def cl_32964 : CNF.NClause := [(46,false),(78,false),(81,true),(15,true),(77,false),(80,false)]
theorem der_32964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32964 :=
  CNF.rup_sound cl_32964 [cl_27497,cl_32956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27497 v h) (hints_cons _ _ _ (der_32956 v h) (by intro d hd; cases hd)))
def cl_32965 : CNF.NClause := [(46,false),(81,true),(77,true),(15,false),(78,false),(80,false)]
theorem der_32965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32965 :=
  CNF.rup_sound cl_32965 [cl_27498,cl_32957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27498 v h) (hints_cons _ _ _ (der_32957 v h) (by intro d hd; cases hd)))
def cl_32966 : CNF.NClause := [(46,false),(78,false),(77,true),(15,true),(80,false),(92,true)]
theorem der_32966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32966 :=
  CNF.rup_sound cl_32966 [cl_27499,cl_32958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27499 v h) (hints_cons _ _ _ (der_32958 v h) (by intro d hd; cases hd)))
def cl_32967 : CNF.NClause := [(46,false),(78,true),(15,false),(79,true),(77,false),(80,false)]
theorem der_32967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32967 :=
  CNF.rup_sound cl_32967 [cl_27500,cl_32940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27500 v h) (hints_cons _ _ _ (der_32940 v h) (by intro d hd; cases hd)))
def cl_32968 : CNF.NClause := [(46,false),(80,false),(78,true),(79,true),(77,false),(92,true)]
theorem der_32968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32968 :=
  CNF.rup_sound cl_32968 [cl_27501,cl_32967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27501 v h) (hints_cons _ _ _ (der_32967 v h) (by intro d hd; cases hd)))
def cl_32969 : CNF.NClause := [(46,false),(78,true),(15,false),(79,true),(77,true),(80,false)]
theorem der_32969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32969 :=
  CNF.rup_sound cl_32969 [cl_27502,cl_32942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27502 v h) (hints_cons _ _ _ (der_32942 v h) (by intro d hd; cases hd)))
def cl_32970 : CNF.NClause := [(46,false),(81,true),(15,true),(77,true),(80,false),(92,true)]
theorem der_32970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32970 :=
  CNF.rup_sound cl_32970 [cl_27503,cl_32966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27503 v h) (hints_cons _ _ _ (der_32966 v h) (by intro d hd; cases hd)))
def cl_32971 : CNF.NClause := [(46,false),(15,false),(81,true),(77,false),(78,false),(79,false)]
theorem der_32971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32971 :=
  CNF.rup_sound cl_32971 [cl_27504,cl_27488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27504 v h) (hints_cons _ _ _ (der_27488 v h) (by intro d hd; cases hd)))
def cl_32972 : CNF.NClause := [(46,false),(80,true),(77,false),(78,false),(79,false),(92,true)]
theorem der_32972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32972 :=
  CNF.rup_sound cl_32972 [cl_27505,cl_32944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27505 v h) (hints_cons _ _ _ (der_32944 v h) (by intro d hd; cases hd)))
def cl_32973 : CNF.NClause := [(46,false),(92,true),(77,true),(78,false),(79,false),(15,true)]
theorem der_32973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32973 :=
  CNF.rup_sound cl_32973 [cl_27506,cl_32952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27506 v h) (hints_cons _ _ _ (der_32952 v h) (by intro d hd; cases hd)))
def cl_32974 : CNF.NClause := [(46,false),(78,true),(15,false),(80,true),(77,false),(79,false)]
theorem der_32974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32974 :=
  CNF.rup_sound cl_32974 [cl_27507,cl_32923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27507 v h) (hints_cons _ _ _ (der_32923 v h) (by intro d hd; cases hd)))
def cl_32975 : CNF.NClause := [(46,false),(77,false),(78,true),(80,true),(81,true),(79,false)]
theorem der_32975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32975 :=
  CNF.rup_sound cl_32975 [cl_27508,cl_32974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27508 v h) (hints_cons _ _ _ (der_32974 v h) (by intro d hd; cases hd)))
def cl_32976 : CNF.NClause := [(46,false),(78,true),(15,false),(80,true),(79,false),(92,true)]
theorem der_32976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32976 :=
  CNF.rup_sound cl_32976 [cl_27509,cl_32974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27509 v h) (hints_cons _ _ _ (der_32974 v h) (by intro d hd; cases hd)))
def cl_32977 : CNF.NClause := [(46,false),(80,true),(78,true),(15,true),(81,true),(79,false)]
theorem der_32977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32977 :=
  CNF.rup_sound cl_32977 [cl_27510,cl_32975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27510 v h) (hints_cons _ _ _ (der_32975 v h) (by intro d hd; cases hd)))
def cl_32978 : CNF.NClause := [(46,false),(80,true),(15,false),(81,true),(77,false),(78,false)]
theorem der_32978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32978 :=
  CNF.rup_sound cl_32978 [cl_27511,cl_32926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27511 v h) (hints_cons _ _ _ (der_32926 v h) (by intro d hd; cases hd)))
def cl_32979 : CNF.NClause := [(46,false),(80,true),(81,true),(77,false),(78,false),(92,true)]
theorem der_32979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32979 :=
  CNF.rup_sound cl_32979 [cl_27512,cl_32972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27512 v h) (hints_cons _ _ _ (der_32972 v h) (by intro d hd; cases hd)))
def cl_32980 : CNF.NClause := [(46,false),(80,true),(79,true),(81,true),(78,false),(92,true)]
theorem der_32980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32980 :=
  CNF.rup_sound cl_32980 [cl_27514,cl_32979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27514 v h) (hints_cons _ _ _ (der_32979 v h) (by intro d hd; cases hd)))
def cl_32981 : CNF.NClause := [(46,false),(15,false),(80,true),(79,true),(81,true),(77,false)]
theorem der_32981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32981 :=
  CNF.rup_sound cl_32981 [cl_27515,cl_32978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27515 v h) (hints_cons _ _ _ (der_32978 v h) (by intro d hd; cases hd)))
def cl_32982 : CNF.NClause := [(46,false),(77,false),(78,true),(15,true),(79,true),(92,true)]
theorem der_32982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32982 :=
  CNF.rup_sound cl_32982 [cl_27516,cl_32968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27516 v h) (hints_cons _ _ _ (der_32968 v h) (by intro d hd; cases hd)))
def cl_32983 : CNF.NClause := [(46,false),(78,true),(15,false),(80,true),(81,true),(92,true)]
theorem der_32983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32983 :=
  CNF.rup_sound cl_32983 [cl_27517,cl_32976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27517 v h) (hints_cons _ _ _ (der_32976 v h) (by intro d hd; cases hd)))
def cl_32984 : CNF.NClause := [(46,false),(80,true),(78,true),(15,true),(77,true),(81,true)]
theorem der_32984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32984 :=
  CNF.rup_sound cl_32984 [cl_27518,cl_32977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27518 v h) (hints_cons _ _ _ (der_32977 v h) (by intro d hd; cases hd)))
def cl_32985 : CNF.NClause := [(42,false),(90,false),(66,true),(69,false),(83,false),(80,false)]
theorem der_32985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32985 :=
  CNF.rup_sound cl_32985 [cl_27525,cl_27519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27525 v h) (hints_cons _ _ _ (der_27519 v h) (by intro d hd; cases hd)))
def cl_32986 : CNF.NClause := [(42,false),(83,false),(69,true),(90,false),(66,false),(80,false)]
theorem der_32986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32986 :=
  CNF.rup_sound cl_32986 [cl_27527,cl_27526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27527 v h) (hints_cons _ _ _ (der_27526 v h) (by intro d hd; cases hd)))
def cl_32987 : CNF.NClause := [(42,false),(66,true),(11,false),(90,false),(83,false),(80,false)]
theorem der_32987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32987 :=
  CNF.rup_sound cl_32987 [cl_27528,cl_27521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27528 v h) (hints_cons _ _ _ (der_27521 v h) (by intro d hd; cases hd)))
def cl_32988 : CNF.NClause := [(42,false),(90,false),(11,true),(66,true),(83,false),(80,false)]
theorem der_32988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32988 :=
  CNF.rup_sound cl_32988 [cl_27529,cl_32985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27529 v h) (hints_cons _ _ _ (der_32985 v h) (by intro d hd; cases hd)))
def cl_32990 : CNF.NClause := [(42,false),(83,false),(80,true),(90,false),(66,false),(69,false)]
theorem der_32990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32990 :=
  CNF.rup_sound cl_32990 [cl_27538,cl_27537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27538 v h) (hints_cons _ _ _ (der_27537 v h) (by intro d hd; cases hd)))
def cl_32991 : CNF.NClause := [(42,false),(11,false),(66,true),(90,false),(69,false),(83,false)]
theorem der_32991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32991 :=
  CNF.rup_sound cl_32991 [cl_27539,cl_27524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27539 v h) (hints_cons _ _ _ (der_27524 v h) (by intro d hd; cases hd)))
def cl_32993 : CNF.NClause := [(42,false),(69,true),(11,false),(90,false),(66,false),(83,false)]
theorem der_32993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32993 :=
  CNF.rup_sound cl_32993 [cl_27541,cl_27526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27541 v h) (hints_cons _ _ _ (der_27526 v h) (by intro d hd; cases hd)))
def cl_32994 : CNF.NClause := [(42,false),(69,true),(72,true),(90,false),(66,false),(83,false)]
theorem der_32994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32994 :=
  CNF.rup_sound cl_32994 [cl_27542,cl_32986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27542 v h) (hints_cons _ _ _ (der_32986 v h) (by intro d hd; cases hd)))
def cl_32995 : CNF.NClause := [(42,false),(80,true),(11,false),(66,true),(90,false),(83,false)]
theorem der_32995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32995 :=
  CNF.rup_sound cl_32995 [cl_27543,cl_32991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27543 v h) (hints_cons _ _ _ (der_32991 v h) (by intro d hd; cases hd)))
def cl_32996 : CNF.NClause := [(42,false),(66,true),(11,true),(72,true),(90,false),(83,false)]
theorem der_32996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32996 :=
  CNF.rup_sound cl_32996 [cl_27544,cl_32988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27544 v h) (hints_cons _ _ _ (der_32988 v h) (by intro d hd; cases hd)))
def cl_32997 : CNF.NClause := [(42,false),(72,false),(90,false),(69,false),(80,false),(66,true)]
theorem der_32997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32997 :=
  CNF.rup_sound cl_32997 [cl_27547,cl_27519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27547 v h) (hints_cons _ _ _ (der_27519 v h) (by intro d hd; cases hd)))
def cl_32998 : CNF.NClause := [(42,false),(69,true),(72,false),(90,false),(66,false),(80,false)]
theorem der_32998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32998 :=
  CNF.rup_sound cl_32998 [cl_27549,cl_27520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27549 v h) (hints_cons _ _ _ (der_27520 v h) (by intro d hd; cases hd)))
def cl_32999 : CNF.NClause := [(42,false),(66,true),(11,false),(72,false),(90,false),(80,false)]
theorem der_32999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32999 :=
  CNF.rup_sound cl_32999 [cl_27550,cl_27521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27550 v h) (hints_cons _ _ _ (der_27521 v h) (by intro d hd; cases hd)))
def cl_33000 : CNF.NClause := [(42,false),(90,false),(69,true),(11,true),(72,false),(80,false)]
theorem der_33000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33000 :=
  CNF.rup_sound cl_33000 [cl_27551,cl_27522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27551 v h) (hints_cons _ _ _ (der_27522 v h) (by intro d hd; cases hd)))
def cl_33001 : CNF.NClause := [(42,false),(83,true),(90,false),(66,false),(69,false),(80,false)]
theorem der_33001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33001 :=
  CNF.rup_sound cl_33001 [cl_27553,cl_27552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27553 v h) (hints_cons _ _ _ (der_27552 v h) (by intro d hd; cases hd)))
def cl_33003 : CNF.NClause := [(42,false),(69,true),(11,false),(90,false),(66,false),(80,false)]
theorem der_33003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33003 :=
  CNF.rup_sound cl_33003 [cl_27556,cl_27526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27556 v h) (hints_cons _ _ _ (der_27526 v h) (by intro d hd; cases hd)))
def cl_33004 : CNF.NClause := [(42,false),(66,true),(11,false),(90,false),(80,false),(83,true)]
theorem der_33004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33004 :=
  CNF.rup_sound cl_33004 [cl_27558,cl_32999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27558 v h) (hints_cons _ _ _ (der_32999 v h) (by intro d hd; cases hd)))
def cl_33005 : CNF.NClause := [(42,false),(66,true),(69,true),(11,true),(90,false),(80,false)]
theorem der_33005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33005 :=
  CNF.rup_sound cl_33005 [cl_27559,cl_33000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27559 v h) (hints_cons _ _ _ (der_33000 v h) (by intro d hd; cases hd)))
def cl_33006 : CNF.NClause := [(42,false),(69,false),(80,true),(72,false),(90,false),(66,false)]
theorem der_33006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33006 :=
  CNF.rup_sound cl_33006 [cl_27561,cl_27560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27561 v h) (hints_cons _ _ _ (der_27560 v h) (by intro d hd; cases hd)))
def cl_33007 : CNF.NClause := [(42,false),(11,false),(66,true),(72,false),(90,false),(69,false)]
theorem der_33007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33007 :=
  CNF.rup_sound cl_33007 [cl_27562,cl_32997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27562 v h) (hints_cons _ _ _ (der_32997 v h) (by intro d hd; cases hd)))
def cl_33008 : CNF.NClause := [(42,false),(69,false),(66,true),(72,false),(90,false),(11,true)]
theorem der_33008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33008 :=
  CNF.rup_sound cl_33008 [cl_27563,cl_32997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27563 v h) (hints_cons _ _ _ (der_32997 v h) (by intro d hd; cases hd)))
def cl_33009 : CNF.NClause := [(42,false),(69,true),(11,false),(72,false),(90,false),(66,false)]
theorem der_33009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33009 :=
  CNF.rup_sound cl_33009 [cl_27564,cl_33003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27564 v h) (hints_cons _ _ _ (der_33003 v h) (by intro d hd; cases hd)))
def cl_33010 : CNF.NClause := [(42,false),(69,true),(72,false),(90,false),(66,false),(83,true)]
theorem der_33010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33010 :=
  CNF.rup_sound cl_33010 [cl_27565,cl_32998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27565 v h) (hints_cons _ _ _ (der_32998 v h) (by intro d hd; cases hd)))
def cl_33011 : CNF.NClause := [(42,false),(69,true),(80,true),(11,false),(72,false),(90,false)]
theorem der_33011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33011 :=
  CNF.rup_sound cl_33011 [cl_27566,cl_33009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27566 v h) (hints_cons _ _ _ (der_33009 v h) (by intro d hd; cases hd)))
def cl_33012 : CNF.NClause := [(42,false),(80,true),(69,true),(72,false),(90,false),(83,true)]
theorem der_33012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33012 :=
  CNF.rup_sound cl_33012 [cl_27567,cl_33011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27567 v h) (hints_cons _ _ _ (der_33011 v h) (by intro d hd; cases hd)))
def cl_33013 : CNF.NClause := [(42,false),(80,true),(11,false),(90,false),(66,false),(69,false)]
theorem der_33013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33013 :=
  CNF.rup_sound cl_33013 [cl_27568,cl_27560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27568 v h) (hints_cons _ _ _ (der_27560 v h) (by intro d hd; cases hd)))
def cl_33014 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(90,false),(69,false)]
theorem der_33014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33014 :=
  CNF.rup_sound cl_33014 [cl_27570,cl_32991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27570 v h) (hints_cons _ _ _ (der_32991 v h) (by intro d hd; cases hd)))
def cl_33015 : CNF.NClause := [(42,false),(69,false),(80,true),(66,true),(72,true),(90,false)]
theorem der_33015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33015 :=
  CNF.rup_sound cl_33015 [cl_27571,cl_33014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27571 v h) (hints_cons _ _ _ (der_33014 v h) (by intro d hd; cases hd)))
def cl_33016 : CNF.NClause := [(42,false),(69,true),(11,false),(90,false),(66,false),(83,true)]
theorem der_33016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33016 :=
  CNF.rup_sound cl_33016 [cl_27572,cl_33003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27572 v h) (hints_cons _ _ _ (der_33003 v h) (by intro d hd; cases hd)))
def cl_33017 : CNF.NClause := [(42,false),(69,true),(80,true),(11,false),(90,false),(83,true)]
theorem der_33017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33017 :=
  CNF.rup_sound cl_33017 [cl_27574,cl_33016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27574 v h) (hints_cons _ _ _ (der_33016 v h) (by intro d hd; cases hd)))
def cl_33018 : CNF.NClause := [(42,false),(80,true),(69,true),(72,true),(90,false),(83,true)]
theorem der_33018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33018 :=
  CNF.rup_sound cl_33018 [cl_27575,cl_33017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27575 v h) (hints_cons _ _ _ (der_33017 v h) (by intro d hd; cases hd)))
def cl_33019 : CNF.NClause := [(42,false),(69,false),(72,false),(66,true),(83,false),(80,false)]
theorem der_33019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33019 :=
  CNF.rup_sound cl_33019 [cl_27578,cl_32997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27578 v h) (hints_cons _ _ _ (der_32997 v h) (by intro d hd; cases hd)))
def cl_33020 : CNF.NClause := [(42,false),(69,true),(72,false),(66,false),(83,false),(80,false)]
theorem der_33020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33020 :=
  CNF.rup_sound cl_33020 [cl_27580,cl_27579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27580 v h) (hints_cons _ _ _ (der_27579 v h) (by intro d hd; cases hd)))
def cl_33021 : CNF.NClause := [(42,false),(66,true),(11,true),(72,false),(83,false),(80,false)]
theorem der_33021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33021 :=
  CNF.rup_sound cl_33021 [cl_27582,cl_33019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27582 v h) (hints_cons _ _ _ (der_33019 v h) (by intro d hd; cases hd)))
def cl_33022 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(83,false),(80,false)]
theorem der_33022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33022 :=
  CNF.rup_sound cl_33022 [cl_27585,cl_27577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27585 v h) (hints_cons _ _ _ (der_27577 v h) (by intro d hd; cases hd)))
def cl_33023 : CNF.NClause := [(42,false),(83,false),(66,true),(72,true),(69,false),(80,false)]
theorem der_33023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33023 :=
  CNF.rup_sound cl_33023 [cl_27586,cl_33022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27586 v h) (hints_cons _ _ _ (der_33022 v h) (by intro d hd; cases hd)))
def cl_33024 : CNF.NClause := [(42,false),(83,false),(69,true),(66,false),(11,true),(80,false)]
theorem der_33024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33024 :=
  CNF.rup_sound cl_33024 [cl_27588,cl_32986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27588 v h) (hints_cons _ _ _ (der_32986 v h) (by intro d hd; cases hd)))
def cl_33025 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(83,false),(80,false)]
theorem der_33025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33025 :=
  CNF.rup_sound cl_33025 [cl_27589,cl_32987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27589 v h) (hints_cons _ _ _ (der_32987 v h) (by intro d hd; cases hd)))
def cl_33026 : CNF.NClause := [(42,false),(83,false),(69,true),(11,true),(80,false),(90,true)]
theorem der_33026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33026 :=
  CNF.rup_sound cl_33026 [cl_27590,cl_33024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27590 v h) (hints_cons _ _ _ (der_33024 v h) (by intro d hd; cases hd)))
def cl_33027 : CNF.NClause := [(42,false),(11,true),(72,false),(66,false),(69,false),(83,false)]
theorem der_33027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33027 :=
  CNF.rup_sound cl_33027 [cl_27592,cl_27576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27592 v h) (hints_cons _ _ _ (der_27576 v h) (by intro d hd; cases hd)))
def cl_33028 : CNF.NClause := [(42,false),(11,false),(66,true),(72,false),(69,false),(83,false)]
theorem der_33028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33028 :=
  CNF.rup_sound cl_33028 [cl_27593,cl_27577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27593 v h) (hints_cons _ _ _ (der_27577 v h) (by intro d hd; cases hd)))
def cl_33029 : CNF.NClause := [(42,false),(80,true),(66,true),(72,false),(69,false),(83,false)]
theorem der_33029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33029 :=
  CNF.rup_sound cl_33029 [cl_27594,cl_33028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27594 v h) (hints_cons _ _ _ (der_33028 v h) (by intro d hd; cases hd)))
def cl_33030 : CNF.NClause := [(42,false),(69,true),(11,false),(72,false),(66,false),(83,false)]
theorem der_33030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33030 :=
  CNF.rup_sound cl_33030 [cl_27595,cl_27579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27595 v h) (hints_cons _ _ _ (der_27579 v h) (by intro d hd; cases hd)))
def cl_33031 : CNF.NClause := [(42,false),(11,true),(80,true),(72,false),(66,false),(83,false)]
theorem der_33031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33031 :=
  CNF.rup_sound cl_33031 [cl_27596,cl_33027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27596 v h) (hints_cons _ _ _ (der_33027 v h) (by intro d hd; cases hd)))
def cl_33033 : CNF.NClause := [(42,false),(11,false),(72,true),(66,false),(69,false),(83,false)]
theorem der_33033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33033 :=
  CNF.rup_sound cl_33033 [cl_27599,cl_27583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27599 v h) (hints_cons _ _ _ (der_27583 v h) (by intro d hd; cases hd)))
def cl_33034 : CNF.NClause := [(42,false),(69,false),(72,true),(66,false),(83,false),(90,true)]
theorem der_33034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33034 :=
  CNF.rup_sound cl_33034 [cl_27600,cl_33033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27600 v h) (hints_cons _ _ _ (der_33033 v h) (by intro d hd; cases hd)))
def cl_33035 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(69,false),(83,false)]
theorem der_33035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33035 :=
  CNF.rup_sound cl_33035 [cl_27601,cl_32991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27601 v h) (hints_cons _ _ _ (der_32991 v h) (by intro d hd; cases hd)))
def cl_33036 : CNF.NClause := [(42,false),(66,true),(80,true),(11,true),(69,false),(83,false)]
theorem der_33036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33036 :=
  CNF.rup_sound cl_33036 [cl_27602,cl_33029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27602 v h) (hints_cons _ _ _ (der_33029 v h) (by intro d hd; cases hd)))
def cl_33037 : CNF.NClause := [(42,false),(80,true),(11,false),(72,true),(66,false),(83,false)]
theorem der_33037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33037 :=
  CNF.rup_sound cl_33037 [cl_27603,cl_33033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27603 v h) (hints_cons _ _ _ (der_33033 v h) (by intro d hd; cases hd)))
def cl_33038 : CNF.NClause := [(42,false),(72,true),(69,true),(80,true),(66,false),(83,false)]
theorem der_33038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33038 :=
  CNF.rup_sound cl_33038 [cl_27604,cl_33037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27604 v h) (hints_cons _ _ _ (der_33037 v h) (by intro d hd; cases hd)))
def cl_33040 : CNF.NClause := [(42,false),(83,true),(72,false),(66,false),(69,false),(80,false)]
theorem der_33040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33040 :=
  CNF.rup_sound cl_33040 [cl_27608,cl_27607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27608 v h) (hints_cons _ _ _ (der_27607 v h) (by intro d hd; cases hd)))
def cl_33041 : CNF.NClause := [(42,false),(66,true),(11,false),(72,false),(69,false),(80,false)]
theorem der_33041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33041 :=
  CNF.rup_sound cl_33041 [cl_27609,cl_33028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27609 v h) (hints_cons _ _ _ (der_33028 v h) (by intro d hd; cases hd)))
def cl_33042 : CNF.NClause := [(42,false),(69,true),(11,false),(72,false),(66,false),(80,false)]
theorem der_33042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33042 :=
  CNF.rup_sound cl_33042 [cl_27611,cl_27579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27611 v h) (hints_cons _ _ _ (der_27579 v h) (by intro d hd; cases hd)))
def cl_33044 : CNF.NClause := [(42,false),(66,true),(69,true),(11,true),(72,false),(80,false)]
theorem der_33044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33044 :=
  CNF.rup_sound cl_33044 [cl_27614,cl_33000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27614 v h) (hints_cons _ _ _ (der_33000 v h) (by intro d hd; cases hd)))
def cl_33045 : CNF.NClause := [(42,false),(66,false),(69,false),(80,false),(83,true),(11,false)]
theorem der_33045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33045 :=
  CNF.rup_sound cl_33045 [cl_27615,cl_27552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27615 v h) (hints_cons _ _ _ (der_27552 v h) (by intro d hd; cases hd)))
def cl_33046 : CNF.NClause := [(42,false),(83,true),(66,false),(69,false),(80,false),(11,true)]
theorem der_33046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33046 :=
  CNF.rup_sound cl_33046 [cl_27616,cl_33040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27616 v h) (hints_cons _ _ _ (der_33040 v h) (by intro d hd; cases hd)))
def cl_33047 : CNF.NClause := [(42,false),(66,true),(11,false),(69,false),(80,false),(83,true)]
theorem der_33047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33047 :=
  CNF.rup_sound cl_33047 [cl_27617,cl_33041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27617 v h) (hints_cons _ _ _ (der_33041 v h) (by intro d hd; cases hd)))
def cl_33048 : CNF.NClause := [(42,false),(90,true),(72,true),(69,false),(80,false),(66,true)]
theorem der_33048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33048 :=
  CNF.rup_sound cl_33048 [cl_27618,cl_33023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27618 v h) (hints_cons _ _ _ (der_33023 v h) (by intro d hd; cases hd)))
def cl_33049 : CNF.NClause := [(42,false),(69,true),(11,false),(66,false),(80,false),(83,true)]
theorem der_33049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33049 :=
  CNF.rup_sound cl_33049 [cl_27619,cl_33042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27619 v h) (hints_cons _ _ _ (der_33042 v h) (by intro d hd; cases hd)))
def cl_33050 : CNF.NClause := [(42,false),(80,false),(69,true),(72,true),(66,false),(83,true)]
theorem der_33050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33050 :=
  CNF.rup_sound cl_33050 [cl_27620,cl_33049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27620 v h) (hints_cons _ _ _ (der_33049 v h) (by intro d hd; cases hd)))
def cl_33051 : CNF.NClause := [(42,false),(66,true),(11,false),(72,true),(80,false),(83,true)]
theorem der_33051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33051 :=
  CNF.rup_sound cl_33051 [cl_27621,cl_33004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27621 v h) (hints_cons _ _ _ (der_33004 v h) (by intro d hd; cases hd)))
def cl_33052 : CNF.NClause := [(42,false),(66,true),(69,true),(11,true),(72,true),(80,false)]
theorem der_33052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33052 :=
  CNF.rup_sound cl_33052 [cl_27622,cl_33005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27622 v h) (hints_cons _ _ _ (der_33005 v h) (by intro d hd; cases hd)))
def cl_33053 : CNF.NClause := [(42,false),(11,false),(72,false),(66,false),(69,false),(83,true)]
theorem der_33053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33053 :=
  CNF.rup_sound cl_33053 [cl_27623,cl_27607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27623 v h) (hints_cons _ _ _ (der_27607 v h) (by intro d hd; cases hd)))
def cl_33054 : CNF.NClause := [(42,false),(90,true),(72,false),(66,false),(69,false),(83,true)]
theorem der_33054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33054 :=
  CNF.rup_sound cl_33054 [cl_27624,cl_33053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27624 v h) (hints_cons _ _ _ (der_33053 v h) (by intro d hd; cases hd)))
def cl_33056 : CNF.NClause := [(42,false),(80,true),(66,true),(72,false),(69,false),(90,true)]
theorem der_33056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33056 :=
  CNF.rup_sound cl_33056 [cl_27626,cl_33029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27626 v h) (hints_cons _ _ _ (der_33029 v h) (by intro d hd; cases hd)))
def cl_33057 : CNF.NClause := [(42,false),(69,true),(11,false),(72,false),(66,false),(83,true)]
theorem der_33057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33057 :=
  CNF.rup_sound cl_33057 [cl_27627,cl_33049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27627 v h) (hints_cons _ _ _ (der_33049 v h) (by intro d hd; cases hd)))
def cl_33060 : CNF.NClause := [(42,false),(11,false),(66,false),(69,false),(83,true),(90,true)]
theorem der_33060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33060 :=
  CNF.rup_sound cl_33060 [cl_27631,cl_33045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27631 v h) (hints_cons _ _ _ (der_33045 v h) (by intro d hd; cases hd)))
def cl_33061 : CNF.NClause := [(42,false),(80,true),(90,true),(66,false),(69,false),(83,true)]
theorem der_33061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33061 :=
  CNF.rup_sound cl_33061 [cl_27632,cl_33060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27632 v h) (hints_cons _ _ _ (der_33060 v h) (by intro d hd; cases hd)))
def cl_33063 : CNF.NClause := [(42,false),(69,true),(80,true),(11,false),(66,false),(83,true)]
theorem der_33063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33063 :=
  CNF.rup_sound cl_33063 [cl_27635,cl_33017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27635 v h) (hints_cons _ _ _ (der_33017 v h) (by intro d hd; cases hd)))
def cl_33064 : CNF.NClause := [(42,false),(72,true),(69,true),(11,true),(66,false),(83,true)]
theorem der_33064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33064 :=
  CNF.rup_sound cl_33064 [cl_27636,cl_33050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27636 v h) (hints_cons _ _ _ (der_33050 v h) (by intro d hd; cases hd)))
def cl_33066 : CNF.NClause := [(42,false),(69,true),(11,true),(66,true),(72,true),(90,true)]
theorem der_33066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33066 :=
  CNF.rup_sound cl_33066 [cl_27638,cl_33052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27638 v h) (hints_cons _ _ _ (der_33052 v h) (by intro d hd; cases hd)))
def cl_33067 : CNF.NClause := [(34,false),(85,false),(3,true),(87,false),(75,false),(80,false)]
theorem der_33067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33067 :=
  CNF.rup_sound cl_33067 [cl_27642,cl_27640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27642 v h) (hints_cons _ _ _ (der_27640 v h) (by intro d hd; cases hd)))
def cl_33068 : CNF.NClause := [(34,false),(85,false),(3,true),(87,false),(80,false),(70,false)]
theorem der_33068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33068 :=
  CNF.rup_sound cl_33068 [cl_27645,cl_27643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27645 v h) (hints_cons _ _ _ (der_27643 v h) (by intro d hd; cases hd)))
def cl_33069 : CNF.NClause := [(34,false),(75,true),(70,true),(85,false),(87,false),(80,false)]
theorem der_33069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33069 :=
  CNF.rup_sound cl_33069 [cl_27649,cl_27647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27649 v h) (hints_cons _ _ _ (der_27647 v h) (by intro d hd; cases hd)))
def cl_33070 : CNF.NClause := [(34,false),(80,true),(85,false),(87,false),(75,false),(70,false)]
theorem der_33070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33070 :=
  CNF.rup_sound cl_33070 [cl_27652,cl_27650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27652 v h) (hints_cons _ _ _ (der_27650 v h) (by intro d hd; cases hd)))
def cl_33071 : CNF.NClause := [(34,false),(65,false),(80,true),(85,false),(87,false),(75,false)]
theorem der_33071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33071 :=
  CNF.rup_sound cl_33071 [cl_27654,cl_33070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27654 v h) (hints_cons _ _ _ (der_33070 v h) (by intro d hd; cases hd)))
def cl_33072 : CNF.NClause := [(34,false),(80,true),(3,false),(85,false),(87,false),(75,false)]
theorem der_33072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33072 :=
  CNF.rup_sound cl_33072 [cl_27655,cl_27653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27655 v h) (hints_cons _ _ _ (der_27653 v h) (by intro d hd; cases hd)))
def cl_33073 : CNF.NClause := [(34,false),(85,false),(80,true),(65,true),(87,false),(75,false)]
theorem der_33073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33073 :=
  CNF.rup_sound cl_33073 [cl_27656,cl_33072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27656 v h) (hints_cons _ _ _ (der_33072 v h) (by intro d hd; cases hd)))
def cl_33074 : CNF.NClause := [(34,false),(80,true),(85,false),(87,false),(70,false),(65,false)]
theorem der_33074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33074 :=
  CNF.rup_sound cl_33074 [cl_27658,cl_33070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27658 v h) (hints_cons _ _ _ (der_33070 v h) (by intro d hd; cases hd)))
def cl_33075 : CNF.NClause := [(34,false),(80,true),(3,false),(85,false),(87,false),(70,false)]
theorem der_33075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33075 :=
  CNF.rup_sound cl_33075 [cl_27659,cl_33074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27659 v h) (hints_cons _ _ _ (der_33074 v h) (by intro d hd; cases hd)))
def cl_33076 : CNF.NClause := [(34,false),(70,false),(80,true),(85,false),(3,true),(87,false)]
theorem der_33076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33076 :=
  CNF.rup_sound cl_33076 [cl_27660,cl_33074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27660 v h) (hints_cons _ _ _ (der_33074 v h) (by intro d hd; cases hd)))
def cl_33077 : CNF.NClause := [(34,false),(85,false),(80,true),(75,true),(87,false),(65,false)]
theorem der_33077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33077 :=
  CNF.rup_sound cl_33077 [cl_27662,cl_33074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27662 v h) (hints_cons _ _ _ (der_33074 v h) (by intro d hd; cases hd)))
def cl_33079 : CNF.NClause := [(34,false),(80,true),(70,true),(75,true),(85,false),(87,false)]
theorem der_33079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33079 :=
  CNF.rup_sound cl_33079 [cl_27664,cl_33077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27664 v h) (hints_cons _ _ _ (der_33077 v h) (by intro d hd; cases hd)))
def cl_33080 : CNF.NClause := [(34,false),(75,false),(87,false),(3,true),(80,false),(65,false)]
theorem der_33080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33080 :=
  CNF.rup_sound cl_33080 [cl_27669,cl_27640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27669 v h) (hints_cons _ _ _ (der_27640 v h) (by intro d hd; cases hd)))
def cl_33081 : CNF.NClause := [(34,false),(87,false),(65,true),(3,false),(75,false),(80,false)]
theorem der_33081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33081 :=
  CNF.rup_sound cl_33081 [cl_27670,cl_27641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27670 v h) (hints_cons _ _ _ (der_27641 v h) (by intro d hd; cases hd)))
def cl_33082 : CNF.NClause := [(34,false),(65,true),(87,false),(75,false),(85,true),(80,false)]
theorem der_33082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33082 :=
  CNF.rup_sound cl_33082 [cl_27671,cl_27667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27671 v h) (hints_cons _ _ _ (der_27667 v h) (by intro d hd; cases hd)))
def cl_33083 : CNF.NClause := [(34,false),(87,false),(65,true),(3,false),(80,false),(70,false)]
theorem der_33083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33083 :=
  CNF.rup_sound cl_33083 [cl_27674,cl_27644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27674 v h) (hints_cons _ _ _ (der_27644 v h) (by intro d hd; cases hd)))
def cl_33084 : CNF.NClause := [(34,false),(70,false),(65,true),(75,true),(87,false),(80,false)]
theorem der_33084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33084 :=
  CNF.rup_sound cl_33084 [cl_27675,cl_33083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27675 v h) (hints_cons _ _ _ (der_33083 v h) (by intro d hd; cases hd)))
def cl_33085 : CNF.NClause := [(34,false),(75,true),(87,false),(70,true),(80,false),(65,false)]
theorem der_33085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33085 :=
  CNF.rup_sound cl_33085 [cl_27677,cl_27647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27677 v h) (hints_cons _ _ _ (der_27647 v h) (by intro d hd; cases hd)))
def cl_33086 : CNF.NClause := [(34,false),(65,true),(3,false),(87,false),(85,true),(80,false)]
theorem der_33086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33086 :=
  CNF.rup_sound cl_33086 [cl_27678,cl_33083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27678 v h) (hints_cons _ _ _ (der_33083 v h) (by intro d hd; cases hd)))
def cl_33087 : CNF.NClause := [(34,false),(65,true),(70,true),(87,false),(85,true),(80,false)]
theorem der_33087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33087 :=
  CNF.rup_sound cl_33087 [cl_27679,cl_33082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27679 v h) (hints_cons _ _ _ (der_33082 v h) (by intro d hd; cases hd)))
def cl_33088 : CNF.NClause := [(34,false),(65,true),(3,false),(87,false),(75,false),(70,false)]
theorem der_33088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33088 :=
  CNF.rup_sound cl_33088 [cl_27682,cl_33083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27682 v h) (hints_cons _ _ _ (der_33083 v h) (by intro d hd; cases hd)))
def cl_33089 : CNF.NClause := [(34,false),(75,false),(80,true),(65,true),(87,false),(70,false)]
theorem der_33089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33089 :=
  CNF.rup_sound cl_33089 [cl_27683,cl_33088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27683 v h) (hints_cons _ _ _ (der_33088 v h) (by intro d hd; cases hd)))
def cl_33090 : CNF.NClause := [(34,false),(65,false),(80,true),(3,false),(87,false),(75,false)]
theorem der_33090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33090 :=
  CNF.rup_sound cl_33090 [cl_27684,cl_27680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27684 v h) (hints_cons _ _ _ (der_27680 v h) (by intro d hd; cases hd)))
def cl_33091 : CNF.NClause := [(34,false),(65,false),(80,true),(87,false),(75,false),(70,true)]
theorem der_33091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33091 :=
  CNF.rup_sound cl_33091 [cl_27685,cl_33071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27685 v h) (hints_cons _ _ _ (der_33071 v h) (by intro d hd; cases hd)))
def cl_33092 : CNF.NClause := [(34,false),(80,true),(70,true),(3,false),(87,false),(75,false)]
theorem der_33092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33092 :=
  CNF.rup_sound cl_33092 [cl_27686,cl_33090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27686 v h) (hints_cons _ _ _ (der_33090 v h) (by intro d hd; cases hd)))
def cl_33093 : CNF.NClause := [(34,false),(80,true),(3,true),(65,true),(87,false),(75,false)]
theorem der_33093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33093 :=
  CNF.rup_sound cl_33093 [cl_27687,cl_33089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27687 v h) (hints_cons _ _ _ (der_33089 v h) (by intro d hd; cases hd)))
def cl_33094 : CNF.NClause := [(34,false),(80,true),(3,false),(87,false),(70,false),(65,false)]
theorem der_33094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33094 :=
  CNF.rup_sound cl_33094 [cl_27688,cl_33090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27688 v h) (hints_cons _ _ _ (der_33090 v h) (by intro d hd; cases hd)))
def cl_33095 : CNF.NClause := [(34,false),(80,true),(65,false),(87,false),(70,false),(3,true)]
theorem der_33095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33095 :=
  CNF.rup_sound cl_33095 [cl_27689,cl_33074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27689 v h) (hints_cons _ _ _ (der_33074 v h) (by intro d hd; cases hd)))
def cl_33096 : CNF.NClause := [(34,false),(65,true),(3,false),(75,true),(87,false),(70,false)]
theorem der_33096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33096 :=
  CNF.rup_sound cl_33096 [cl_27690,cl_33083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27690 v h) (hints_cons _ _ _ (der_33083 v h) (by intro d hd; cases hd)))
def cl_33097 : CNF.NClause := [(34,false),(65,true),(75,true),(87,false),(85,true),(70,false)]
theorem der_33097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33097 :=
  CNF.rup_sound cl_33097 [cl_27691,cl_33084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27691 v h) (hints_cons _ _ _ (der_33084 v h) (by intro d hd; cases hd)))
def cl_33098 : CNF.NClause := [(34,false),(70,true),(3,false),(75,true),(87,false),(65,false)]
theorem der_33098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33098 :=
  CNF.rup_sound cl_33098 [cl_27692,cl_27661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27692 v h) (hints_cons _ _ _ (der_27661 v h) (by intro d hd; cases hd)))
def cl_33099 : CNF.NClause := [(34,false),(70,true),(80,true),(75,true),(87,false),(65,false)]
theorem der_33099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33099 :=
  CNF.rup_sound cl_33099 [cl_27693,cl_33077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27693 v h) (hints_cons _ _ _ (der_33077 v h) (by intro d hd; cases hd)))
def cl_33100 : CNF.NClause := [(34,false),(80,true),(70,true),(3,false),(75,true),(87,false)]
theorem der_33100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33100 :=
  CNF.rup_sound cl_33100 [cl_27694,cl_33098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27694 v h) (hints_cons _ _ _ (der_33098 v h) (by intro d hd; cases hd)))
def cl_33101 : CNF.NClause := [(34,false),(65,true),(70,true),(75,true),(87,false),(85,true)]
theorem der_33101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33101 :=
  CNF.rup_sound cl_33101 [cl_27695,cl_33087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27695 v h) (hints_cons _ _ _ (der_33087 v h) (by intro d hd; cases hd)))
def cl_33102 : CNF.NClause := [(34,false),(75,false),(65,true),(85,false),(80,false),(70,false)]
theorem der_33102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33102 :=
  CNF.rup_sound cl_33102 [cl_27698,cl_27697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27698 v h) (hints_cons _ _ _ (der_27697 v h) (by intro d hd; cases hd)))
def cl_33103 : CNF.NClause := [(34,false),(85,false),(70,true),(75,false),(80,false),(65,false)]
theorem der_33103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33103 :=
  CNF.rup_sound cl_33103 [cl_27700,cl_27699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27700 v h) (hints_cons _ _ _ (der_27699 v h) (by intro d hd; cases hd)))
def cl_33104 : CNF.NClause := [(34,false),(85,false),(70,true),(3,true),(75,false),(80,false)]
theorem der_33104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33104 :=
  CNF.rup_sound cl_33104 [cl_27702,cl_33103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27702 v h) (hints_cons _ _ _ (der_33103 v h) (by intro d hd; cases hd)))
def cl_33105 : CNF.NClause := [(34,false),(65,true),(3,true),(85,false),(80,false),(70,false)]
theorem der_33105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33105 :=
  CNF.rup_sound cl_33105 [cl_27706,cl_33102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27706 v h) (hints_cons _ _ _ (der_33102 v h) (by intro d hd; cases hd)))
def cl_33106 : CNF.NClause := [(34,false),(85,false),(3,false),(70,true),(80,false),(65,false)]
theorem der_33106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33106 :=
  CNF.rup_sound cl_33106 [cl_27707,cl_27699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27707 v h) (hints_cons _ _ _ (der_27699 v h) (by intro d hd; cases hd)))
def cl_33107 : CNF.NClause := [(34,false),(80,false),(85,false),(70,true),(65,false),(87,true)]
theorem der_33107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33107 :=
  CNF.rup_sound cl_33107 [cl_27708,cl_33103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27708 v h) (hints_cons _ _ _ (der_33103 v h) (by intro d hd; cases hd)))
def cl_33108 : CNF.NClause := [(34,false),(70,true),(3,false),(75,true),(85,false),(80,false)]
theorem der_33108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33108 :=
  CNF.rup_sound cl_33108 [cl_27709,cl_33106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27709 v h) (hints_cons _ _ _ (der_33106 v h) (by intro d hd; cases hd)))
def cl_33109 : CNF.NClause := [(34,false),(75,true),(65,true),(70,true),(85,false),(80,false)]
theorem der_33109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33109 :=
  CNF.rup_sound cl_33109 [cl_27710,cl_33069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27710 v h) (hints_cons _ _ _ (der_33069 v h) (by intro d hd; cases hd)))
def cl_33110 : CNF.NClause := [(34,false),(80,true),(85,false),(75,false),(70,false),(65,false)]
theorem der_33110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33110 :=
  CNF.rup_sound cl_33110 [cl_27712,cl_33070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27712 v h) (hints_cons _ _ _ (der_33070 v h) (by intro d hd; cases hd)))
def cl_33111 : CNF.NClause := [(34,false),(65,true),(3,false),(85,false),(75,false),(70,false)]
theorem der_33111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33111 :=
  CNF.rup_sound cl_33111 [cl_27713,cl_27697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27713 v h) (hints_cons _ _ _ (der_27697 v h) (by intro d hd; cases hd)))
def cl_33112 : CNF.NClause := [(34,false),(85,false),(80,true),(3,true),(75,false),(70,false)]
theorem der_33112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33112 :=
  CNF.rup_sound cl_33112 [cl_27714,cl_33110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27714 v h) (hints_cons _ _ _ (der_33110 v h) (by intro d hd; cases hd)))
def cl_33113 : CNF.NClause := [(34,false),(70,true),(3,false),(85,false),(75,false),(65,false)]
theorem der_33113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33113 :=
  CNF.rup_sound cl_33113 [cl_27715,cl_33106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27715 v h) (hints_cons _ _ _ (der_33106 v h) (by intro d hd; cases hd)))
def cl_33114 : CNF.NClause := [(34,false),(70,true),(87,true),(85,false),(75,false),(65,false)]
theorem der_33114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33114 :=
  CNF.rup_sound cl_33114 [cl_27716,cl_33113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27716 v h) (hints_cons _ _ _ (der_33113 v h) (by intro d hd; cases hd)))
def cl_33116 : CNF.NClause := [(34,false),(65,true),(80,true),(70,true),(85,false),(75,false)]
theorem der_33116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33116 :=
  CNF.rup_sound cl_33116 [cl_27718,cl_33073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27718 v h) (hints_cons _ _ _ (der_33073 v h) (by intro d hd; cases hd)))
def cl_33117 : CNF.NClause := [(34,false),(80,true),(65,false),(85,false),(70,false),(3,true)]
theorem der_33117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33117 :=
  CNF.rup_sound cl_33117 [cl_27720,cl_33110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27720 v h) (hints_cons _ _ _ (der_33110 v h) (by intro d hd; cases hd)))
def cl_33119 : CNF.NClause := [(34,false),(85,false),(3,false),(75,true),(70,true),(65,false)]
theorem der_33119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33119 :=
  CNF.rup_sound cl_33119 [cl_27723,cl_33098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27723 v h) (hints_cons _ _ _ (der_33098 v h) (by intro d hd; cases hd)))
def cl_33120 : CNF.NClause := [(34,false),(85,false),(80,true),(75,true),(3,true),(65,false)]
theorem der_33120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33120 :=
  CNF.rup_sound cl_33120 [cl_27724,cl_33077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27724 v h) (hints_cons _ _ _ (der_33077 v h) (by intro d hd; cases hd)))
def cl_33121 : CNF.NClause := [(34,false),(80,true),(70,true),(65,true),(3,false),(85,false)]
theorem der_33121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33121 :=
  CNF.rup_sound cl_33121 [cl_27725,cl_33116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27725 v h) (hints_cons _ _ _ (der_33116 v h) (by intro d hd; cases hd)))
def cl_33122 : CNF.NClause := [(34,false),(80,true),(70,true),(3,true),(65,true),(85,false)]
theorem der_33122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33122 :=
  CNF.rup_sound cl_33122 [cl_27726,cl_33116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27726 v h) (hints_cons _ _ _ (der_33116 v h) (by intro d hd; cases hd)))
def cl_33123 : CNF.NClause := [(34,false),(75,false),(65,false),(85,true),(80,false),(70,false)]
theorem der_33123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33123 :=
  CNF.rup_sound cl_33123 [cl_27728,cl_27727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27728 v h) (hints_cons _ _ _ (der_27727 v h) (by intro d hd; cases hd)))
def cl_33124 : CNF.NClause := [(34,false),(75,false),(65,true),(3,false),(80,false),(70,false)]
theorem der_33124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33124 :=
  CNF.rup_sound cl_33124 [cl_27729,cl_33102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27729 v h) (hints_cons _ _ _ (der_33102 v h) (by intro d hd; cases hd)))
def cl_33125 : CNF.NClause := [(34,false),(75,false),(70,true),(3,false),(80,false),(65,false)]
theorem der_33125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33125 :=
  CNF.rup_sound cl_33125 [cl_27731,cl_33106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27731 v h) (hints_cons _ _ _ (der_33106 v h) (by intro d hd; cases hd)))
def cl_33126 : CNF.NClause := [(34,false),(65,false),(70,true),(75,false),(80,false),(3,true)]
theorem der_33126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33126 :=
  CNF.rup_sound cl_33126 [cl_27732,cl_33103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27732 v h) (hints_cons _ _ _ (der_33103 v h) (by intro d hd; cases hd)))
def cl_33127 : CNF.NClause := [(34,false),(70,true),(3,false),(75,false),(85,true),(80,false)]
theorem der_33127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33127 :=
  CNF.rup_sound cl_33127 [cl_27733,cl_33125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27733 v h) (hints_cons _ _ _ (der_33125 v h) (by intro d hd; cases hd)))
def cl_33128 : CNF.NClause := [(34,false),(75,false),(65,true),(70,true),(85,true),(80,false)]
theorem der_33128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33128 :=
  CNF.rup_sound cl_33128 [cl_27734,cl_33082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27734 v h) (hints_cons _ _ _ (der_33082 v h) (by intro d hd; cases hd)))
def cl_33129 : CNF.NClause := [(34,false),(65,false),(85,true),(80,false),(70,false),(3,true)]
theorem der_33129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33129 :=
  CNF.rup_sound cl_33129 [cl_27736,cl_33123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27736 v h) (hints_cons _ _ _ (der_33123 v h) (by intro d hd; cases hd)))
def cl_33130 : CNF.NClause := [(34,false),(85,true),(65,true),(3,false),(80,false),(70,false)]
theorem der_33130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33130 :=
  CNF.rup_sound cl_33130 [cl_27737,cl_33086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27737 v h) (hints_cons _ _ _ (der_33086 v h) (by intro d hd; cases hd)))
def cl_33131 : CNF.NClause := [(34,false),(87,true),(85,true),(80,false),(70,false),(3,true)]
theorem der_33131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33131 :=
  CNF.rup_sound cl_33131 [cl_27738,cl_27730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27738 v h) (hints_cons _ _ _ (der_27730 v h) (by intro d hd; cases hd)))
def cl_33132 : CNF.NClause := [(34,false),(3,false),(75,true),(70,true),(80,false),(65,false)]
theorem der_33132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33132 :=
  CNF.rup_sound cl_33132 [cl_27739,cl_33106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27739 v h) (hints_cons _ _ _ (der_33106 v h) (by intro d hd; cases hd)))
def cl_33133 : CNF.NClause := [(34,false),(65,true),(70,true),(3,false),(85,true),(80,false)]
theorem der_33133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33133 :=
  CNF.rup_sound cl_33133 [cl_27741,cl_33086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27741 v h) (hints_cons _ _ _ (der_33086 v h) (by intro d hd; cases hd)))
def cl_33134 : CNF.NClause := [(34,false),(75,true),(70,true),(65,true),(3,true),(80,false)]
theorem der_33134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33134 :=
  CNF.rup_sound cl_33134 [cl_27742,cl_33109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27742 v h) (hints_cons _ _ _ (der_33109 v h) (by intro d hd; cases hd)))
def cl_33135 : CNF.NClause := [(34,false),(80,true),(3,false),(75,false),(70,false),(65,false)]
theorem der_33135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33135 :=
  CNF.rup_sound cl_33135 [cl_27743,cl_33090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27743 v h) (hints_cons _ _ _ (der_33090 v h) (by intro d hd; cases hd)))
def cl_33136 : CNF.NClause := [(34,false),(80,true),(65,false),(75,false),(70,false),(3,true)]
theorem der_33136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33136 :=
  CNF.rup_sound cl_33136 [cl_27744,cl_33110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27744 v h) (hints_cons _ _ _ (der_33110 v h) (by intro d hd; cases hd)))
def cl_33137 : CNF.NClause := [(34,false),(65,true),(3,false),(75,false),(85,true),(70,false)]
theorem der_33137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33137 :=
  CNF.rup_sound cl_33137 [cl_27745,cl_33130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27745 v h) (hints_cons _ _ _ (der_33130 v h) (by intro d hd; cases hd)))
def cl_33138 : CNF.NClause := [(34,false),(70,false),(80,true),(75,false),(85,true),(3,true)]
theorem der_33138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33138 :=
  CNF.rup_sound cl_33138 [cl_27746,cl_33136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27746 v h) (hints_cons _ _ _ (der_33136 v h) (by intro d hd; cases hd)))
def cl_33139 : CNF.NClause := [(34,false),(65,false),(80,true),(3,false),(75,false),(70,true)]
theorem der_33139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33139 :=
  CNF.rup_sound cl_33139 [cl_27747,cl_33113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27747 v h) (hints_cons _ _ _ (der_33113 v h) (by intro d hd; cases hd)))
def cl_33140 : CNF.NClause := [(34,false),(80,true),(70,true),(65,true),(3,false),(75,false)]
theorem der_33140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33140 :=
  CNF.rup_sound cl_33140 [cl_27749,cl_33092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27749 v h) (hints_cons _ _ _ (der_33092 v h) (by intro d hd; cases hd)))
def cl_33141 : CNF.NClause := [(34,false),(80,true),(70,true),(3,true),(65,true),(75,false)]
theorem der_33141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33141 :=
  CNF.rup_sound cl_33141 [cl_27750,cl_33116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27750 v h) (hints_cons _ _ _ (der_33116 v h) (by intro d hd; cases hd)))
def cl_33142 : CNF.NClause := [(34,false),(80,true),(3,false),(85,true),(70,false),(65,false)]
theorem der_33142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33142 :=
  CNF.rup_sound cl_33142 [cl_27751,cl_33135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27751 v h) (hints_cons _ _ _ (der_33135 v h) (by intro d hd; cases hd)))
def cl_33143 : CNF.NClause := [(34,false),(65,true),(3,false),(75,true),(85,true),(70,false)]
theorem der_33143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33143 :=
  CNF.rup_sound cl_33143 [cl_27753,cl_33130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27753 v h) (hints_cons _ _ _ (der_33130 v h) (by intro d hd; cases hd)))
def cl_33144 : CNF.NClause := [(34,false),(80,true),(65,true),(75,true),(85,true),(70,false)]
theorem der_33144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33144 :=
  CNF.rup_sound cl_33144 [cl_27754,cl_33097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27754 v h) (hints_cons _ _ _ (der_33097 v h) (by intro d hd; cases hd)))
def cl_33146 : CNF.NClause := [(34,false),(80,true),(70,true),(3,false),(75,true),(85,true)]
theorem der_33146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33146 :=
  CNF.rup_sound cl_33146 [cl_27757,cl_33100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27757 v h) (hints_cons _ _ _ (der_33100 v h) (by intro d hd; cases hd)))
def cl_33147 : CNF.NClause := [(34,false),(80,true),(70,true),(75,true),(85,true),(87,true)]
theorem der_33147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33147 :=
  CNF.rup_sound cl_33147 [cl_27758,cl_33146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27758 v h) (hints_cons _ _ _ (der_33146 v h) (by intro d hd; cases hd)))
def cl_33148 : CNF.NClause := [(31,true),(39,true),(42,true),(53,true),(59,true),(121,false)]
theorem der_33148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33148 :=
  CNF.rup_sound cl_33148 [cl_3832,cl_23949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3832 v h) (hints_cons _ _ _ (der_23949 v h) (by intro d hd; cases hd)))
def cl_33149 : CNF.NClause := [(31,true),(39,true),(53,true),(50,true),(59,true),(121,false)]
theorem der_33149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33149 :=
  CNF.rup_sound cl_33149 [cl_3836,cl_23949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3836 v h) (hints_cons _ _ _ (der_23949 v h) (by intro d hd; cases hd)))
def cl_33150 : CNF.NClause := [(80,false),(29,true),(15,true),(11,true),(3,true),(7,true)]
theorem der_33150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33150 :=
  CNF.rup_sound cl_33150 [cl_1200,cl_23771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1200 v h) (hints_cons _ _ _ (der_23771 v h) (by intro d hd; cases hd)))
def cl_33151 : CNF.NClause := [(80,false),(24,true),(11,true),(3,true),(29,true),(7,true)]
theorem der_33151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33151 :=
  CNF.rup_sound cl_33151 [cl_1208,cl_23771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1208 v h) (hints_cons _ _ _ (der_23771 v h) (by intro d hd; cases hd)))
def cl_33152 : CNF.NClause := [(80,false),(15,true),(24,true),(3,true),(29,true),(7,true)]
theorem der_33152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33152 :=
  CNF.rup_sound cl_33152 [cl_1212,cl_23771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1212 v h) (hints_cons _ _ _ (der_23771 v h) (by intro d hd; cases hd)))
def cl_33153 : CNF.NClause := [(80,false),(15,true),(11,true),(24,true),(3,true),(29,true)]
theorem der_33153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33153 :=
  CNF.rup_sound cl_33153 [cl_1214,cl_23771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1214 v h) (hints_cons _ _ _ (der_23771 v h) (by intro d hd; cases hd)))
def cl_33154 : CNF.NClause := [(80,false),(29,true),(11,true),(7,true),(15,true),(24,true)]
theorem der_33154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33154 :=
  CNF.rup_sound cl_33154 [cl_1215,cl_23771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1215 v h) (hints_cons _ _ _ (der_23771 v h) (by intro d hd; cases hd)))
def cl_33156 : CNF.NClause := [(48,false),(88,false),(77,false),(70,true),(76,false),(83,false)]
theorem der_33156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33156 :=
  CNF.rup_sound cl_33156 [cl_27762,cl_27760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27762 v h) (hints_cons _ _ _ (der_27760 v h) (by intro d hd; cases hd)))
def cl_33157 : CNF.NClause := [(48,false),(76,true),(77,false),(88,false),(83,false),(70,false)]
theorem der_33157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33157 :=
  CNF.rup_sound cl_33157 [cl_27765,cl_27763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27765 v h) (hints_cons _ _ _ (der_27763 v h) (by intro d hd; cases hd)))
def cl_33158 : CNF.NClause := [(48,false),(77,false),(70,true),(88,false),(64,false),(83,false)]
theorem der_33158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33158 :=
  CNF.rup_sound cl_33158 [cl_27767,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27767 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33159 : CNF.NClause := [(48,false),(70,true),(17,false),(77,false),(88,false),(83,false)]
theorem der_33159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33159 :=
  CNF.rup_sound cl_33159 [cl_27768,cl_33158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27768 v h) (hints_cons _ _ _ (der_33158 v h) (by intro d hd; cases hd)))
def cl_33160 : CNF.NClause := [(48,false),(83,false),(70,true),(77,false),(88,false),(17,true)]
theorem der_33160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33160 :=
  CNF.rup_sound cl_33160 [cl_27769,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27769 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33161 : CNF.NClause := [(48,false),(83,false),(77,true),(88,false),(76,false),(70,false)]
theorem der_33161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33161 :=
  CNF.rup_sound cl_33161 [cl_27771,cl_27770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27771 v h) (hints_cons _ _ _ (der_27770 v h) (by intro d hd; cases hd)))
def cl_33162 : CNF.NClause := [(48,false),(76,false),(88,false),(64,false),(70,true),(83,false)]
theorem der_33162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33162 :=
  CNF.rup_sound cl_33162 [cl_27773,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27773 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33163 : CNF.NClause := [(48,false),(76,false),(17,false),(88,false),(70,true),(83,false)]
theorem der_33163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33163 :=
  CNF.rup_sound cl_33163 [cl_27774,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27774 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33164 : CNF.NClause := [(48,false),(76,false),(70,true),(88,false),(17,true),(83,false)]
theorem der_33164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33164 :=
  CNF.rup_sound cl_33164 [cl_27775,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27775 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33165 : CNF.NClause := [(48,false),(76,true),(88,false),(64,false),(83,false),(70,false)]
theorem der_33165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33165 :=
  CNF.rup_sound cl_33165 [cl_27776,cl_26339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27776 v h) (hints_cons _ _ _ (der_26339 v h) (by intro d hd; cases hd)))
def cl_33166 : CNF.NClause := [(48,false),(76,true),(17,false),(88,false),(83,false),(70,false)]
theorem der_33166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33166 :=
  CNF.rup_sound cl_33166 [cl_27777,cl_33165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27777 v h) (hints_cons _ _ _ (der_33165 v h) (by intro d hd; cases hd)))
def cl_33167 : CNF.NClause := [(48,false),(70,false),(77,true),(88,false),(83,false),(17,true)]
theorem der_33167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33167 :=
  CNF.rup_sound cl_33167 [cl_27778,cl_32389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27778 v h) (hints_cons _ _ _ (der_32389 v h) (by intro d hd; cases hd)))
def cl_33169 : CNF.NClause := [(48,false),(83,false),(77,true),(88,false),(17,true),(64,false)]
theorem der_33169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33169 :=
  CNF.rup_sound cl_33169 [cl_27780,cl_32389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27780 v h) (hints_cons _ _ _ (der_32389 v h) (by intro d hd; cases hd)))
def cl_33170 : CNF.NClause := [(48,false),(88,false),(76,true),(17,false),(70,true),(83,false)]
theorem der_33170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33170 :=
  CNF.rup_sound cl_33170 [cl_27781,cl_33159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27781 v h) (hints_cons _ _ _ (der_33159 v h) (by intro d hd; cases hd)))
def cl_33171 : CNF.NClause := [(48,false),(83,true),(77,false),(88,false),(76,false),(70,false)]
theorem der_33171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33171 :=
  CNF.rup_sound cl_33171 [cl_27785,cl_27783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27785 v h) (hints_cons _ _ _ (der_27783 v h) (by intro d hd; cases hd)))
def cl_33172 : CNF.NClause := [(48,false),(77,false),(88,false),(64,false),(76,false),(70,true)]
theorem der_33172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33172 :=
  CNF.rup_sound cl_33172 [cl_27787,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27787 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33173 : CNF.NClause := [(48,false),(83,true),(17,false),(77,false),(88,false),(76,false)]
theorem der_33173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33173 :=
  CNF.rup_sound cl_33173 [cl_27788,cl_27786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27788 v h) (hints_cons _ _ _ (der_27786 v h) (by intro d hd; cases hd)))
def cl_33174 : CNF.NClause := [(48,false),(70,true),(77,false),(88,false),(76,false),(17,true)]
theorem der_33174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33174 :=
  CNF.rup_sound cl_33174 [cl_27789,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27789 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_33175 : CNF.NClause := [(48,false),(83,true),(77,false),(88,false),(64,false),(70,false)]
theorem der_33175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33175 :=
  CNF.rup_sound cl_33175 [cl_27790,cl_26340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27790 v h) (hints_cons _ _ _ (der_26340 v h) (by intro d hd; cases hd)))
def cl_33176 : CNF.NClause := [(48,false),(83,true),(17,false),(77,false),(88,false),(70,false)]
theorem der_33176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33176 :=
  CNF.rup_sound cl_33176 [cl_27791,cl_33175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27791 v h) (hints_cons _ _ _ (der_33175 v h) (by intro d hd; cases hd)))
def cl_33179 : CNF.NClause := [(48,false),(83,true),(77,false),(88,false),(64,false),(70,true)]
theorem der_33179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33179 :=
  CNF.rup_sound cl_33179 [cl_27794,cl_33172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27794 v h) (hints_cons _ _ _ (der_33172 v h) (by intro d hd; cases hd)))
def cl_33180 : CNF.NClause := [(48,false),(83,true),(76,true),(17,false),(77,false),(88,false)]
theorem der_33180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33180 :=
  CNF.rup_sound cl_33180 [cl_27795,cl_33176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27795 v h) (hints_cons _ _ _ (der_33176 v h) (by intro d hd; cases hd)))
def cl_33181 : CNF.NClause := [(48,false),(83,true),(76,true),(77,false),(88,false),(70,true)]
theorem der_33181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33181 :=
  CNF.rup_sound cl_33181 [cl_27796,cl_33179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27796 v h) (hints_cons _ _ _ (der_33179 v h) (by intro d hd; cases hd)))
def cl_33182 : CNF.NClause := [(48,false),(83,true),(88,false),(64,false),(76,false),(70,false)]
theorem der_33182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33182 :=
  CNF.rup_sound cl_33182 [cl_27797,cl_32086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27797 v h) (hints_cons _ _ _ (der_32086 v h) (by intro d hd; cases hd)))
def cl_33183 : CNF.NClause := [(48,false),(83,true),(17,false),(88,false),(76,false),(70,false)]
theorem der_33183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33183 :=
  CNF.rup_sound cl_33183 [cl_27798,cl_33182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27798 v h) (hints_cons _ _ _ (der_33182 v h) (by intro d hd; cases hd)))
def cl_33184 : CNF.NClause := [(48,false),(70,false),(77,true),(88,false),(76,false),(17,true)]
theorem der_33184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33184 :=
  CNF.rup_sound cl_33184 [cl_27799,cl_32389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27799 v h) (hints_cons _ _ _ (der_32389 v h) (by intro d hd; cases hd)))
def cl_33185 : CNF.NClause := [(48,false),(70,true),(17,false),(88,false),(64,false),(76,false)]
theorem der_33185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33185 :=
  CNF.rup_sound cl_33185 [cl_27800,cl_33172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27800 v h) (hints_cons _ _ _ (der_33172 v h) (by intro d hd; cases hd)))
def cl_33186 : CNF.NClause := [(48,false),(76,false),(77,true),(88,false),(17,true),(64,false)]
theorem der_33186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33186 :=
  CNF.rup_sound cl_33186 [cl_27801,cl_32389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27801 v h) (hints_cons _ _ _ (der_32389 v h) (by intro d hd; cases hd)))
def cl_33187 : CNF.NClause := [(48,false),(88,false),(17,false),(77,true),(70,true),(76,false)]
theorem der_33187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33187 :=
  CNF.rup_sound cl_33187 [cl_27802,cl_33185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27802 v h) (hints_cons _ _ _ (der_33185 v h) (by intro d hd; cases hd)))
def cl_33188 : CNF.NClause := [(48,false),(76,false),(70,true),(64,true),(77,true),(88,false)]
theorem der_33188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33188 :=
  CNF.rup_sound cl_33188 [cl_27803,cl_33187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27803 v h) (hints_cons _ _ _ (der_33187 v h) (by intro d hd; cases hd)))
def cl_33189 : CNF.NClause := [(48,false),(76,true),(17,false),(88,false),(64,false),(70,false)]
theorem der_33189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33189 :=
  CNF.rup_sound cl_33189 [cl_27804,cl_33166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27804 v h) (hints_cons _ _ _ (der_33166 v h) (by intro d hd; cases hd)))
def cl_33190 : CNF.NClause := [(48,false),(76,true),(17,false),(77,true),(88,false),(70,false)]
theorem der_33190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33190 :=
  CNF.rup_sound cl_33190 [cl_27805,cl_33189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27805 v h) (hints_cons _ _ _ (der_33189 v h) (by intro d hd; cases hd)))
def cl_33191 : CNF.NClause := [(48,false),(83,true),(76,true),(88,false),(70,false),(17,true)]
theorem der_33191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33191 :=
  CNF.rup_sound cl_33191 [cl_27806,cl_32086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27806 v h) (hints_cons _ _ _ (der_32086 v h) (by intro d hd; cases hd)))
def cl_33193 : CNF.NClause := [(48,false),(70,true),(76,true),(88,false),(64,false),(83,true)]
theorem der_33193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33193 :=
  CNF.rup_sound cl_33193 [cl_27808,cl_33179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27808 v h) (hints_cons _ _ _ (der_33179 v h) (by intro d hd; cases hd)))
def cl_33194 : CNF.NClause := [(48,false),(88,false),(76,true),(17,false),(70,true),(83,true)]
theorem der_33194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33194 :=
  CNF.rup_sound cl_33194 [cl_27809,cl_33193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27809 v h) (hints_cons _ _ _ (der_33193 v h) (by intro d hd; cases hd)))
def cl_33195 : CNF.NClause := [(48,false),(70,false),(77,false),(64,false),(76,false),(17,true)]
theorem der_33195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33195 :=
  CNF.rup_sound cl_33195 [cl_27811,cl_32088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27811 v h) (hints_cons _ _ _ (der_32088 v h) (by intro d hd; cases hd)))
def cl_33196 : CNF.NClause := [(48,false),(64,true),(17,false),(77,false),(76,false),(83,false)]
theorem der_33196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33196 :=
  CNF.rup_sound cl_33196 [cl_27816,cl_27812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27816 v h) (hints_cons _ _ _ (der_27812 v h) (by intro d hd; cases hd)))
def cl_33197 : CNF.NClause := [(48,false),(76,false),(64,true),(77,false),(83,false),(88,true)]
theorem der_33197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33197 :=
  CNF.rup_sound cl_33197 [cl_27817,cl_33196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27817 v h) (hints_cons _ _ _ (der_33196 v h) (by intro d hd; cases hd)))
def cl_33198 : CNF.NClause := [(48,false),(76,true),(77,false),(64,false),(83,false),(70,false)]
theorem der_33198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33198 :=
  CNF.rup_sound cl_33198 [cl_27818,cl_33157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27818 v h) (hints_cons _ _ _ (der_33157 v h) (by intro d hd; cases hd)))
def cl_33199 : CNF.NClause := [(48,false),(76,true),(17,false),(77,false),(83,false),(70,false)]
theorem der_33199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33199 :=
  CNF.rup_sound cl_33199 [cl_27819,cl_33198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27819 v h) (hints_cons _ _ _ (der_33198 v h) (by intro d hd; cases hd)))
def cl_33200 : CNF.NClause := [(48,false),(76,true),(17,false),(77,false),(64,false),(83,false)]
theorem der_33200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33200 :=
  CNF.rup_sound cl_33200 [cl_27821,cl_33199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27821 v h) (hints_cons _ _ _ (der_33199 v h) (by intro d hd; cases hd)))
def cl_33201 : CNF.NClause := [(48,false),(17,true),(77,false),(64,false),(83,false),(88,true)]
theorem der_33201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33201 :=
  CNF.rup_sound cl_33201 [cl_27822,cl_27815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27822 v h) (hints_cons _ _ _ (der_27815 v h) (by intro d hd; cases hd)))
def cl_33203 : CNF.NClause := [(48,false),(64,true),(17,true),(77,false),(83,false),(88,true)]
theorem der_33203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33203 :=
  CNF.rup_sound cl_33203 [cl_27824,cl_27820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27824 v h) (hints_cons _ _ _ (der_27820 v h) (by intro d hd; cases hd)))
def cl_33204 : CNF.NClause := [(48,false),(70,false),(64,false),(76,false),(17,true),(88,true)]
theorem der_33204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33204 :=
  CNF.rup_sound cl_33204 [cl_27826,cl_32088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27826 v h) (hints_cons _ _ _ (der_32088 v h) (by intro d hd; cases hd)))
def cl_33205 : CNF.NClause := [(48,false),(77,true),(17,false),(76,false),(83,false),(70,false)]
theorem der_33205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33205 :=
  CNF.rup_sound cl_33205 [cl_27827,cl_27825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27827 v h) (hints_cons _ _ _ (der_27825 v h) (by intro d hd; cases hd)))
def cl_33206 : CNF.NClause := [(48,false),(83,false),(76,false),(17,true),(70,false),(88,true)]
theorem der_33206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33206 :=
  CNF.rup_sound cl_33206 [cl_27828,cl_33204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27828 v h) (hints_cons _ _ _ (der_33204 v h) (by intro d hd; cases hd)))
def cl_33207 : CNF.NClause := [(48,false),(76,false),(17,false),(77,true),(64,false),(83,false)]
theorem der_33207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33207 :=
  CNF.rup_sound cl_33207 [cl_27829,cl_27825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27829 v h) (hints_cons _ _ _ (der_27825 v h) (by intro d hd; cases hd)))
def cl_33208 : CNF.NClause := [(48,false),(76,false),(70,true),(77,true),(64,false),(83,false)]
theorem der_33208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33208 :=
  CNF.rup_sound cl_33208 [cl_27830,cl_33207] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27830 v h) (hints_cons _ _ _ (der_33207 v h) (by intro d hd; cases hd)))
def cl_33209 : CNF.NClause := [(48,false),(83,false),(17,false),(77,true),(76,false),(70,true)]
theorem der_33209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33209 :=
  CNF.rup_sound cl_33209 [cl_27831,cl_33187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27831 v h) (hints_cons _ _ _ (der_33187 v h) (by intro d hd; cases hd)))
def cl_33210 : CNF.NClause := [(48,false),(83,false),(70,true),(64,true),(76,false),(17,true)]
theorem der_33210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33210 :=
  CNF.rup_sound cl_33210 [cl_27832,cl_33164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27832 v h) (hints_cons _ _ _ (der_33164 v h) (by intro d hd; cases hd)))
def cl_33211 : CNF.NClause := [(48,false),(76,true),(77,true),(64,false),(83,false),(70,false)]
theorem der_33211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33211 :=
  CNF.rup_sound cl_33211 [cl_27833,cl_33165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27833 v h) (hints_cons _ _ _ (der_33165 v h) (by intro d hd; cases hd)))
def cl_33212 : CNF.NClause := [(48,false),(76,true),(64,true),(17,false),(83,false),(70,false)]
theorem der_33212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33212 :=
  CNF.rup_sound cl_33212 [cl_27834,cl_33166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27834 v h) (hints_cons _ _ _ (der_33166 v h) (by intro d hd; cases hd)))
def cl_33213 : CNF.NClause := [(48,false),(76,true),(17,true),(77,true),(83,false),(70,false)]
theorem der_33213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33213 :=
  CNF.rup_sound cl_33213 [cl_27835,cl_33167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27835 v h) (hints_cons _ _ _ (der_33167 v h) (by intro d hd; cases hd)))
def cl_33214 : CNF.NClause := [(48,false),(76,true),(17,false),(77,true),(64,false),(83,false)]
theorem der_33214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33214 :=
  CNF.rup_sound cl_33214 [cl_27836,cl_33211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27836 v h) (hints_cons _ _ _ (der_33211 v h) (by intro d hd; cases hd)))
def cl_33215 : CNF.NClause := [(48,false),(83,false),(76,true),(64,false),(17,true),(88,true)]
theorem der_33215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33215 :=
  CNF.rup_sound cl_33215 [cl_27837,cl_32087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27837 v h) (hints_cons _ _ _ (der_32087 v h) (by intro d hd; cases hd)))
def cl_33216 : CNF.NClause := [(48,false),(83,false),(17,false),(77,true),(70,true),(88,true)]
theorem der_33216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33216 :=
  CNF.rup_sound cl_33216 [cl_27838,cl_33209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27838 v h) (hints_cons _ _ _ (der_33209 v h) (by intro d hd; cases hd)))
def cl_33217 : CNF.NClause := [(48,false),(83,false),(76,true),(64,true),(17,true),(88,true)]
theorem der_33217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33217 :=
  CNF.rup_sound cl_33217 [cl_27839,cl_33203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27839 v h) (hints_cons _ _ _ (der_33203 v h) (by intro d hd; cases hd)))
def cl_33218 : CNF.NClause := [(48,false),(83,true),(77,false),(64,false),(76,false),(70,false)]
theorem der_33218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33218 :=
  CNF.rup_sound cl_33218 [cl_27840,cl_32088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27840 v h) (hints_cons _ _ _ (der_32088 v h) (by intro d hd; cases hd)))
def cl_33219 : CNF.NClause := [(48,false),(83,true),(17,false),(77,false),(76,false),(70,false)]
theorem der_33219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33219 :=
  CNF.rup_sound cl_33219 [cl_27841,cl_33218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27841 v h) (hints_cons _ _ _ (der_33218 v h) (by intro d hd; cases hd)))
def cl_33220 : CNF.NClause := [(48,false),(88,true),(77,false),(76,false),(70,false),(17,true)]
theorem der_33220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33220 :=
  CNF.rup_sound cl_33220 [cl_27842,cl_33195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27842 v h) (hints_cons _ _ _ (der_33195 v h) (by intro d hd; cases hd)))
def cl_33221 : CNF.NClause := [(48,false),(17,false),(77,false),(64,false),(76,false),(70,true)]
theorem der_33221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33221 :=
  CNF.rup_sound cl_33221 [cl_27843,cl_27814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27843 v h) (hints_cons _ _ _ (der_27814 v h) (by intro d hd; cases hd)))
def cl_33223 : CNF.NClause := [(48,false),(83,true),(64,true),(17,false),(77,false),(76,false)]
theorem der_33223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33223 :=
  CNF.rup_sound cl_33223 [cl_27845,cl_33219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27845 v h) (hints_cons _ _ _ (der_33219 v h) (by intro d hd; cases hd)))
def cl_33224 : CNF.NClause := [(48,false),(88,true),(64,true),(77,false),(76,false),(17,true)]
theorem der_33224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33224 :=
  CNF.rup_sound cl_33224 [cl_27846,cl_33220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27846 v h) (hints_cons _ _ _ (der_33220 v h) (by intro d hd; cases hd)))
def cl_33225 : CNF.NClause := [(48,false),(76,true),(17,false),(77,false),(64,false),(70,false)]
theorem der_33225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33225 :=
  CNF.rup_sound cl_33225 [cl_27847,cl_33199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27847 v h) (hints_cons _ _ _ (der_33199 v h) (by intro d hd; cases hd)))
def cl_33227 : CNF.NClause := [(48,false),(76,true),(17,false),(77,false),(64,false),(70,true)]
theorem der_33227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33227 :=
  CNF.rup_sound cl_33227 [cl_27850,cl_33200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27850 v h) (hints_cons _ _ _ (der_33200 v h) (by intro d hd; cases hd)))
def cl_33230 : CNF.NClause := [(48,false),(88,true),(70,true),(64,true),(77,false),(17,true)]
theorem der_33230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33230 :=
  CNF.rup_sound cl_33230 [cl_27853,cl_33224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27853 v h) (hints_cons _ _ _ (der_33224 v h) (by intro d hd; cases hd)))
def cl_33233 : CNF.NClause := [(48,false),(76,false),(17,false),(77,true),(64,false),(70,true)]
theorem der_33233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33233 :=
  CNF.rup_sound cl_33233 [cl_27857,cl_33187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27857 v h) (hints_cons _ _ _ (der_33187 v h) (by intro d hd; cases hd)))
def cl_33234 : CNF.NClause := [(48,false),(83,true),(64,false),(76,false),(17,true),(88,true)]
theorem der_33234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33234 :=
  CNF.rup_sound cl_33234 [cl_27858,cl_32088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27858 v h) (hints_cons _ _ _ (der_32088 v h) (by intro d hd; cases hd)))
def cl_33236 : CNF.NClause := [(48,false),(83,true),(64,true),(77,true),(76,false),(70,true)]
theorem der_33236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33236 :=
  CNF.rup_sound cl_33236 [cl_27860,cl_33188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27860 v h) (hints_cons _ _ _ (der_33188 v h) (by intro d hd; cases hd)))
def cl_33239 : CNF.NClause := [(48,false),(70,true),(17,false),(77,true),(64,false),(83,true)]
theorem der_33239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33239 :=
  CNF.rup_sound cl_33239 [cl_27864,cl_33233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27864 v h) (hints_cons _ _ _ (der_33233 v h) (by intro d hd; cases hd)))
def cl_33240 : CNF.NClause := [(48,false),(83,true),(70,true),(76,true),(64,false),(17,true)]
theorem der_33240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33240 :=
  CNF.rup_sound cl_33240 [cl_27865,cl_33193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27865 v h) (hints_cons _ _ _ (der_33193 v h) (by intro d hd; cases hd)))
def cl_33241 : CNF.NClause := [(48,false),(83,true),(76,true),(64,true),(77,true),(17,true)]
theorem der_33241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33241 :=
  CNF.rup_sound cl_33241 [cl_27867,cl_27810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27867 v h) (hints_cons _ _ _ (der_27810 v h) (by intro d hd; cases hd)))
def cl_33242 : CNF.NClause := [(50,false),(49,false),(47,true),(46,true),(61,true),(108,true)]
theorem der_33242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33242 :=
  CNF.rup_sound cl_33242 [cl_2980,cl_25833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2980 v h) (hints_cons _ _ _ (der_25833 v h) (by intro d hd; cases hd)))
def cl_33243 : CNF.NClause := [(49,true),(47,true),(46,true),(50,true),(61,true),(108,false)]
theorem der_33243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33243 :=
  CNF.rup_sound cl_33243 [cl_3004,cl_23935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3004 v h) (hints_cons _ _ _ (der_23935 v h) (by intro d hd; cases hd)))
def cl_33244 : CNF.NClause := [(48,false),(52,false),(31,true),(40,true),(60,true),(119,true)]
theorem der_33244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33244 :=
  CNF.rup_sound cl_33244 [cl_3684,cl_23890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3684 v h) (hints_cons _ _ _ (der_23890 v h) (by intro d hd; cases hd)))
def cl_33245 : CNF.NClause := [(31,true),(40,true),(44,true),(52,true),(60,true),(119,false)]
theorem der_33245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33245 :=
  CNF.rup_sound cl_33245 [cl_3704,cl_23959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3704 v h) (hints_cons _ _ _ (der_23959 v h) (by intro d hd; cases hd)))
def cl_33246 : CNF.NClause := [(43,false),(91,false),(64,true),(72,false),(85,false),(81,false)]
theorem der_33246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33246 :=
  CNF.rup_sound cl_33246 [cl_27871,cl_27870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27871 v h) (hints_cons _ _ _ (der_27870 v h) (by intro d hd; cases hd)))
def cl_33247 : CNF.NClause := [(85,false),(43,false),(64,true),(91,false),(81,false),(68,false)]
theorem der_33247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33247 :=
  CNF.rup_sound cl_33247 [cl_27874,cl_27873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27874 v h) (hints_cons _ _ _ (der_27873 v h) (by intro d hd; cases hd)))
def cl_33250 : CNF.NClause := [(68,true),(43,false),(64,true),(91,false),(85,false),(81,false)]
theorem der_33250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33250 :=
  CNF.rup_sound cl_33250 [cl_27878,cl_33246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27878 v h) (hints_cons _ _ _ (der_33246 v h) (by intro d hd; cases hd)))
def cl_33251 : CNF.NClause := [(43,false),(64,true),(91,false),(72,false),(85,false),(68,false)]
theorem der_33251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33251 :=
  CNF.rup_sound cl_33251 [cl_27881,cl_27880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27881 v h) (hints_cons _ _ _ (der_27880 v h) (by intro d hd; cases hd)))
def cl_33252 : CNF.NClause := [(68,true),(43,false),(64,false),(91,false),(72,false),(85,false)]
theorem der_33252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33252 :=
  CNF.rup_sound cl_33252 [cl_27883,cl_27882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27883 v h) (hints_cons _ _ _ (der_27882 v h) (by intro d hd; cases hd)))
def cl_33253 : CNF.NClause := [(43,false),(64,true),(91,false),(12,false),(72,false),(85,false)]
theorem der_33253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33253 :=
  CNF.rup_sound cl_33253 [cl_27884,cl_33251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27884 v h) (hints_cons _ _ _ (der_33251 v h) (by intro d hd; cases hd)))
def cl_33254 : CNF.NClause := [(68,true),(85,false),(81,true),(91,false),(72,false),(43,false)]
theorem der_33254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33254 :=
  CNF.rup_sound cl_33254 [cl_27885,cl_33252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27885 v h) (hints_cons _ _ _ (der_33252 v h) (by intro d hd; cases hd)))
def cl_33255 : CNF.NClause := [(43,false),(72,true),(91,false),(85,false),(64,false),(68,false)]
theorem der_33255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33255 :=
  CNF.rup_sound cl_33255 [cl_27887,cl_27886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27887 v h) (hints_cons _ _ _ (der_27886 v h) (by intro d hd; cases hd)))
def cl_33257 : CNF.NClause := [(43,false),(64,true),(72,true),(91,false),(85,false),(68,false)]
theorem der_33257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33257 :=
  CNF.rup_sound cl_33257 [cl_27889,cl_33247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27889 v h) (hints_cons _ _ _ (der_33247 v h) (by intro d hd; cases hd)))
def cl_33258 : CNF.NClause := [(85,false),(72,true),(91,false),(12,false),(43,false),(64,false)]
theorem der_33258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33258 :=
  CNF.rup_sound cl_33258 [cl_27890,cl_33255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27890 v h) (hints_cons _ _ _ (der_33255 v h) (by intro d hd; cases hd)))
def cl_33259 : CNF.NClause := [(85,false),(81,true),(72,true),(91,false),(43,false),(64,false)]
theorem der_33259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33259 :=
  CNF.rup_sound cl_33259 [cl_27891,cl_33255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27891 v h) (hints_cons _ _ _ (der_33255 v h) (by intro d hd; cases hd)))
def cl_33260 : CNF.NClause := [(43,false),(64,true),(72,true),(91,false),(12,false),(85,false)]
theorem der_33260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33260 :=
  CNF.rup_sound cl_33260 [cl_27892,cl_33257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27892 v h) (hints_cons _ _ _ (der_33257 v h) (by intro d hd; cases hd)))
def cl_33261 : CNF.NClause := [(85,false),(43,false),(64,true),(72,true),(12,true),(91,false)]
theorem der_33261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33261 :=
  CNF.rup_sound cl_33261 [cl_27893,cl_33257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27893 v h) (hints_cons _ _ _ (der_33257 v h) (by intro d hd; cases hd)))
def cl_33262 : CNF.NClause := [(43,false),(91,false),(64,true),(72,false),(81,false),(68,false)]
theorem der_33262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33262 :=
  CNF.rup_sound cl_33262 [cl_27896,cl_27895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27896 v h) (hints_cons _ _ _ (der_27895 v h) (by intro d hd; cases hd)))
def cl_33263 : CNF.NClause := [(43,false),(72,false),(68,true),(91,false),(64,false),(81,false)]
theorem der_33263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33263 :=
  CNF.rup_sound cl_33263 [cl_27898,cl_27897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27898 v h) (hints_cons _ _ _ (der_27897 v h) (by intro d hd; cases hd)))
def cl_33265 : CNF.NClause := [(68,true),(43,false),(64,true),(91,false),(72,false),(81,false)]
theorem der_33265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33265 :=
  CNF.rup_sound cl_33265 [cl_27900,cl_33246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27900 v h) (hints_cons _ _ _ (der_33246 v h) (by intro d hd; cases hd)))
def cl_33266 : CNF.NClause := [(81,false),(43,false),(72,true),(91,false),(64,false),(68,false)]
theorem der_33266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33266 :=
  CNF.rup_sound cl_33266 [cl_27902,cl_27901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27902 v h) (hints_cons _ _ _ (der_27901 v h) (by intro d hd; cases hd)))
def cl_33267 : CNF.NClause := [(43,false),(64,true),(91,false),(12,false),(81,false),(68,false)]
theorem der_33267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33267 :=
  CNF.rup_sound cl_33267 [cl_27903,cl_27895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27903 v h) (hints_cons _ _ _ (der_27895 v h) (by intro d hd; cases hd)))
def cl_33268 : CNF.NClause := [(43,false),(64,true),(72,true),(91,false),(81,false),(68,false)]
theorem der_33268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33268 :=
  CNF.rup_sound cl_33268 [cl_27904,cl_33267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27904 v h) (hints_cons _ _ _ (der_33267 v h) (by intro d hd; cases hd)))
def cl_33269 : CNF.NClause := [(68,true),(81,false),(91,false),(12,false),(64,false),(43,false)]
theorem der_33269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33269 :=
  CNF.rup_sound cl_33269 [cl_27905,cl_33263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27905 v h) (hints_cons _ _ _ (der_33263 v h) (by intro d hd; cases hd)))
def cl_33270 : CNF.NClause := [(81,false),(43,false),(68,true),(91,false),(64,false),(12,true)]
theorem der_33270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33270 :=
  CNF.rup_sound cl_33270 [cl_27906,cl_33263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27906 v h) (hints_cons _ _ _ (der_33263 v h) (by intro d hd; cases hd)))
def cl_33271 : CNF.NClause := [(68,true),(81,false),(64,true),(91,false),(12,false),(43,false)]
theorem der_33271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33271 :=
  CNF.rup_sound cl_33271 [cl_27907,cl_33265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27907 v h) (hints_cons _ _ _ (der_33265 v h) (by intro d hd; cases hd)))
def cl_33272 : CNF.NClause := [(81,false),(43,false),(68,true),(64,true),(91,false),(12,true)]
theorem der_33272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33272 :=
  CNF.rup_sound cl_33272 [cl_27908,cl_33265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27908 v h) (hints_cons _ _ _ (der_33265 v h) (by intro d hd; cases hd)))
def cl_33273 : CNF.NClause := [(43,false),(12,true),(91,false),(72,false),(64,false),(68,false)]
theorem der_33273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33273 :=
  CNF.rup_sound cl_33273 [cl_27910,cl_27894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27910 v h) (hints_cons _ _ _ (der_27894 v h) (by intro d hd; cases hd)))
def cl_33274 : CNF.NClause := [(43,false),(64,true),(91,false),(12,false),(72,false),(68,false)]
theorem der_33274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33274 :=
  CNF.rup_sound cl_33274 [cl_27911,cl_33251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27911 v h) (hints_cons _ _ _ (der_33251 v h) (by intro d hd; cases hd)))
def cl_33275 : CNF.NClause := [(68,true),(43,false),(91,false),(12,false),(72,false),(64,false)]
theorem der_33275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33275 :=
  CNF.rup_sound cl_33275 [cl_27913,cl_33263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27913 v h) (hints_cons _ _ _ (der_33263 v h) (by intro d hd; cases hd)))
def cl_33276 : CNF.NClause := [(68,true),(43,false),(64,true),(91,false),(12,false),(72,false)]
theorem der_33276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33276 :=
  CNF.rup_sound cl_33276 [cl_27915,cl_33265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27915 v h) (hints_cons _ _ _ (der_33265 v h) (by intro d hd; cases hd)))
def cl_33277 : CNF.NClause := [(43,false),(91,false),(68,true),(64,true),(81,true),(72,false)]
theorem der_33277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33277 :=
  CNF.rup_sound cl_33277 [cl_27916,cl_33276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27916 v h) (hints_cons _ _ _ (der_33276 v h) (by intro d hd; cases hd)))
def cl_33278 : CNF.NClause := [(43,false),(72,true),(91,false),(12,false),(64,false),(68,false)]
theorem der_33278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33278 :=
  CNF.rup_sound cl_33278 [cl_27917,cl_33266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27917 v h) (hints_cons _ _ _ (der_33266 v h) (by intro d hd; cases hd)))
def cl_33279 : CNF.NClause := [(43,false),(68,false),(81,true),(72,true),(91,false),(12,false)]
theorem der_33279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33279 :=
  CNF.rup_sound cl_33279 [cl_27919,cl_33278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27919 v h) (hints_cons _ _ _ (der_33278 v h) (by intro d hd; cases hd)))
def cl_33280 : CNF.NClause := [(43,false),(12,true),(64,true),(72,true),(91,false),(68,false)]
theorem der_33280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33280 :=
  CNF.rup_sound cl_33280 [cl_27920,cl_33268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27920 v h) (hints_cons _ _ _ (der_33268 v h) (by intro d hd; cases hd)))
def cl_33281 : CNF.NClause := [(43,false),(81,true),(72,true),(91,false),(12,false),(64,false)]
theorem der_33281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33281 :=
  CNF.rup_sound cl_33281 [cl_27921,cl_33278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27921 v h) (hints_cons _ _ _ (der_33278 v h) (by intro d hd; cases hd)))
def cl_33282 : CNF.NClause := [(43,false),(91,false),(68,true),(81,true),(72,true),(64,false)]
theorem der_33282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33282 :=
  CNF.rup_sound cl_33282 [cl_27922,cl_33281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27922 v h) (hints_cons _ _ _ (der_33281 v h) (by intro d hd; cases hd)))
def cl_33283 : CNF.NClause := [(68,true),(43,false),(64,true),(91,false),(12,false),(85,true)]
theorem der_33283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33283 :=
  CNF.rup_sound cl_33283 [cl_27923,cl_33276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27923 v h) (hints_cons _ _ _ (der_33276 v h) (by intro d hd; cases hd)))
def cl_33284 : CNF.NClause := [(85,true),(43,false),(68,true),(64,true),(81,true),(91,false)]
theorem der_33284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33284 :=
  CNF.rup_sound cl_33284 [cl_27924,cl_33283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27924 v h) (hints_cons _ _ _ (der_33283 v h) (by intro d hd; cases hd)))
def cl_33285 : CNF.NClause := [(81,false),(43,false),(64,true),(72,false),(85,false),(68,false)]
theorem der_33285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33285 :=
  CNF.rup_sound cl_33285 [cl_27927,cl_27926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27927 v h) (hints_cons _ _ _ (der_27926 v h) (by intro d hd; cases hd)))
def cl_33286 : CNF.NClause := [(85,false),(43,false),(12,true),(72,false),(64,false),(81,false)]
theorem der_33286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33286 :=
  CNF.rup_sound cl_33286 [cl_27929,cl_27925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27929 v h) (hints_cons _ _ _ (der_27925 v h) (by intro d hd; cases hd)))
def cl_33287 : CNF.NClause := [(68,true),(43,false),(12,false),(72,false),(85,false),(81,false)]
theorem der_33287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33287 :=
  CNF.rup_sound cl_33287 [cl_27930,cl_27928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27930 v h) (hints_cons _ _ _ (der_27928 v h) (by intro d hd; cases hd)))
def cl_33288 : CNF.NClause := [(43,false),(64,true),(68,true),(72,false),(85,false),(81,false)]
theorem der_33288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33288 :=
  CNF.rup_sound cl_33288 [cl_27931,cl_33287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27931 v h) (hints_cons _ _ _ (der_33287 v h) (by intro d hd; cases hd)))
def cl_33289 : CNF.NClause := [(85,false),(43,false),(72,true),(64,false),(81,false),(68,false)]
theorem der_33289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33289 :=
  CNF.rup_sound cl_33289 [cl_27933,cl_27932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27933 v h) (hints_cons _ _ _ (der_27932 v h) (by intro d hd; cases hd)))
def cl_33290 : CNF.NClause := [(43,false),(72,true),(12,false),(85,false),(81,false),(68,false)]
theorem der_33290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33290 :=
  CNF.rup_sound cl_33290 [cl_27934,cl_33289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27934 v h) (hints_cons _ _ _ (der_33289 v h) (by intro d hd; cases hd)))
def cl_33291 : CNF.NClause := [(85,false),(43,false),(72,true),(81,false),(68,false),(91,true)]
theorem der_33291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33291 :=
  CNF.rup_sound cl_33291 [cl_27935,cl_33290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27935 v h) (hints_cons _ _ _ (der_33290 v h) (by intro d hd; cases hd)))
def cl_33292 : CNF.NClause := [(85,false),(43,false),(12,false),(72,true),(64,false),(81,false)]
theorem der_33292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33292 :=
  CNF.rup_sound cl_33292 [cl_27936,cl_33258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27936 v h) (hints_cons _ _ _ (der_33258 v h) (by intro d hd; cases hd)))
def cl_33293 : CNF.NClause := [(85,false),(43,false),(72,true),(64,false),(81,false),(91,true)]
theorem der_33293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33293 :=
  CNF.rup_sound cl_33293 [cl_27937,cl_33292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27937 v h) (hints_cons _ _ _ (der_33292 v h) (by intro d hd; cases hd)))
def cl_33294 : CNF.NClause := [(68,true),(43,false),(64,true),(12,false),(85,false),(81,false)]
theorem der_33294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33294 :=
  CNF.rup_sound cl_33294 [cl_27938,cl_33287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27938 v h) (hints_cons _ _ _ (der_33287 v h) (by intro d hd; cases hd)))
def cl_33296 : CNF.NClause := [(43,false),(12,true),(72,false),(85,false),(64,false),(68,false)]
theorem der_33296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33296 :=
  CNF.rup_sound cl_33296 [cl_27941,cl_27925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27941 v h) (hints_cons _ _ _ (der_27925 v h) (by intro d hd; cases hd)))
def cl_33297 : CNF.NClause := [(43,false),(12,false),(72,false),(85,false),(68,false),(64,true)]
theorem der_33297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33297 :=
  CNF.rup_sound cl_33297 [cl_27942,cl_33251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27942 v h) (hints_cons _ _ _ (der_33251 v h) (by intro d hd; cases hd)))
def cl_33298 : CNF.NClause := [(43,false),(12,true),(81,true),(72,false),(85,false),(68,false)]
theorem der_33298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33298 :=
  CNF.rup_sound cl_33298 [cl_27943,cl_33296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27943 v h) (hints_cons _ _ _ (der_33296 v h) (by intro d hd; cases hd)))
def cl_33299 : CNF.NClause := [(68,true),(43,false),(72,false),(85,false),(64,false),(12,true)]
theorem der_33299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33299 :=
  CNF.rup_sound cl_33299 [cl_27945,cl_33252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27945 v h) (hints_cons _ _ _ (der_33252 v h) (by intro d hd; cases hd)))
def cl_33300 : CNF.NClause := [(43,false),(64,true),(81,true),(12,false),(72,false),(85,false)]
theorem der_33300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33300 :=
  CNF.rup_sound cl_33300 [cl_27946,cl_33297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27946 v h) (hints_cons _ _ _ (der_33297 v h) (by intro d hd; cases hd)))
def cl_33301 : CNF.NClause := [(85,false),(43,false),(68,true),(64,true),(81,true),(72,false)]
theorem der_33301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33301 :=
  CNF.rup_sound cl_33301 [cl_27947,cl_33300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27947 v h) (hints_cons _ _ _ (der_33300 v h) (by intro d hd; cases hd)))
def cl_33302 : CNF.NClause := [(43,false),(12,false),(85,false),(64,false),(68,false),(72,true)]
theorem der_33302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33302 :=
  CNF.rup_sound cl_33302 [cl_27948,cl_27886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27948 v h) (hints_cons _ _ _ (der_27886 v h) (by intro d hd; cases hd)))
def cl_33303 : CNF.NClause := [(43,false),(12,true),(81,true),(85,false),(64,false),(68,false)]
theorem der_33303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33303 :=
  CNF.rup_sound cl_33303 [cl_27949,cl_33296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27949 v h) (hints_cons _ _ _ (der_33296 v h) (by intro d hd; cases hd)))
def cl_33304 : CNF.NClause := [(85,false),(43,false),(72,true),(12,false),(64,true),(68,false)]
theorem der_33304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33304 :=
  CNF.rup_sound cl_33304 [cl_27950,cl_33290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27950 v h) (hints_cons _ _ _ (der_33290 v h) (by intro d hd; cases hd)))
def cl_33305 : CNF.NClause := [(43,false),(12,true),(64,true),(81,true),(85,false),(68,false)]
theorem der_33305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33305 :=
  CNF.rup_sound cl_33305 [cl_27951,cl_33298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27951 v h) (hints_cons _ _ _ (der_33298 v h) (by intro d hd; cases hd)))
def cl_33306 : CNF.NClause := [(68,true),(85,false),(72,true),(12,false),(43,false),(64,false)]
theorem der_33306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33306 :=
  CNF.rup_sound cl_33306 [cl_27952,cl_33292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27952 v h) (hints_cons _ _ _ (der_33292 v h) (by intro d hd; cases hd)))
def cl_33307 : CNF.NClause := [(85,false),(43,false),(68,true),(81,true),(72,true),(64,false)]
theorem der_33307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33307 :=
  CNF.rup_sound cl_33307 [cl_27953,cl_33306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27953 v h) (hints_cons _ _ _ (der_33306 v h) (by intro d hd; cases hd)))
def cl_33308 : CNF.NClause := [(68,true),(43,false),(64,true),(72,true),(12,false),(85,false)]
theorem der_33308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33308 :=
  CNF.rup_sound cl_33308 [cl_27954,cl_33294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27954 v h) (hints_cons _ _ _ (der_33294 v h) (by intro d hd; cases hd)))
def cl_33309 : CNF.NClause := [(85,false),(43,false),(68,true),(64,true),(72,true),(91,true)]
theorem der_33309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33309 :=
  CNF.rup_sound cl_33309 [cl_27955,cl_33308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27955 v h) (hints_cons _ _ _ (der_33308 v h) (by intro d hd; cases hd)))
def cl_33310 : CNF.NClause := [(81,false),(43,false),(72,false),(12,true),(64,false),(68,false)]
theorem der_33310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33310 :=
  CNF.rup_sound cl_33310 [cl_27957,cl_27894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27957 v h) (hints_cons _ _ _ (der_27894 v h) (by intro d hd; cases hd)))
def cl_33311 : CNF.NClause := [(43,false),(81,false),(64,true),(12,false),(72,false),(68,false)]
theorem der_33311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33311 :=
  CNF.rup_sound cl_33311 [cl_27958,cl_33285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27958 v h) (hints_cons _ _ _ (der_33285 v h) (by intro d hd; cases hd)))
def cl_33312 : CNF.NClause := [(81,false),(43,false),(64,true),(12,true),(72,false),(68,false)]
theorem der_33312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33312 :=
  CNF.rup_sound cl_33312 [cl_27959,cl_33262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27959 v h) (hints_cons _ _ _ (der_33262 v h) (by intro d hd; cases hd)))
def cl_33313 : CNF.NClause := [(68,true),(43,false),(72,false),(64,false),(81,false),(85,true)]
theorem der_33313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33313 :=
  CNF.rup_sound cl_33313 [cl_27961,cl_33263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27961 v h) (hints_cons _ _ _ (der_33263 v h) (by intro d hd; cases hd)))
def cl_33314 : CNF.NClause := [(43,false),(64,true),(12,false),(72,false),(81,false),(85,true)]
theorem der_33314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33314 :=
  CNF.rup_sound cl_33314 [cl_27962,cl_33311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27962 v h) (hints_cons _ _ _ (der_33311 v h) (by intro d hd; cases hd)))
def cl_33315 : CNF.NClause := [(68,true),(43,false),(12,true),(64,true),(72,false),(81,false)]
theorem der_33315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33315 :=
  CNF.rup_sound cl_33315 [cl_27963,cl_33265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27963 v h) (hints_cons _ _ _ (der_33265 v h) (by intro d hd; cases hd)))
def cl_33316 : CNF.NClause := [(43,false),(72,true),(12,false),(64,false),(81,false),(68,false)]
theorem der_33316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33316 :=
  CNF.rup_sound cl_33316 [cl_27964,cl_33289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27964 v h) (hints_cons _ _ _ (der_33289 v h) (by intro d hd; cases hd)))
def cl_33318 : CNF.NClause := [(43,false),(12,true),(64,true),(81,false),(85,true),(68,false)]
theorem der_33318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33318 :=
  CNF.rup_sound cl_33318 [cl_27967,cl_33312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27967 v h) (hints_cons _ _ _ (der_33312 v h) (by intro d hd; cases hd)))
def cl_33319 : CNF.NClause := [(43,false),(91,true),(12,false),(64,false),(81,false),(72,true)]
theorem der_33319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33319 :=
  CNF.rup_sound cl_33319 [cl_27968,cl_33293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27968 v h) (hints_cons _ _ _ (der_33293 v h) (by intro d hd; cases hd)))
def cl_33320 : CNF.NClause := [(85,true),(43,false),(68,true),(64,false),(81,false),(12,true)]
theorem der_33320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33320 :=
  CNF.rup_sound cl_33320 [cl_27969,cl_33313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27969 v h) (hints_cons _ _ _ (der_33313 v h) (by intro d hd; cases hd)))
def cl_33321 : CNF.NClause := [(68,true),(64,true),(72,true),(12,false),(81,false),(43,false)]
theorem der_33321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33321 :=
  CNF.rup_sound cl_33321 [cl_27970,cl_33294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27970 v h) (hints_cons _ _ _ (der_33294 v h) (by intro d hd; cases hd)))
def cl_33322 : CNF.NClause := [(68,true),(43,false),(91,true),(64,true),(72,true),(81,false)]
theorem der_33322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33322 :=
  CNF.rup_sound cl_33322 [cl_27971,cl_33321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27971 v h) (hints_cons _ _ _ (der_33321 v h) (by intro d hd; cases hd)))
def cl_33323 : CNF.NClause := [(81,true),(43,false),(12,false),(72,false),(64,false),(68,false)]
theorem der_33323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33323 :=
  CNF.rup_sound cl_33323 [cl_27972,cl_27909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27972 v h) (hints_cons _ _ _ (der_27909 v h) (by intro d hd; cases hd)))
def cl_33324 : CNF.NClause := [(43,false),(12,true),(81,true),(72,false),(64,false),(68,false)]
theorem der_33324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33324 :=
  CNF.rup_sound cl_33324 [cl_27973,cl_33296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27973 v h) (hints_cons _ _ _ (der_33296 v h) (by intro d hd; cases hd)))
def cl_33325 : CNF.NClause := [(43,false),(12,false),(72,false),(85,true),(68,false),(64,true)]
theorem der_33325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33325 :=
  CNF.rup_sound cl_33325 [cl_27974,cl_33274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27974 v h) (hints_cons _ _ _ (der_33274 v h) (by intro d hd; cases hd)))
def cl_33326 : CNF.NClause := [(43,false),(91,true),(81,true),(72,false),(68,false),(12,true)]
theorem der_33326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33326 :=
  CNF.rup_sound cl_33326 [cl_27975,cl_33324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27975 v h) (hints_cons _ _ _ (der_33324 v h) (by intro d hd; cases hd)))
def cl_33327 : CNF.NClause := [(85,true),(81,true),(12,false),(72,false),(64,false),(43,false)]
theorem der_33327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33327 :=
  CNF.rup_sound cl_33327 [cl_27976,cl_33323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27976 v h) (hints_cons _ _ _ (der_33323 v h) (by intro d hd; cases hd)))
def cl_33328 : CNF.NClause := [(81,true),(43,false),(91,true),(72,false),(64,false),(85,true)]
theorem der_33328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33328 :=
  CNF.rup_sound cl_33328 [cl_27977,cl_33327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27977 v h) (hints_cons _ _ _ (der_33327 v h) (by intro d hd; cases hd)))
def cl_33329 : CNF.NClause := [(68,true),(43,false),(64,true),(81,true),(12,false),(72,false)]
theorem der_33329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33329 :=
  CNF.rup_sound cl_33329 [cl_27978,cl_33277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27978 v h) (hints_cons _ _ _ (der_33277 v h) (by intro d hd; cases hd)))
def cl_33330 : CNF.NClause := [(85,true),(43,false),(68,true),(64,true),(81,true),(72,false)]
theorem der_33330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33330 :=
  CNF.rup_sound cl_33330 [cl_27979,cl_33329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27979 v h) (hints_cons _ _ _ (der_33329 v h) (by intro d hd; cases hd)))
def cl_33332 : CNF.NClause := [(43,false),(91,true),(64,false),(85,true),(68,false),(12,true)]
theorem der_33332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33332 :=
  CNF.rup_sound cl_33332 [cl_27981,cl_27965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27981 v h) (hints_cons _ _ _ (der_27965 v h) (by intro d hd; cases hd)))
def cl_33334 : CNF.NClause := [(43,false),(12,true),(64,true),(81,true),(72,true),(68,false)]
theorem der_33334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33334 :=
  CNF.rup_sound cl_33334 [cl_27983,cl_33305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27983 v h) (hints_cons _ _ _ (der_33305 v h) (by intro d hd; cases hd)))
def cl_33335 : CNF.NClause := [(68,true),(43,false),(81,true),(72,true),(12,false),(64,false)]
theorem der_33335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33335 :=
  CNF.rup_sound cl_33335 [cl_27984,cl_33306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27984 v h) (hints_cons _ _ _ (der_33306 v h) (by intro d hd; cases hd)))
def cl_33336 : CNF.NClause := [(43,false),(68,true),(81,true),(72,true),(12,true),(64,false)]
theorem der_33336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33336 :=
  CNF.rup_sound cl_33336 [cl_27985,cl_33282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27985 v h) (hints_cons _ _ _ (der_33282 v h) (by intro d hd; cases hd)))
def cl_33338 : CNF.NClause := [(33,false),(79,false),(64,true),(87,false),(84,false),(74,false)]
theorem der_33338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33338 :=
  CNF.rup_sound cl_33338 [cl_27991,cl_27990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27991 v h) (hints_cons _ _ _ (der_27990 v h) (by intro d hd; cases hd)))
def cl_33339 : CNF.NClause := [(69,false),(33,false),(64,true),(87,false),(79,false),(84,false)]
theorem der_33339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33339 :=
  CNF.rup_sound cl_33339 [cl_27994,cl_27993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27994 v h) (hints_cons _ _ _ (der_27993 v h) (by intro d hd; cases hd)))
def cl_33340 : CNF.NClause := [(33,false),(79,false),(74,true),(64,false),(87,false),(84,false)]
theorem der_33340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33340 :=
  CNF.rup_sound cl_33340 [cl_27996,cl_27995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27996 v h) (hints_cons _ _ _ (der_27995 v h) (by intro d hd; cases hd)))
def cl_33342 : CNF.NClause := [(84,false),(33,false),(64,true),(87,false),(69,false),(74,false)]
theorem der_33342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33342 :=
  CNF.rup_sound cl_33342 [cl_28001,cl_28000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28001 v h) (hints_cons _ _ _ (der_28000 v h) (by intro d hd; cases hd)))
def cl_33343 : CNF.NClause := [(84,false),(33,false),(79,true),(64,false),(87,false),(74,false)]
theorem der_33343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33343 :=
  CNF.rup_sound cl_33343 [cl_28003,cl_28002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28003 v h) (hints_cons _ _ _ (der_28002 v h) (by intro d hd; cases hd)))
def cl_33344 : CNF.NClause := [(69,true),(33,false),(64,true),(87,false),(84,false),(74,false)]
theorem der_33344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33344 :=
  CNF.rup_sound cl_33344 [cl_28005,cl_33338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28005 v h) (hints_cons _ _ _ (der_33338 v h) (by intro d hd; cases hd)))
def cl_33345 : CNF.NClause := [(69,false),(33,false),(74,true),(64,false),(87,false),(84,false)]
theorem der_33345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33345 :=
  CNF.rup_sound cl_33345 [cl_28007,cl_28006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28007 v h) (hints_cons _ _ _ (der_28006 v h) (by intro d hd; cases hd)))
def cl_33346 : CNF.NClause := [(69,false),(64,true),(87,false),(33,false),(84,false),(2,false)]
theorem der_33346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33346 :=
  CNF.rup_sound cl_33346 [cl_28008,cl_33342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28008 v h) (hints_cons _ _ _ (der_33342 v h) (by intro d hd; cases hd)))
def cl_33347 : CNF.NClause := [(74,true),(69,false),(64,true),(87,false),(33,false),(84,false)]
theorem der_33347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33347 :=
  CNF.rup_sound cl_33347 [cl_28009,cl_33339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28009 v h) (hints_cons _ _ _ (der_33339 v h) (by intro d hd; cases hd)))
def cl_33349 : CNF.NClause := [(74,true),(33,false),(69,true),(64,false),(87,false),(84,false)]
theorem der_33349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33349 :=
  CNF.rup_sound cl_33349 [cl_28011,cl_33340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28011 v h) (hints_cons _ _ _ (der_33340 v h) (by intro d hd; cases hd)))
def cl_33351 : CNF.NClause := [(69,true),(33,false),(74,true),(2,true),(87,false),(84,false)]
theorem der_33351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33351 :=
  CNF.rup_sound cl_33351 [cl_28013,cl_33349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28013 v h) (hints_cons _ _ _ (der_33349 v h) (by intro d hd; cases hd)))
def cl_33352 : CNF.NClause := [(33,false),(79,false),(64,true),(87,false),(69,false),(74,false)]
theorem der_33352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33352 :=
  CNF.rup_sound cl_33352 [cl_28016,cl_28015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28016 v h) (hints_cons _ _ _ (der_28015 v h) (by intro d hd; cases hd)))
def cl_33353 : CNF.NClause := [(74,false),(84,true),(64,false),(87,false),(79,false),(33,false)]
theorem der_33353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33353 :=
  CNF.rup_sound cl_33353 [cl_28018,cl_28014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28018 v h) (hints_cons _ _ _ (der_28014 v h) (by intro d hd; cases hd)))
def cl_33354 : CNF.NClause := [(69,true),(64,true),(33,false),(87,false),(79,false),(74,false)]
theorem der_33354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33354 :=
  CNF.rup_sound cl_33354 [cl_28020,cl_33338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28020 v h) (hints_cons _ _ _ (der_33338 v h) (by intro d hd; cases hd)))
def cl_33355 : CNF.NClause := [(33,false),(79,false),(74,true),(64,false),(87,false),(69,false)]
theorem der_33355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33355 :=
  CNF.rup_sound cl_33355 [cl_28022,cl_28021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28022 v h) (hints_cons _ _ _ (der_28021 v h) (by intro d hd; cases hd)))
def cl_33357 : CNF.NClause := [(74,true),(69,false),(64,true),(87,false),(79,false),(33,false)]
theorem der_33357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33357 :=
  CNF.rup_sound cl_33357 [cl_28024,cl_33347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28024 v h) (hints_cons _ _ _ (der_33347 v h) (by intro d hd; cases hd)))
def cl_33358 : CNF.NClause := [(74,true),(33,false),(64,false),(87,false),(79,false),(2,false)]
theorem der_33358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33358 :=
  CNF.rup_sound cl_33358 [cl_28025,cl_28021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28025 v h) (hints_cons _ _ _ (der_28021 v h) (by intro d hd; cases hd)))
def cl_33359 : CNF.NClause := [(33,false),(64,false),(74,true),(69,true),(87,false),(79,false)]
theorem der_33359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33359 :=
  CNF.rup_sound cl_33359 [cl_28026,cl_33358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28026 v h) (hints_cons _ _ _ (der_33358 v h) (by intro d hd; cases hd)))
def cl_33360 : CNF.NClause := [(33,false),(69,true),(64,true),(87,false),(79,false),(2,false)]
theorem der_33360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33360 :=
  CNF.rup_sound cl_33360 [cl_28027,cl_33354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28027 v h) (hints_cons _ _ _ (der_33354 v h) (by intro d hd; cases hd)))
def cl_33361 : CNF.NClause := [(33,false),(74,true),(2,true),(64,true),(87,false),(79,false)]
theorem der_33361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33361 :=
  CNF.rup_sound cl_33361 [cl_28028,cl_33357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28028 v h) (hints_cons _ _ _ (der_33357 v h) (by intro d hd; cases hd)))
def cl_33362 : CNF.NClause := [(69,false),(33,false),(79,true),(64,false),(87,false),(74,false)]
theorem der_33362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33362 :=
  CNF.rup_sound cl_33362 [cl_28030,cl_28029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28030 v h) (hints_cons _ _ _ (der_28029 v h) (by intro d hd; cases hd)))
def cl_33363 : CNF.NClause := [(74,false),(33,false),(79,true),(87,false),(69,false),(2,false)]
theorem der_33363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33363 :=
  CNF.rup_sound cl_33363 [cl_28031,cl_28029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28031 v h) (hints_cons _ _ _ (der_28029 v h) (by intro d hd; cases hd)))
def cl_33364 : CNF.NClause := [(69,false),(33,false),(79,true),(84,true),(87,false),(74,false)]
theorem der_33364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33364 :=
  CNF.rup_sound cl_33364 [cl_28032,cl_33362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28032 v h) (hints_cons _ _ _ (der_33362 v h) (by intro d hd; cases hd)))
def cl_33366 : CNF.NClause := [(33,false),(79,true),(84,true),(64,false),(87,false),(74,false)]
theorem der_33366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33366 :=
  CNF.rup_sound cl_33366 [cl_28034,cl_33362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28034 v h) (hints_cons _ _ _ (der_33362 v h) (by intro d hd; cases hd)))
def cl_33368 : CNF.NClause := [(33,false),(69,true),(64,true),(2,true),(87,false),(74,false)]
theorem der_33368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33368 :=
  CNF.rup_sound cl_33368 [cl_28036,cl_33354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28036 v h) (hints_cons _ _ _ (der_33354 v h) (by intro d hd; cases hd)))
def cl_33369 : CNF.NClause := [(74,true),(69,false),(64,false),(87,false),(33,false),(2,false)]
theorem der_33369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33369 :=
  CNF.rup_sound cl_33369 [cl_28037,cl_33345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28037 v h) (hints_cons _ _ _ (der_33345 v h) (by intro d hd; cases hd)))
def cl_33370 : CNF.NClause := [(69,false),(33,false),(79,true),(64,false),(2,true),(87,false)]
theorem der_33370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33370 :=
  CNF.rup_sound cl_33370 [cl_28038,cl_33362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28038 v h) (hints_cons _ _ _ (der_33362 v h) (by intro d hd; cases hd)))
def cl_33371 : CNF.NClause := [(33,false),(64,true),(79,true),(87,false),(69,false),(2,false)]
theorem der_33371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33371 :=
  CNF.rup_sound cl_33371 [cl_28039,cl_33363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28039 v h) (hints_cons _ _ _ (der_33363 v h) (by intro d hd; cases hd)))
def cl_33372 : CNF.NClause := [(69,false),(33,false),(74,true),(64,true),(2,true),(87,false)]
theorem der_33372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33372 :=
  CNF.rup_sound cl_33372 [cl_28040,cl_33357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28040 v h) (hints_cons _ _ _ (der_33357 v h) (by intro d hd; cases hd)))
def cl_33373 : CNF.NClause := [(74,true),(33,false),(79,true),(64,false),(87,false),(2,false)]
theorem der_33373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33373 :=
  CNF.rup_sound cl_33373 [cl_28041,cl_33369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28041 v h) (hints_cons _ _ _ (der_33369 v h) (by intro d hd; cases hd)))
def cl_33374 : CNF.NClause := [(74,true),(69,true),(79,true),(33,false),(64,false),(87,false)]
theorem der_33374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33374 :=
  CNF.rup_sound cl_33374 [cl_28042,cl_33349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28042 v h) (hints_cons _ _ _ (der_33349 v h) (by intro d hd; cases hd)))
def cl_33377 : CNF.NClause := [(33,false),(69,false),(2,true),(79,false),(84,false),(74,false)]
theorem der_33377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33377 :=
  CNF.rup_sound cl_33377 [cl_28045,cl_26323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28045 v h) (hints_cons _ _ _ (der_26323 v h) (by intro d hd; cases hd)))
def cl_33378 : CNF.NClause := [(33,false),(64,true),(79,false),(69,false),(84,false),(74,false)]
theorem der_33378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33378 :=
  CNF.rup_sound cl_33378 [cl_28046,cl_26322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28046 v h) (hints_cons _ _ _ (der_26322 v h) (by intro d hd; cases hd)))
def cl_33379 : CNF.NClause := [(33,false),(2,true),(64,false),(79,false),(84,false),(74,false)]
theorem der_33379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33379 :=
  CNF.rup_sound cl_33379 [cl_28048,cl_33377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28048 v h) (hints_cons _ _ _ (der_33377 v h) (by intro d hd; cases hd)))
def cl_33380 : CNF.NClause := [(69,true),(33,false),(79,false),(84,false),(74,false),(2,false)]
theorem der_33380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33380 :=
  CNF.rup_sound cl_33380 [cl_28049,cl_28047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28049 v h) (hints_cons _ _ _ (der_28047 v h) (by intro d hd; cases hd)))
def cl_33381 : CNF.NClause := [(33,false),(84,false),(64,true),(2,true),(79,false),(74,false)]
theorem der_33381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33381 :=
  CNF.rup_sound cl_33381 [cl_28050,cl_33378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28050 v h) (hints_cons _ _ _ (der_33378 v h) (by intro d hd; cases hd)))
def cl_33382 : CNF.NClause := [(33,false),(2,true),(64,false),(79,false),(69,false),(84,false)]
theorem der_33382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33382 :=
  CNF.rup_sound cl_33382 [cl_28052,cl_33377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28052 v h) (hints_cons _ _ _ (der_33377 v h) (by intro d hd; cases hd)))
def cl_33383 : CNF.NClause := [(74,true),(69,false),(79,false),(33,false),(84,false),(2,false)]
theorem der_33383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33383 :=
  CNF.rup_sound cl_33383 [cl_28053,cl_28051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28053 v h) (hints_cons _ _ _ (der_28051 v h) (by intro d hd; cases hd)))
def cl_33384 : CNF.NClause := [(33,false),(2,true),(64,true),(79,false),(69,false),(84,false)]
theorem der_33384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33384 :=
  CNF.rup_sound cl_33384 [cl_28054,cl_26322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28054 v h) (hints_cons _ _ _ (der_26322 v h) (by intro d hd; cases hd)))
def cl_33385 : CNF.NClause := [(74,true),(33,false),(64,false),(79,false),(84,false),(2,false)]
theorem der_33385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33385 :=
  CNF.rup_sound cl_33385 [cl_28055,cl_33383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28055 v h) (hints_cons _ _ _ (der_33383 v h) (by intro d hd; cases hd)))
def cl_33386 : CNF.NClause := [(74,true),(33,false),(69,true),(64,false),(79,false),(84,false)]
theorem der_33386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33386 :=
  CNF.rup_sound cl_33386 [cl_28056,cl_33340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28056 v h) (hints_cons _ _ _ (der_33340 v h) (by intro d hd; cases hd)))
def cl_33388 : CNF.NClause := [(69,true),(33,false),(74,true),(2,true),(79,false),(84,false)]
theorem der_33388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33388 :=
  CNF.rup_sound cl_33388 [cl_28058,cl_33386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28058 v h) (hints_cons _ _ _ (der_33386 v h) (by intro d hd; cases hd)))
def cl_33389 : CNF.NClause := [(74,false),(33,false),(79,true),(64,false),(69,false),(84,false)]
theorem der_33389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33389 :=
  CNF.rup_sound cl_33389 [cl_28060,cl_28059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28060 v h) (hints_cons _ _ _ (der_28059 v h) (by intro d hd; cases hd)))
def cl_33390 : CNF.NClause := [(74,false),(33,false),(79,true),(69,false),(84,false),(2,false)]
theorem der_33390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33390 :=
  CNF.rup_sound cl_33390 [cl_28061,cl_28059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28061 v h) (hints_cons _ _ _ (der_28059 v h) (by intro d hd; cases hd)))
def cl_33391 : CNF.NClause := [(74,false),(33,false),(64,true),(69,false),(84,false),(2,true)]
theorem der_33391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33391 :=
  CNF.rup_sound cl_33391 [cl_28062,cl_33342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28062 v h) (hints_cons _ _ _ (der_33342 v h) (by intro d hd; cases hd)))
def cl_33394 : CNF.NClause := [(33,false),(64,true),(79,true),(84,false),(74,false),(2,false)]
theorem der_33394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33394 :=
  CNF.rup_sound cl_33394 [cl_28065,cl_33390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28065 v h) (hints_cons _ _ _ (der_33390 v h) (by intro d hd; cases hd)))
def cl_33395 : CNF.NClause := [(33,false),(84,false),(69,true),(64,true),(79,true),(74,false)]
theorem der_33395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33395 :=
  CNF.rup_sound cl_33395 [cl_28066,cl_33394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28066 v h) (hints_cons _ _ _ (der_33394 v h) (by intro d hd; cases hd)))
def cl_33396 : CNF.NClause := [(84,false),(79,true),(64,false),(69,false),(33,false),(87,true)]
theorem der_33396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33396 :=
  CNF.rup_sound cl_33396 [cl_28068,cl_33389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28068 v h) (hints_cons _ _ _ (der_33389 v h) (by intro d hd; cases hd)))
def cl_33397 : CNF.NClause := [(74,true),(69,false),(64,true),(33,false),(84,false),(2,false)]
theorem der_33397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33397 :=
  CNF.rup_sound cl_33397 [cl_28069,cl_33383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28069 v h) (hints_cons _ _ _ (der_33383 v h) (by intro d hd; cases hd)))
def cl_33398 : CNF.NClause := [(69,false),(33,false),(74,true),(64,true),(79,true),(84,false)]
theorem der_33398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33398 :=
  CNF.rup_sound cl_33398 [cl_28070,cl_33397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28070 v h) (hints_cons _ _ _ (der_33397 v h) (by intro d hd; cases hd)))
def cl_33402 : CNF.NClause := [(69,true),(33,false),(74,true),(2,true),(79,true),(84,false)]
theorem der_33402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33402 :=
  CNF.rup_sound cl_33402 [cl_28074,cl_33351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28074 v h) (hints_cons _ _ _ (der_33351 v h) (by intro d hd; cases hd)))
def cl_33403 : CNF.NClause := [(84,true),(33,false),(64,false),(79,false),(69,false),(74,false)]
theorem der_33403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33403 :=
  CNF.rup_sound cl_33403 [cl_28076,cl_33353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28076 v h) (hints_cons _ _ _ (der_33353 v h) (by intro d hd; cases hd)))
def cl_33404 : CNF.NClause := [(33,false),(64,true),(79,false),(69,false),(74,false),(2,false)]
theorem der_33404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33404 :=
  CNF.rup_sound cl_33404 [cl_28077,cl_33352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28077 v h) (hints_cons _ _ _ (der_33352 v h) (by intro d hd; cases hd)))
def cl_33406 : CNF.NClause := [(69,true),(33,false),(64,false),(79,false),(74,false),(2,false)]
theorem der_33406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33406 :=
  CNF.rup_sound cl_33406 [cl_28079,cl_33380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28079 v h) (hints_cons _ _ _ (der_33380 v h) (by intro d hd; cases hd)))
def cl_33407 : CNF.NClause := [(33,false),(84,true),(64,false),(79,false),(74,false),(87,true)]
theorem der_33407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33407 :=
  CNF.rup_sound cl_33407 [cl_28080,cl_33403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28080 v h) (hints_cons _ _ _ (der_33403 v h) (by intro d hd; cases hd)))
def cl_33408 : CNF.NClause := [(69,true),(84,true),(33,false),(79,false),(74,false),(2,false)]
theorem der_33408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33408 :=
  CNF.rup_sound cl_33408 [cl_28081,cl_33406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28081 v h) (hints_cons _ _ _ (der_33406 v h) (by intro d hd; cases hd)))
def cl_33409 : CNF.NClause := [(84,true),(33,false),(69,true),(79,false),(74,false),(87,true)]
theorem der_33409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33409 :=
  CNF.rup_sound cl_33409 [cl_28082,cl_33408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28082 v h) (hints_cons _ _ _ (der_33408 v h) (by intro d hd; cases hd)))
def cl_33410 : CNF.NClause := [(74,true),(33,false),(64,false),(79,false),(69,false),(2,false)]
theorem der_33410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33410 :=
  CNF.rup_sound cl_33410 [cl_28083,cl_33385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28083 v h) (hints_cons _ _ _ (der_33385 v h) (by intro d hd; cases hd)))
def cl_33411 : CNF.NClause := [(33,false),(2,true),(64,false),(79,false),(69,false),(87,true)]
theorem der_33411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33411 :=
  CNF.rup_sound cl_33411 [cl_28084,cl_33382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28084 v h) (hints_cons _ _ _ (der_33382 v h) (by intro d hd; cases hd)))
def cl_33412 : CNF.NClause := [(74,true),(33,false),(64,true),(84,true),(79,false),(69,false)]
theorem der_33412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33412 :=
  CNF.rup_sound cl_33412 [cl_28086,cl_33357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28086 v h) (hints_cons _ _ _ (der_33357 v h) (by intro d hd; cases hd)))
def cl_33414 : CNF.NClause := [(74,true),(33,false),(69,true),(84,true),(64,false),(79,false)]
theorem der_33414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33414 :=
  CNF.rup_sound cl_33414 [cl_28088,cl_33359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28088 v h) (hints_cons _ _ _ (der_33359 v h) (by intro d hd; cases hd)))
def cl_33415 : CNF.NClause := [(74,true),(33,false),(69,true),(84,true),(79,false),(2,false)]
theorem der_33415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33415 :=
  CNF.rup_sound cl_33415 [cl_28089,cl_33414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28089 v h) (hints_cons _ _ _ (der_33414 v h) (by intro d hd; cases hd)))
def cl_33416 : CNF.NClause := [(69,true),(33,false),(74,true),(84,true),(79,false),(87,true)]
theorem der_33416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33416 :=
  CNF.rup_sound cl_33416 [cl_28090,cl_33415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28090 v h) (hints_cons _ _ _ (der_33415 v h) (by intro d hd; cases hd)))
def cl_33417 : CNF.NClause := [(33,false),(79,true),(64,false),(69,false),(74,false),(2,false)]
theorem der_33417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33417 :=
  CNF.rup_sound cl_33417 [cl_28091,cl_33362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28091 v h) (hints_cons _ _ _ (der_33362 v h) (by intro d hd; cases hd)))
def cl_33418 : CNF.NClause := [(33,false),(79,true),(84,true),(64,false),(69,false),(74,false)]
theorem der_33418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33418 :=
  CNF.rup_sound cl_33418 [cl_28092,cl_33366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28092 v h) (hints_cons _ _ _ (der_33366 v h) (by intro d hd; cases hd)))
def cl_33419 : CNF.NClause := [(74,false),(33,false),(64,true),(69,false),(2,true),(87,true)]
theorem der_33419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33419 :=
  CNF.rup_sound cl_33419 [cl_28094,cl_33391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28094 v h) (hints_cons _ _ _ (der_33391 v h) (by intro d hd; cases hd)))
def cl_33420 : CNF.NClause := [(69,true),(33,false),(64,false),(74,false),(2,false),(87,true)]
theorem der_33420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33420 :=
  CNF.rup_sound cl_33420 [cl_28095,cl_33406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28095 v h) (hints_cons _ _ _ (der_33406 v h) (by intro d hd; cases hd)))
def cl_33421 : CNF.NClause := [(74,false),(33,false),(69,true),(79,true),(64,false),(87,true)]
theorem der_33421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33421 :=
  CNF.rup_sound cl_33421 [cl_28096,cl_33420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28096 v h) (hints_cons _ _ _ (der_33420 v h) (by intro d hd; cases hd)))
def cl_33422 : CNF.NClause := [(69,true),(33,false),(64,true),(79,true),(74,false),(2,false)]
theorem der_33422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33422 :=
  CNF.rup_sound cl_33422 [cl_28097,cl_33395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28097 v h) (hints_cons _ _ _ (der_33395 v h) (by intro d hd; cases hd)))
def cl_33423 : CNF.NClause := [(69,true),(33,false),(64,true),(79,true),(74,false),(87,true)]
theorem der_33423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33423 :=
  CNF.rup_sound cl_33423 [cl_28098,cl_33395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28098 v h) (hints_cons _ _ _ (der_33395 v h) (by intro d hd; cases hd)))
def cl_33425 : CNF.NClause := [(69,false),(33,false),(74,true),(79,true),(64,false),(2,true)]
theorem der_33425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33425 :=
  CNF.rup_sound cl_33425 [cl_28100,cl_33370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28100 v h) (hints_cons _ _ _ (der_33370 v h) (by intro d hd; cases hd)))
def chunk020 : List CNF.NClause := [cl_32862,cl_32863,cl_32864,cl_32865,cl_32866,cl_32867,cl_32868,cl_32869,cl_32870,cl_32871,cl_32872,cl_32873,cl_32874,cl_32875,cl_32876,cl_32877,cl_32878,cl_32879,cl_32880,cl_32881,cl_32882,cl_32883,cl_32886,cl_32887,cl_32888,cl_32889,cl_32890,cl_32891,cl_32892,cl_32894,cl_32895,cl_32896,cl_32897,cl_32898,cl_32899,cl_32900,cl_32901,cl_32902,cl_32903,cl_32904,cl_32905,cl_32906,cl_32907,cl_32908,cl_32909,cl_32910,cl_32911,cl_32912,cl_32913,cl_32914,cl_32916,cl_32917,cl_32918,cl_32919,cl_32921,cl_32922,cl_32923,cl_32924,cl_32926,cl_32927,cl_32928,cl_32929,cl_32930,cl_32931,cl_32933,cl_32934,cl_32935,cl_32936,cl_32937,cl_32938,cl_32939,cl_32940,cl_32941,cl_32942,cl_32943,cl_32944,cl_32945,cl_32947,cl_32948,cl_32949,cl_32950,cl_32951,cl_32952,cl_32953,cl_32954,cl_32955,cl_32956,cl_32957,cl_32958,cl_32959,cl_32960,cl_32961,cl_32962,cl_32963,cl_32964,cl_32965,cl_32966,cl_32967,cl_32968,cl_32969,cl_32970,cl_32971,cl_32972,cl_32973,cl_32974,cl_32975,cl_32976,cl_32977,cl_32978,cl_32979,cl_32980,cl_32981,cl_32982,cl_32983,cl_32984,cl_32985,cl_32986,cl_32987,cl_32988,cl_32990,cl_32991,cl_32993,cl_32994,cl_32995,cl_32996,cl_32997,cl_32998,cl_32999,cl_33000,cl_33001,cl_33003,cl_33004,cl_33005,cl_33006,cl_33007,cl_33008,cl_33009,cl_33010,cl_33011,cl_33012,cl_33013,cl_33014,cl_33015,cl_33016,cl_33017,cl_33018,cl_33019,cl_33020,cl_33021,cl_33022,cl_33023,cl_33024,cl_33025,cl_33026,cl_33027,cl_33028,cl_33029,cl_33030,cl_33031,cl_33033,cl_33034,cl_33035,cl_33036,cl_33037,cl_33038,cl_33040,cl_33041,cl_33042,cl_33044,cl_33045,cl_33046,cl_33047,cl_33048,cl_33049,cl_33050,cl_33051,cl_33052,cl_33053,cl_33054,cl_33056,cl_33057,cl_33060,cl_33061,cl_33063,cl_33064,cl_33066,cl_33067,cl_33068,cl_33069,cl_33070,cl_33071,cl_33072,cl_33073,cl_33074,cl_33075,cl_33076,cl_33077,cl_33079,cl_33080,cl_33081,cl_33082,cl_33083,cl_33084,cl_33085,cl_33086,cl_33087,cl_33088,cl_33089,cl_33090,cl_33091,cl_33092,cl_33093,cl_33094,cl_33095,cl_33096,cl_33097,cl_33098,cl_33099,cl_33100,cl_33101,cl_33102,cl_33103,cl_33104,cl_33105,cl_33106,cl_33107,cl_33108,cl_33109,cl_33110,cl_33111,cl_33112,cl_33113,cl_33114,cl_33116,cl_33117,cl_33119,cl_33120,cl_33121,cl_33122,cl_33123,cl_33124,cl_33125,cl_33126,cl_33127,cl_33128,cl_33129,cl_33130,cl_33131,cl_33132,cl_33133,cl_33134,cl_33135,cl_33136,cl_33137,cl_33138,cl_33139,cl_33140,cl_33141,cl_33142,cl_33143,cl_33144,cl_33146,cl_33147,cl_33148,cl_33149,cl_33150,cl_33151,cl_33152,cl_33153,cl_33154,cl_33156,cl_33157,cl_33158,cl_33159,cl_33160,cl_33161,cl_33162,cl_33163,cl_33164,cl_33165,cl_33166,cl_33167,cl_33169,cl_33170,cl_33171,cl_33172,cl_33173,cl_33174,cl_33175,cl_33176,cl_33179,cl_33180,cl_33181,cl_33182,cl_33183,cl_33184,cl_33185,cl_33186,cl_33187,cl_33188,cl_33189,cl_33190,cl_33191,cl_33193,cl_33194,cl_33195,cl_33196,cl_33197,cl_33198,cl_33199,cl_33200,cl_33201,cl_33203,cl_33204,cl_33205,cl_33206,cl_33207,cl_33208,cl_33209,cl_33210,cl_33211,cl_33212,cl_33213,cl_33214,cl_33215,cl_33216,cl_33217,cl_33218,cl_33219,cl_33220,cl_33221,cl_33223,cl_33224,cl_33225,cl_33227,cl_33230,cl_33233,cl_33234,cl_33236,cl_33239,cl_33240,cl_33241,cl_33242,cl_33243,cl_33244,cl_33245,cl_33246,cl_33247,cl_33250,cl_33251,cl_33252,cl_33253,cl_33254,cl_33255,cl_33257,cl_33258,cl_33259,cl_33260,cl_33261,cl_33262,cl_33263,cl_33265,cl_33266,cl_33267,cl_33268,cl_33269,cl_33270,cl_33271,cl_33272,cl_33273,cl_33274,cl_33275,cl_33276,cl_33277,cl_33278,cl_33279,cl_33280,cl_33281,cl_33282,cl_33283,cl_33284,cl_33285,cl_33286,cl_33287,cl_33288,cl_33289,cl_33290,cl_33291,cl_33292,cl_33293,cl_33294,cl_33296,cl_33297,cl_33298,cl_33299,cl_33300,cl_33301,cl_33302,cl_33303,cl_33304,cl_33305,cl_33306,cl_33307,cl_33308,cl_33309,cl_33310,cl_33311,cl_33312,cl_33313,cl_33314,cl_33315,cl_33316,cl_33318,cl_33319,cl_33320,cl_33321,cl_33322,cl_33323,cl_33324,cl_33325,cl_33326,cl_33327,cl_33328,cl_33329,cl_33330,cl_33332,cl_33334,cl_33335,cl_33336,cl_33338,cl_33339,cl_33340,cl_33342,cl_33343,cl_33344,cl_33345,cl_33346,cl_33347,cl_33349,cl_33351,cl_33352,cl_33353,cl_33354,cl_33355,cl_33357,cl_33358,cl_33359,cl_33360,cl_33361,cl_33362,cl_33363,cl_33364,cl_33366,cl_33368,cl_33369,cl_33370,cl_33371,cl_33372,cl_33373,cl_33374,cl_33377,cl_33378,cl_33379,cl_33380,cl_33381,cl_33382,cl_33383,cl_33384,cl_33385,cl_33386,cl_33388,cl_33389,cl_33390,cl_33391,cl_33394,cl_33395,cl_33396,cl_33397,cl_33398,cl_33402,cl_33403,cl_33404,cl_33406,cl_33407,cl_33408,cl_33409,cl_33410,cl_33411,cl_33412,cl_33414,cl_33415,cl_33416,cl_33417,cl_33418,cl_33419,cl_33420,cl_33421,cl_33422,cl_33423,cl_33425]
theorem chunk_sound020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk020, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_32862 v h) (hints_cons _ _ _ (der_32863 v h) (hints_cons _ _ _ (der_32864 v h) (hints_cons _ _ _ (der_32865 v h) (hints_cons _ _ _ (der_32866 v h) (hints_cons _ _ _ (der_32867 v h) (hints_cons _ _ _ (der_32868 v h) (hints_cons _ _ _ (der_32869 v h) (hints_cons _ _ _ (der_32870 v h) (hints_cons _ _ _ (der_32871 v h) (hints_cons _ _ _ (der_32872 v h) (hints_cons _ _ _ (der_32873 v h) (hints_cons _ _ _ (der_32874 v h) (hints_cons _ _ _ (der_32875 v h) (hints_cons _ _ _ (der_32876 v h) (hints_cons _ _ _ (der_32877 v h) (hints_cons _ _ _ (der_32878 v h) (hints_cons _ _ _ (der_32879 v h) (hints_cons _ _ _ (der_32880 v h) (hints_cons _ _ _ (der_32881 v h) (hints_cons _ _ _ (der_32882 v h) (hints_cons _ _ _ (der_32883 v h) (hints_cons _ _ _ (der_32886 v h) (hints_cons _ _ _ (der_32887 v h) (hints_cons _ _ _ (der_32888 v h) (hints_cons _ _ _ (der_32889 v h) (hints_cons _ _ _ (der_32890 v h) (hints_cons _ _ _ (der_32891 v h) (hints_cons _ _ _ (der_32892 v h) (hints_cons _ _ _ (der_32894 v h) (hints_cons _ _ _ (der_32895 v h) (hints_cons _ _ _ (der_32896 v h) (hints_cons _ _ _ (der_32897 v h) (hints_cons _ _ _ (der_32898 v h) (hints_cons _ _ _ (der_32899 v h) (hints_cons _ _ _ (der_32900 v h) (hints_cons _ _ _ (der_32901 v h) (hints_cons _ _ _ (der_32902 v h) (hints_cons _ _ _ (der_32903 v h) (hints_cons _ _ _ (der_32904 v h) (hints_cons _ _ _ (der_32905 v h) (hints_cons _ _ _ (der_32906 v h) (hints_cons _ _ _ (der_32907 v h) (hints_cons _ _ _ (der_32908 v h) (hints_cons _ _ _ (der_32909 v h) (hints_cons _ _ _ (der_32910 v h) (hints_cons _ _ _ (der_32911 v h) (hints_cons _ _ _ (der_32912 v h) (hints_cons _ _ _ (der_32913 v h) (hints_cons _ _ _ (der_32914 v h) (hints_cons _ _ _ (der_32916 v h) (hints_cons _ _ _ (der_32917 v h) (hints_cons _ _ _ (der_32918 v h) (hints_cons _ _ _ (der_32919 v h) (hints_cons _ _ _ (der_32921 v h) (hints_cons _ _ _ (der_32922 v h) (hints_cons _ _ _ (der_32923 v h) (hints_cons _ _ _ (der_32924 v h) (hints_cons _ _ _ (der_32926 v h) (hints_cons _ _ _ (der_32927 v h) (hints_cons _ _ _ (der_32928 v h) (hints_cons _ _ _ (der_32929 v h) (hints_cons _ _ _ (der_32930 v h) (hints_cons _ _ _ (der_32931 v h) (hints_cons _ _ _ (der_32933 v h) (hints_cons _ _ _ (der_32934 v h) (hints_cons _ _ _ (der_32935 v h) (hints_cons _ _ _ (der_32936 v h) (hints_cons _ _ _ (der_32937 v h) (hints_cons _ _ _ (der_32938 v h) (hints_cons _ _ _ (der_32939 v h) (hints_cons _ _ _ (der_32940 v h) (hints_cons _ _ _ (der_32941 v h) (hints_cons _ _ _ (der_32942 v h) (hints_cons _ _ _ (der_32943 v h) (hints_cons _ _ _ (der_32944 v h) (hints_cons _ _ _ (der_32945 v h) (hints_cons _ _ _ (der_32947 v h) (hints_cons _ _ _ (der_32948 v h) (hints_cons _ _ _ (der_32949 v h) (hints_cons _ _ _ (der_32950 v h) (hints_cons _ _ _ (der_32951 v h) (hints_cons _ _ _ (der_32952 v h) (hints_cons _ _ _ (der_32953 v h) (hints_cons _ _ _ (der_32954 v h) (hints_cons _ _ _ (der_32955 v h) (hints_cons _ _ _ (der_32956 v h) (hints_cons _ _ _ (der_32957 v h) (hints_cons _ _ _ (der_32958 v h) (hints_cons _ _ _ (der_32959 v h) (hints_cons _ _ _ (der_32960 v h) (hints_cons _ _ _ (der_32961 v h) (hints_cons _ _ _ (der_32962 v h) (hints_cons _ _ _ (der_32963 v h) (hints_cons _ _ _ (der_32964 v h) (hints_cons _ _ _ (der_32965 v h) (hints_cons _ _ _ (der_32966 v h) (hints_cons _ _ _ (der_32967 v h) (hints_cons _ _ _ (der_32968 v h) (hints_cons _ _ _ (der_32969 v h) (hints_cons _ _ _ (der_32970 v h) (hints_cons _ _ _ (der_32971 v h) (hints_cons _ _ _ (der_32972 v h) (hints_cons _ _ _ (der_32973 v h) (hints_cons _ _ _ (der_32974 v h) (hints_cons _ _ _ (der_32975 v h) (hints_cons _ _ _ (der_32976 v h) (hints_cons _ _ _ (der_32977 v h) (hints_cons _ _ _ (der_32978 v h) (hints_cons _ _ _ (der_32979 v h) (hints_cons _ _ _ (der_32980 v h) (hints_cons _ _ _ (der_32981 v h) (hints_cons _ _ _ (der_32982 v h) (hints_cons _ _ _ (der_32983 v h) (hints_cons _ _ _ (der_32984 v h) (hints_cons _ _ _ (der_32985 v h) (hints_cons _ _ _ (der_32986 v h) (hints_cons _ _ _ (der_32987 v h) (hints_cons _ _ _ (der_32988 v h) (hints_cons _ _ _ (der_32990 v h) (hints_cons _ _ _ (der_32991 v h) (hints_cons _ _ _ (der_32993 v h) (hints_cons _ _ _ (der_32994 v h) (hints_cons _ _ _ (der_32995 v h) (hints_cons _ _ _ (der_32996 v h) (hints_cons _ _ _ (der_32997 v h) (hints_cons _ _ _ (der_32998 v h) (hints_cons _ _ _ (der_32999 v h) (hints_cons _ _ _ (der_33000 v h) (hints_cons _ _ _ (der_33001 v h) (hints_cons _ _ _ (der_33003 v h) (hints_cons _ _ _ (der_33004 v h) (hints_cons _ _ _ (der_33005 v h) (hints_cons _ _ _ (der_33006 v h) (hints_cons _ _ _ (der_33007 v h) (hints_cons _ _ _ (der_33008 v h) (hints_cons _ _ _ (der_33009 v h) (hints_cons _ _ _ (der_33010 v h) (hints_cons _ _ _ (der_33011 v h) (hints_cons _ _ _ (der_33012 v h) (hints_cons _ _ _ (der_33013 v h) (hints_cons _ _ _ (der_33014 v h) (hints_cons _ _ _ (der_33015 v h) (hints_cons _ _ _ (der_33016 v h) (hints_cons _ _ _ (der_33017 v h) (hints_cons _ _ _ (der_33018 v h) (hints_cons _ _ _ (der_33019 v h) (hints_cons _ _ _ (der_33020 v h) (hints_cons _ _ _ (der_33021 v h) (hints_cons _ _ _ (der_33022 v h) (hints_cons _ _ _ (der_33023 v h) (hints_cons _ _ _ (der_33024 v h) (hints_cons _ _ _ (der_33025 v h) (hints_cons _ _ _ (der_33026 v h) (hints_cons _ _ _ (der_33027 v h) (hints_cons _ _ _ (der_33028 v h) (hints_cons _ _ _ (der_33029 v h) (hints_cons _ _ _ (der_33030 v h) (hints_cons _ _ _ (der_33031 v h) (hints_cons _ _ _ (der_33033 v h) (hints_cons _ _ _ (der_33034 v h) (hints_cons _ _ _ (der_33035 v h) (hints_cons _ _ _ (der_33036 v h) (hints_cons _ _ _ (der_33037 v h) (hints_cons _ _ _ (der_33038 v h) (hints_cons _ _ _ (der_33040 v h) (hints_cons _ _ _ (der_33041 v h) (hints_cons _ _ _ (der_33042 v h) (hints_cons _ _ _ (der_33044 v h) (hints_cons _ _ _ (der_33045 v h) (hints_cons _ _ _ (der_33046 v h) (hints_cons _ _ _ (der_33047 v h) (hints_cons _ _ _ (der_33048 v h) (hints_cons _ _ _ (der_33049 v h) (hints_cons _ _ _ (der_33050 v h) (hints_cons _ _ _ (der_33051 v h) (hints_cons _ _ _ (der_33052 v h) (hints_cons _ _ _ (der_33053 v h) (hints_cons _ _ _ (der_33054 v h) (hints_cons _ _ _ (der_33056 v h) (hints_cons _ _ _ (der_33057 v h) (hints_cons _ _ _ (der_33060 v h) (hints_cons _ _ _ (der_33061 v h) (hints_cons _ _ _ (der_33063 v h) (hints_cons _ _ _ (der_33064 v h) (hints_cons _ _ _ (der_33066 v h) (hints_cons _ _ _ (der_33067 v h) (hints_cons _ _ _ (der_33068 v h) (hints_cons _ _ _ (der_33069 v h) (hints_cons _ _ _ (der_33070 v h) (hints_cons _ _ _ (der_33071 v h) (hints_cons _ _ _ (der_33072 v h) (hints_cons _ _ _ (der_33073 v h) (hints_cons _ _ _ (der_33074 v h) (hints_cons _ _ _ (der_33075 v h) (hints_cons _ _ _ (der_33076 v h) (hints_cons _ _ _ (der_33077 v h) (hints_cons _ _ _ (der_33079 v h) (hints_cons _ _ _ (der_33080 v h) (hints_cons _ _ _ (der_33081 v h) (hints_cons _ _ _ (der_33082 v h) (hints_cons _ _ _ (der_33083 v h) (hints_cons _ _ _ (der_33084 v h) (hints_cons _ _ _ (der_33085 v h) (hints_cons _ _ _ (der_33086 v h) (hints_cons _ _ _ (der_33087 v h) (hints_cons _ _ _ (der_33088 v h) (hints_cons _ _ _ (der_33089 v h) (hints_cons _ _ _ (der_33090 v h) (hints_cons _ _ _ (der_33091 v h) (hints_cons _ _ _ (der_33092 v h) (hints_cons _ _ _ (der_33093 v h) (hints_cons _ _ _ (der_33094 v h) (hints_cons _ _ _ (der_33095 v h) (hints_cons _ _ _ (der_33096 v h) (hints_cons _ _ _ (der_33097 v h) (hints_cons _ _ _ (der_33098 v h) (hints_cons _ _ _ (der_33099 v h) (hints_cons _ _ _ (der_33100 v h) (hints_cons _ _ _ (der_33101 v h) (hints_cons _ _ _ (der_33102 v h) (hints_cons _ _ _ (der_33103 v h) (hints_cons _ _ _ (der_33104 v h) (hints_cons _ _ _ (der_33105 v h) (hints_cons _ _ _ (der_33106 v h) (hints_cons _ _ _ (der_33107 v h) (hints_cons _ _ _ (der_33108 v h) (hints_cons _ _ _ (der_33109 v h) (hints_cons _ _ _ (der_33110 v h) (hints_cons _ _ _ (der_33111 v h) (hints_cons _ _ _ (der_33112 v h) (hints_cons _ _ _ (der_33113 v h) (hints_cons _ _ _ (der_33114 v h) (hints_cons _ _ _ (der_33116 v h) (hints_cons _ _ _ (der_33117 v h) (hints_cons _ _ _ (der_33119 v h) (hints_cons _ _ _ (der_33120 v h) (hints_cons _ _ _ (der_33121 v h) (hints_cons _ _ _ (der_33122 v h) (hints_cons _ _ _ (der_33123 v h) (hints_cons _ _ _ (der_33124 v h) (hints_cons _ _ _ (der_33125 v h) (hints_cons _ _ _ (der_33126 v h) (hints_cons _ _ _ (der_33127 v h) (hints_cons _ _ _ (der_33128 v h) (hints_cons _ _ _ (der_33129 v h) (hints_cons _ _ _ (der_33130 v h) (hints_cons _ _ _ (der_33131 v h) (hints_cons _ _ _ (der_33132 v h) (hints_cons _ _ _ (der_33133 v h) (hints_cons _ _ _ (der_33134 v h) (hints_cons _ _ _ (der_33135 v h) (hints_cons _ _ _ (der_33136 v h) (hints_cons _ _ _ (der_33137 v h) (hints_cons _ _ _ (der_33138 v h) (hints_cons _ _ _ (der_33139 v h) (hints_cons _ _ _ (der_33140 v h) (hints_cons _ _ _ (der_33141 v h) (hints_cons _ _ _ (der_33142 v h) (hints_cons _ _ _ (der_33143 v h) (hints_cons _ _ _ (der_33144 v h) (hints_cons _ _ _ (der_33146 v h) (hints_cons _ _ _ (der_33147 v h) (hints_cons _ _ _ (der_33148 v h) (hints_cons _ _ _ (der_33149 v h) (hints_cons _ _ _ (der_33150 v h) (hints_cons _ _ _ (der_33151 v h) (hints_cons _ _ _ (der_33152 v h) (hints_cons _ _ _ (der_33153 v h) (hints_cons _ _ _ (der_33154 v h) (hints_cons _ _ _ (der_33156 v h) (hints_cons _ _ _ (der_33157 v h) (hints_cons _ _ _ (der_33158 v h) (hints_cons _ _ _ (der_33159 v h) (hints_cons _ _ _ (der_33160 v h) (hints_cons _ _ _ (der_33161 v h) (hints_cons _ _ _ (der_33162 v h) (hints_cons _ _ _ (der_33163 v h) (hints_cons _ _ _ (der_33164 v h) (hints_cons _ _ _ (der_33165 v h) (hints_cons _ _ _ (der_33166 v h) (hints_cons _ _ _ (der_33167 v h) (hints_cons _ _ _ (der_33169 v h) (hints_cons _ _ _ (der_33170 v h) (hints_cons _ _ _ (der_33171 v h) (hints_cons _ _ _ (der_33172 v h) (hints_cons _ _ _ (der_33173 v h) (hints_cons _ _ _ (der_33174 v h) (hints_cons _ _ _ (der_33175 v h) (hints_cons _ _ _ (der_33176 v h) (hints_cons _ _ _ (der_33179 v h) (hints_cons _ _ _ (der_33180 v h) (hints_cons _ _ _ (der_33181 v h) (hints_cons _ _ _ (der_33182 v h) (hints_cons _ _ _ (der_33183 v h) (hints_cons _ _ _ (der_33184 v h) (hints_cons _ _ _ (der_33185 v h) (hints_cons _ _ _ (der_33186 v h) (hints_cons _ _ _ (der_33187 v h) (hints_cons _ _ _ (der_33188 v h) (hints_cons _ _ _ (der_33189 v h) (hints_cons _ _ _ (der_33190 v h) (hints_cons _ _ _ (der_33191 v h) (hints_cons _ _ _ (der_33193 v h) (hints_cons _ _ _ (der_33194 v h) (hints_cons _ _ _ (der_33195 v h) (hints_cons _ _ _ (der_33196 v h) (hints_cons _ _ _ (der_33197 v h) (hints_cons _ _ _ (der_33198 v h) (hints_cons _ _ _ (der_33199 v h) (hints_cons _ _ _ (der_33200 v h) (hints_cons _ _ _ (der_33201 v h) (hints_cons _ _ _ (der_33203 v h) (hints_cons _ _ _ (der_33204 v h) (hints_cons _ _ _ (der_33205 v h) (hints_cons _ _ _ (der_33206 v h) (hints_cons _ _ _ (der_33207 v h) (hints_cons _ _ _ (der_33208 v h) (hints_cons _ _ _ (der_33209 v h) (hints_cons _ _ _ (der_33210 v h) (hints_cons _ _ _ (der_33211 v h) (hints_cons _ _ _ (der_33212 v h) (hints_cons _ _ _ (der_33213 v h) (hints_cons _ _ _ (der_33214 v h) (hints_cons _ _ _ (der_33215 v h) (hints_cons _ _ _ (der_33216 v h) (hints_cons _ _ _ (der_33217 v h) (hints_cons _ _ _ (der_33218 v h) (hints_cons _ _ _ (der_33219 v h) (hints_cons _ _ _ (der_33220 v h) (hints_cons _ _ _ (der_33221 v h) (hints_cons _ _ _ (der_33223 v h) (hints_cons _ _ _ (der_33224 v h) (hints_cons _ _ _ (der_33225 v h) (hints_cons _ _ _ (der_33227 v h) (hints_cons _ _ _ (der_33230 v h) (hints_cons _ _ _ (der_33233 v h) (hints_cons _ _ _ (der_33234 v h) (hints_cons _ _ _ (der_33236 v h) (hints_cons _ _ _ (der_33239 v h) (hints_cons _ _ _ (der_33240 v h) (hints_cons _ _ _ (der_33241 v h) (hints_cons _ _ _ (der_33242 v h) (hints_cons _ _ _ (der_33243 v h) (hints_cons _ _ _ (der_33244 v h) (hints_cons _ _ _ (der_33245 v h) (hints_cons _ _ _ (der_33246 v h) (hints_cons _ _ _ (der_33247 v h) (hints_cons _ _ _ (der_33250 v h) (hints_cons _ _ _ (der_33251 v h) (hints_cons _ _ _ (der_33252 v h) (hints_cons _ _ _ (der_33253 v h) (hints_cons _ _ _ (der_33254 v h) (hints_cons _ _ _ (der_33255 v h) (hints_cons _ _ _ (der_33257 v h) (hints_cons _ _ _ (der_33258 v h) (hints_cons _ _ _ (der_33259 v h) (hints_cons _ _ _ (der_33260 v h) (hints_cons _ _ _ (der_33261 v h) (hints_cons _ _ _ (der_33262 v h) (hints_cons _ _ _ (der_33263 v h) (hints_cons _ _ _ (der_33265 v h) (hints_cons _ _ _ (der_33266 v h) (hints_cons _ _ _ (der_33267 v h) (hints_cons _ _ _ (der_33268 v h) (hints_cons _ _ _ (der_33269 v h) (hints_cons _ _ _ (der_33270 v h) (hints_cons _ _ _ (der_33271 v h) (hints_cons _ _ _ (der_33272 v h) (hints_cons _ _ _ (der_33273 v h) (hints_cons _ _ _ (der_33274 v h) (hints_cons _ _ _ (der_33275 v h) (hints_cons _ _ _ (der_33276 v h) (hints_cons _ _ _ (der_33277 v h) (hints_cons _ _ _ (der_33278 v h) (hints_cons _ _ _ (der_33279 v h) (hints_cons _ _ _ (der_33280 v h) (hints_cons _ _ _ (der_33281 v h) (hints_cons _ _ _ (der_33282 v h) (hints_cons _ _ _ (der_33283 v h) (hints_cons _ _ _ (der_33284 v h) (hints_cons _ _ _ (der_33285 v h) (hints_cons _ _ _ (der_33286 v h) (hints_cons _ _ _ (der_33287 v h) (hints_cons _ _ _ (der_33288 v h) (hints_cons _ _ _ (der_33289 v h) (hints_cons _ _ _ (der_33290 v h) (hints_cons _ _ _ (der_33291 v h) (hints_cons _ _ _ (der_33292 v h) (hints_cons _ _ _ (der_33293 v h) (hints_cons _ _ _ (der_33294 v h) (hints_cons _ _ _ (der_33296 v h) (hints_cons _ _ _ (der_33297 v h) (hints_cons _ _ _ (der_33298 v h) (hints_cons _ _ _ (der_33299 v h) (hints_cons _ _ _ (der_33300 v h) (hints_cons _ _ _ (der_33301 v h) (hints_cons _ _ _ (der_33302 v h) (hints_cons _ _ _ (der_33303 v h) (hints_cons _ _ _ (der_33304 v h) (hints_cons _ _ _ (der_33305 v h) (hints_cons _ _ _ (der_33306 v h) (hints_cons _ _ _ (der_33307 v h) (hints_cons _ _ _ (der_33308 v h) (hints_cons _ _ _ (der_33309 v h) (hints_cons _ _ _ (der_33310 v h) (hints_cons _ _ _ (der_33311 v h) (hints_cons _ _ _ (der_33312 v h) (hints_cons _ _ _ (der_33313 v h) (hints_cons _ _ _ (der_33314 v h) (hints_cons _ _ _ (der_33315 v h) (hints_cons _ _ _ (der_33316 v h) (hints_cons _ _ _ (der_33318 v h) (hints_cons _ _ _ (der_33319 v h) (hints_cons _ _ _ (der_33320 v h) (hints_cons _ _ _ (der_33321 v h) (hints_cons _ _ _ (der_33322 v h) (hints_cons _ _ _ (der_33323 v h) (hints_cons _ _ _ (der_33324 v h) (hints_cons _ _ _ (der_33325 v h) (hints_cons _ _ _ (der_33326 v h) (hints_cons _ _ _ (der_33327 v h) (hints_cons _ _ _ (der_33328 v h) (hints_cons _ _ _ (der_33329 v h) (hints_cons _ _ _ (der_33330 v h) (hints_cons _ _ _ (der_33332 v h) (hints_cons _ _ _ (der_33334 v h) (hints_cons _ _ _ (der_33335 v h) (hints_cons _ _ _ (der_33336 v h) (hints_cons _ _ _ (der_33338 v h) (hints_cons _ _ _ (der_33339 v h) (hints_cons _ _ _ (der_33340 v h) (hints_cons _ _ _ (der_33342 v h) (hints_cons _ _ _ (der_33343 v h) (hints_cons _ _ _ (der_33344 v h) (hints_cons _ _ _ (der_33345 v h) (hints_cons _ _ _ (der_33346 v h) (hints_cons _ _ _ (der_33347 v h) (hints_cons _ _ _ (der_33349 v h) (hints_cons _ _ _ (der_33351 v h) (hints_cons _ _ _ (der_33352 v h) (hints_cons _ _ _ (der_33353 v h) (hints_cons _ _ _ (der_33354 v h) (hints_cons _ _ _ (der_33355 v h) (hints_cons _ _ _ (der_33357 v h) (hints_cons _ _ _ (der_33358 v h) (hints_cons _ _ _ (der_33359 v h) (hints_cons _ _ _ (der_33360 v h) (hints_cons _ _ _ (der_33361 v h) (hints_cons _ _ _ (der_33362 v h) (hints_cons _ _ _ (der_33363 v h) (hints_cons _ _ _ (der_33364 v h) (hints_cons _ _ _ (der_33366 v h) (hints_cons _ _ _ (der_33368 v h) (hints_cons _ _ _ (der_33369 v h) (hints_cons _ _ _ (der_33370 v h) (hints_cons _ _ _ (der_33371 v h) (hints_cons _ _ _ (der_33372 v h) (hints_cons _ _ _ (der_33373 v h) (hints_cons _ _ _ (der_33374 v h) (hints_cons _ _ _ (der_33377 v h) (hints_cons _ _ _ (der_33378 v h) (hints_cons _ _ _ (der_33379 v h) (hints_cons _ _ _ (der_33380 v h) (hints_cons _ _ _ (der_33381 v h) (hints_cons _ _ _ (der_33382 v h) (hints_cons _ _ _ (der_33383 v h) (hints_cons _ _ _ (der_33384 v h) (hints_cons _ _ _ (der_33385 v h) (hints_cons _ _ _ (der_33386 v h) (hints_cons _ _ _ (der_33388 v h) (hints_cons _ _ _ (der_33389 v h) (hints_cons _ _ _ (der_33390 v h) (hints_cons _ _ _ (der_33391 v h) (hints_cons _ _ _ (der_33394 v h) (hints_cons _ _ _ (der_33395 v h) (hints_cons _ _ _ (der_33396 v h) (hints_cons _ _ _ (der_33397 v h) (hints_cons _ _ _ (der_33398 v h) (hints_cons _ _ _ (der_33402 v h) (hints_cons _ _ _ (der_33403 v h) (hints_cons _ _ _ (der_33404 v h) (hints_cons _ _ _ (der_33406 v h) (hints_cons _ _ _ (der_33407 v h) (hints_cons _ _ _ (der_33408 v h) (hints_cons _ _ _ (der_33409 v h) (hints_cons _ _ _ (der_33410 v h) (hints_cons _ _ _ (der_33411 v h) (hints_cons _ _ _ (der_33412 v h) (hints_cons _ _ _ (der_33414 v h) (hints_cons _ _ _ (der_33415 v h) (hints_cons _ _ _ (der_33416 v h) (hints_cons _ _ _ (der_33417 v h) (hints_cons _ _ _ (der_33418 v h) (hints_cons _ _ _ (der_33419 v h) (hints_cons _ _ _ (der_33420 v h) (hints_cons _ _ _ (der_33421 v h) (hints_cons _ _ _ (der_33422 v h) (hints_cons _ _ _ (der_33423 v h) (hints_cons _ _ _ (der_33425 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix020 := prefix019 ++ chunk020
theorem prefix_sound020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix020, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound019 v h c hc
  · exact chunk_sound020 v h c hc
end Percolation.NReplay
