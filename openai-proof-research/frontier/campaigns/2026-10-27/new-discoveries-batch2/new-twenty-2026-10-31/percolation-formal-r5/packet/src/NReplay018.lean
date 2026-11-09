import NReplay017
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_31736 : CNF.NClause := [(38,false),(52,false),(41,true),(59,true),(104,true)]
theorem der_31736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31736 :=
  CNF.rup_sound cl_31736 [cl_25984,cl_31733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25984 v h) (hints_cons _ _ _ (der_31733 v h) (by intro d hd; cases hd)))
def cl_31737 : CNF.NClause := [(41,false),(38,false),(49,false),(59,true),(104,true)]
theorem der_31737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31737 :=
  CNF.rup_sound cl_31737 [cl_25985,cl_31731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25985 v h) (hints_cons _ _ _ (der_31731 v h) (by intro d hd; cases hd)))
def cl_31738 : CNF.NClause := [(41,false),(49,false),(38,true),(35,true),(104,true)]
theorem der_31738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31738 :=
  CNF.rup_sound cl_31738 [cl_25986,cl_31732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25986 v h) (hints_cons _ _ _ (der_31732 v h) (by intro d hd; cases hd)))
def cl_31739 : CNF.NClause := [(38,false),(49,false),(41,true),(35,true),(104,true)]
theorem der_31739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31739 :=
  CNF.rup_sound cl_31739 [cl_25987,cl_31733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25987 v h) (hints_cons _ _ _ (der_31733 v h) (by intro d hd; cases hd)))
def cl_31740 : CNF.NClause := [(41,false),(38,false),(52,true),(59,true),(104,true)]
theorem der_31740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31740 :=
  CNF.rup_sound cl_31740 [cl_25988,cl_31737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25988 v h) (hints_cons _ _ _ (der_31737 v h) (by intro d hd; cases hd)))
def cl_31741 : CNF.NClause := [(58,false),(44,false),(53,false),(37,true),(109,true)]
theorem der_31741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31741 :=
  CNF.rup_sound cl_31741 [cl_25993,cl_25989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25993 v h) (hints_cons _ _ _ (der_25989 v h) (by intro d hd; cases hd)))
def cl_31743 : CNF.NClause := [(58,false),(37,true),(53,false),(35,true),(109,true)]
theorem der_31743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31743 :=
  CNF.rup_sound cl_31743 [cl_25995,cl_31741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25995 v h) (hints_cons _ _ _ (der_31741 v h) (by intro d hd; cases hd)))
def cl_31744 : CNF.NClause := [(58,false),(46,false),(37,true),(44,true),(109,true)]
theorem der_31744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31744 :=
  CNF.rup_sound cl_31744 [cl_25999,cl_24793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25999 v h) (hints_cons _ _ _ (der_24793 v h) (by intro d hd; cases hd)))
def cl_31745 : CNF.NClause := [(58,false),(37,false),(44,false),(53,true),(109,true)]
theorem der_31745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31745 :=
  CNF.rup_sound cl_31745 [cl_26000,cl_25996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26000 v h) (hints_cons _ _ _ (der_25996 v h) (by intro d hd; cases hd)))
def cl_31746 : CNF.NClause := [(58,false),(44,false),(37,true),(46,true),(109,true)]
theorem der_31746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31746 :=
  CNF.rup_sound cl_31746 [cl_26001,cl_31741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26001 v h) (hints_cons _ _ _ (der_31741 v h) (by intro d hd; cases hd)))
def cl_31747 : CNF.NClause := [(58,false),(37,false),(44,true),(35,true),(109,true)]
theorem der_31747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31747 :=
  CNF.rup_sound cl_31747 [cl_26002,cl_25998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26002 v h) (hints_cons _ _ _ (der_25998 v h) (by intro d hd; cases hd)))
def cl_31748 : CNF.NClause := [(46,false),(44,false),(53,false),(37,true),(109,true)]
theorem der_31748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31748 :=
  CNF.rup_sound cl_31748 [cl_26004,cl_24796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26004 v h) (hints_cons _ _ _ (der_24796 v h) (by intro d hd; cases hd)))
def cl_31749 : CNF.NClause := [(37,false),(46,false),(53,false),(58,true),(109,true)]
theorem der_31749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31749 :=
  CNF.rup_sound cl_31749 [cl_26005,cl_26003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26005 v h) (hints_cons _ _ _ (der_26003 v h) (by intro d hd; cases hd)))
def cl_31750 : CNF.NClause := [(46,false),(44,true),(37,true),(53,false),(109,true)]
theorem der_31750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31750 :=
  CNF.rup_sound cl_31750 [cl_26006,cl_30785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26006 v h) (hints_cons _ _ _ (der_30785 v h) (by intro d hd; cases hd)))
def cl_31751 : CNF.NClause := [(37,false),(44,false),(53,false),(58,true),(109,true)]
theorem der_31751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31751 :=
  CNF.rup_sound cl_31751 [cl_26007,cl_26003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26007 v h) (hints_cons _ _ _ (der_26003 v h) (by intro d hd; cases hd)))
def cl_31752 : CNF.NClause := [(44,false),(37,true),(53,false),(35,true),(109,true)]
theorem der_31752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31752 :=
  CNF.rup_sound cl_31752 [cl_26008,cl_31748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26008 v h) (hints_cons _ _ _ (der_31748 v h) (by intro d hd; cases hd)))
def cl_31753 : CNF.NClause := [(37,false),(44,true),(53,false),(46,true),(109,true)]
theorem der_31753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31753 :=
  CNF.rup_sound cl_31753 [cl_26009,cl_30124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26009 v h) (hints_cons _ _ _ (der_30124 v h) (by intro d hd; cases hd)))
def cl_31754 : CNF.NClause := [(37,false),(46,false),(44,false),(58,true),(109,true)]
theorem der_31754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31754 :=
  CNF.rup_sound cl_31754 [cl_26010,cl_26003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26010 v h) (hints_cons _ _ _ (der_26003 v h) (by intro d hd; cases hd)))
def cl_31755 : CNF.NClause := [(46,false),(44,false),(37,true),(35,true),(109,true)]
theorem der_31755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31755 :=
  CNF.rup_sound cl_31755 [cl_26011,cl_31748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26011 v h) (hints_cons _ _ _ (der_31748 v h) (by intro d hd; cases hd)))
def cl_31756 : CNF.NClause := [(37,false),(44,false),(53,true),(58,true),(109,true)]
theorem der_31756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31756 :=
  CNF.rup_sound cl_31756 [cl_26013,cl_31754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26013 v h) (hints_cons _ _ _ (der_31754 v h) (by intro d hd; cases hd)))
def cl_31757 : CNF.NClause := [(57,false),(48,false),(42,false),(54,false),(114,true)]
theorem der_31757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31757 :=
  CNF.rup_sound cl_31757 [cl_26015,cl_26014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26015 v h) (hints_cons _ _ _ (der_26014 v h) (by intro d hd; cases hd)))
def cl_31758 : CNF.NClause := [(57,false),(48,false),(54,false),(36,false),(114,true)]
theorem der_31758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31758 :=
  CNF.rup_sound cl_31758 [cl_26016,cl_26014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26016 v h) (hints_cons _ _ _ (der_26014 v h) (by intro d hd; cases hd)))
def cl_31759 : CNF.NClause := [(57,false),(48,false),(54,false),(36,true),(114,true)]
theorem der_31759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31759 :=
  CNF.rup_sound cl_31759 [cl_26017,cl_31757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26017 v h) (hints_cons _ _ _ (der_31757 v h) (by intro d hd; cases hd)))
def cl_31761 : CNF.NClause := [(57,false),(42,false),(54,false),(36,true),(114,true)]
theorem der_31761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31761 :=
  CNF.rup_sound cl_31761 [cl_26019,cl_31759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26019 v h) (hints_cons _ _ _ (der_31759 v h) (by intro d hd; cases hd)))
def cl_31762 : CNF.NClause := [(57,false),(54,false),(36,false),(42,true),(114,true)]
theorem der_31762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31762 :=
  CNF.rup_sound cl_31762 [cl_26020,cl_31758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26020 v h) (hints_cons _ _ _ (der_31758 v h) (by intro d hd; cases hd)))
def cl_31763 : CNF.NClause := [(57,false),(54,false),(42,true),(48,true),(114,true)]
theorem der_31763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31763 :=
  CNF.rup_sound cl_31763 [cl_26021,cl_31762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26021 v h) (hints_cons _ _ _ (der_31762 v h) (by intro d hd; cases hd)))
def cl_31764 : CNF.NClause := [(57,false),(48,false),(42,false),(36,false),(114,true)]
theorem der_31764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31764 :=
  CNF.rup_sound cl_31764 [cl_26022,cl_30979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26022 v h) (hints_cons _ _ _ (der_30979 v h) (by intro d hd; cases hd)))
def cl_31765 : CNF.NClause := [(57,false),(48,false),(42,false),(54,true),(114,true)]
theorem der_31765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31765 :=
  CNF.rup_sound cl_31765 [cl_26023,cl_31764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26023 v h) (hints_cons _ _ _ (der_31764 v h) (by intro d hd; cases hd)))
def cl_31766 : CNF.NClause := [(57,false),(48,false),(36,false),(42,true),(114,true)]
theorem der_31766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31766 :=
  CNF.rup_sound cl_31766 [cl_26024,cl_31197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26024 v h) (hints_cons _ _ _ (der_31197 v h) (by intro d hd; cases hd)))
def cl_31767 : CNF.NClause := [(57,false),(48,false),(36,true),(35,true),(114,true)]
theorem der_31767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31767 :=
  CNF.rup_sound cl_31767 [cl_26025,cl_31759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26025 v h) (hints_cons _ _ _ (der_31759 v h) (by intro d hd; cases hd)))
def cl_31768 : CNF.NClause := [(57,false),(42,false),(36,false),(54,true),(114,true)]
theorem der_31768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31768 :=
  CNF.rup_sound cl_31768 [cl_26026,cl_31764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26026 v h) (hints_cons _ _ _ (der_31764 v h) (by intro d hd; cases hd)))
def cl_31769 : CNF.NClause := [(57,false),(42,false),(48,true),(36,true),(114,true)]
theorem der_31769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31769 :=
  CNF.rup_sound cl_31769 [cl_26027,cl_31761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26027 v h) (hints_cons _ _ _ (der_31761 v h) (by intro d hd; cases hd)))
def cl_31770 : CNF.NClause := [(57,false),(36,false),(42,true),(48,true),(114,true)]
theorem der_31770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31770 :=
  CNF.rup_sound cl_31770 [cl_26028,cl_31762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26028 v h) (hints_cons _ _ _ (der_31762 v h) (by intro d hd; cases hd)))
def cl_31771 : CNF.NClause := [(48,false),(42,false),(54,false),(36,true),(114,true)]
theorem der_31771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31771 :=
  CNF.rup_sound cl_31771 [cl_26030,cl_24903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26030 v h) (hints_cons _ _ _ (der_24903 v h) (by intro d hd; cases hd)))
def cl_31772 : CNF.NClause := [(48,false),(54,false),(36,false),(42,true),(114,true)]
theorem der_31772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31772 :=
  CNF.rup_sound cl_31772 [cl_26031,cl_31198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26031 v h) (hints_cons _ _ _ (der_31198 v h) (by intro d hd; cases hd)))
def cl_31773 : CNF.NClause := [(48,false),(54,false),(36,true),(35,true),(114,true)]
theorem der_31773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31773 :=
  CNF.rup_sound cl_31773 [cl_26032,cl_31771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26032 v h) (hints_cons _ _ _ (der_31771 v h) (by intro d hd; cases hd)))
def cl_31774 : CNF.NClause := [(42,false),(54,false),(36,false),(35,true),(114,true)]
theorem der_31774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31774 :=
  CNF.rup_sound cl_31774 [cl_26033,cl_26029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26033 v h) (hints_cons _ _ _ (der_26029 v h) (by intro d hd; cases hd)))
def cl_31775 : CNF.NClause := [(42,false),(54,false),(36,true),(57,true),(114,true)]
theorem der_31775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31775 :=
  CNF.rup_sound cl_31775 [cl_26034,cl_30860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26034 v h) (hints_cons _ _ _ (der_30860 v h) (by intro d hd; cases hd)))
def cl_31776 : CNF.NClause := [(54,false),(36,false),(57,true),(35,true),(114,true)]
theorem der_31776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31776 :=
  CNF.rup_sound cl_31776 [cl_26035,cl_31774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26035 v h) (hints_cons _ _ _ (der_31774 v h) (by intro d hd; cases hd)))
def cl_31777 : CNF.NClause := [(48,false),(42,false),(36,false),(35,true),(114,true)]
theorem der_31777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31777 :=
  CNF.rup_sound cl_31777 [cl_26036,cl_31774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26036 v h) (hints_cons _ _ _ (der_31774 v h) (by intro d hd; cases hd)))
def cl_31778 : CNF.NClause := [(48,false),(42,false),(54,true),(57,true),(114,true)]
theorem der_31778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31778 :=
  CNF.rup_sound cl_31778 [cl_26037,cl_30980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26037 v h) (hints_cons _ _ _ (der_30980 v h) (by intro d hd; cases hd)))
def cl_31779 : CNF.NClause := [(48,false),(36,false),(42,true),(35,true),(114,true)]
theorem der_31779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31779 :=
  CNF.rup_sound cl_31779 [cl_26038,cl_31766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26038 v h) (hints_cons _ _ _ (der_31766 v h) (by intro d hd; cases hd)))
def cl_31780 : CNF.NClause := [(42,false),(36,false),(48,true),(54,true),(114,true)]
theorem der_31780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31780 :=
  CNF.rup_sound cl_31780 [cl_26039,cl_31768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26039 v h) (hints_cons _ _ _ (der_31768 v h) (by intro d hd; cases hd)))
def cl_31781 : CNF.NClause := [(59,false),(61,false),(60,false),(58,false),(93,true)]
theorem der_31781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31781 :=
  CNF.rup_sound cl_31781 [cl_26042,cl_31367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26042 v h) (hints_cons _ _ _ (der_31367 v h) (by intro d hd; cases hd)))
def cl_31782 : CNF.NClause := [(59,false),(61,false),(60,false),(58,true),(93,true)]
theorem der_31782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31782 :=
  CNF.rup_sound cl_31782 [cl_26043,cl_31357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26043 v h) (hints_cons _ _ _ (der_31357 v h) (by intro d hd; cases hd)))
def cl_31783 : CNF.NClause := [(61,false),(60,false),(58,false),(56,true),(93,true)]
theorem der_31783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31783 :=
  CNF.rup_sound cl_31783 [cl_26044,cl_31555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26044 v h) (hints_cons _ _ _ (der_31555 v h) (by intro d hd; cases hd)))
def cl_31784 : CNF.NClause := [(61,false),(60,false),(58,true),(59,true),(93,true)]
theorem der_31784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31784 :=
  CNF.rup_sound cl_31784 [cl_26045,cl_31357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26045 v h) (hints_cons _ _ _ (der_31357 v h) (by intro d hd; cases hd)))
def cl_31785 : CNF.NClause := [(59,false),(61,false),(58,false),(56,true),(93,true)]
theorem der_31785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31785 :=
  CNF.rup_sound cl_31785 [cl_26046,cl_31783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26046 v h) (hints_cons _ _ _ (der_31783 v h) (by intro d hd; cases hd)))
def cl_31788 : CNF.NClause := [(59,false),(60,false),(58,false),(61,true),(93,true)]
theorem der_31788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31788 :=
  CNF.rup_sound cl_31788 [cl_26049,cl_31367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26049 v h) (hints_cons _ _ _ (der_31367 v h) (by intro d hd; cases hd)))
def cl_31789 : CNF.NClause := [(59,false),(60,false),(61,true),(57,true),(93,true)]
theorem der_31789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31789 :=
  CNF.rup_sound cl_31789 [cl_26050,cl_31788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26050 v h) (hints_cons _ _ _ (der_31788 v h) (by intro d hd; cases hd)))
def cl_31790 : CNF.NClause := [(60,false),(58,false),(59,true),(57,true),(93,true)]
theorem der_31790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31790 :=
  CNF.rup_sound cl_31790 [cl_26051,cl_31371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26051 v h) (hints_cons _ _ _ (der_31371 v h) (by intro d hd; cases hd)))
def cl_31791 : CNF.NClause := [(59,false),(58,false),(56,true),(60,true),(93,true)]
theorem der_31791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31791 :=
  CNF.rup_sound cl_31791 [cl_26052,cl_31785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26052 v h) (hints_cons _ _ _ (der_31785 v h) (by intro d hd; cases hd)))
def cl_31792 : CNF.NClause := [(35,false),(48,false),(42,false),(54,false),(114,true)]
theorem der_31792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31792 :=
  CNF.rup_sound cl_31792 [cl_26053,cl_24903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26053 v h) (hints_cons _ _ _ (der_24903 v h) (by intro d hd; cases hd)))
def cl_31793 : CNF.NClause := [(45,false),(46,false),(33,false),(52,false),(110,true)]
theorem der_31793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31793 :=
  CNF.rup_sound cl_31793 [cl_26054,cl_31525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26054 v h) (hints_cons _ _ _ (der_31525 v h) (by intro d hd; cases hd)))
def cl_31795 : CNF.NClause := [(41,false),(47,false),(40,true),(57,true),(106,true)]
theorem der_31795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31795 :=
  CNF.rup_sound cl_31795 [cl_26056,cl_31279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26056 v h) (hints_cons _ _ _ (der_31279 v h) (by intro d hd; cases hd)))
def cl_31796 : CNF.NClause := [(41,false),(34,false),(40,true),(57,true),(106,true)]
theorem der_31796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31796 :=
  CNF.rup_sound cl_31796 [cl_26057,cl_31795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26057 v h) (hints_cons _ _ _ (der_31795 v h) (by intro d hd; cases hd)))
def cl_31797 : CNF.NClause := [(37,false),(55,false),(49,false),(43,true),(122,true)]
theorem der_31797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31797 :=
  CNF.rup_sound cl_31797 [cl_26058,cl_31094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26058 v h) (hints_cons _ _ _ (der_31094 v h) (by intro d hd; cases hd)))
def cl_31798 : CNF.NClause := [(37,false),(55,false),(43,false),(49,false),(122,true)]
theorem der_31798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31798 :=
  CNF.rup_sound cl_31798 [cl_26059,cl_25211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26059 v h) (hints_cons _ _ _ (der_25211 v h) (by intro d hd; cases hd)))
def cl_31799 : CNF.NClause := [(39,false),(52,false),(45,false),(57,true),(110,true)]
theorem der_31799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31799 :=
  CNF.rup_sound cl_31799 [cl_26060,cl_31528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26060 v h) (hints_cons _ _ _ (der_31528 v h) (by intro d hd; cases hd)))
def cl_31800 : CNF.NClause := [(46,true),(45,false),(33,false),(52,true),(110,true)]
theorem der_31800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31800 :=
  CNF.rup_sound cl_31800 [cl_26061,cl_30732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26061 v h) (hints_cons _ _ _ (der_30732 v h) (by intro d hd; cases hd)))
def cl_31801 : CNF.NClause := [(37,false),(55,false),(43,true),(57,true),(122,true)]
theorem der_31801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31801 :=
  CNF.rup_sound cl_31801 [cl_26062,cl_31098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26062 v h) (hints_cons _ _ _ (der_31098 v h) (by intro d hd; cases hd)))
def cl_31802 : CNF.NClause := [(39,false),(45,false),(33,false),(52,true),(110,true)]
theorem der_31802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31802 :=
  CNF.rup_sound cl_31802 [cl_26063,cl_31800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26063 v h) (hints_cons _ _ _ (der_31800 v h) (by intro d hd; cases hd)))
def cl_31803 : CNF.NClause := [(39,false),(45,true),(46,true),(33,false),(110,true)]
theorem der_31803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31803 :=
  CNF.rup_sound cl_31803 [cl_26064,cl_25801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26064 v h) (hints_cons _ _ _ (der_25801 v h) (by intro d hd; cases hd)))
def cl_31804 : CNF.NClause := [(41,false),(40,false),(34,false),(53,false),(106,true)]
theorem der_31804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31804 :=
  CNF.rup_sound cl_31804 [cl_26065,cl_30099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26065 v h) (hints_cons _ _ _ (der_30099 v h) (by intro d hd; cases hd)))
def cl_31805 : CNF.NClause := [(37,false),(49,true),(43,false),(31,true),(122,true)]
theorem der_31805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31805 :=
  CNF.rup_sound cl_31805 [cl_26066,cl_31091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26066 v h) (hints_cons _ _ _ (der_31091 v h) (by intro d hd; cases hd)))
def cl_31806 : CNF.NClause := [(35,false),(54,false),(36,false),(48,true),(114,true)]
theorem der_31806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31806 :=
  CNF.rup_sound cl_31806 [cl_26067,cl_31199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26067 v h) (hints_cons _ _ _ (der_31199 v h) (by intro d hd; cases hd)))
def cl_31807 : CNF.NClause := [(39,false),(46,false),(33,false),(52,true),(110,true)]
theorem der_31807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31807 :=
  CNF.rup_sound cl_31807 [cl_26068,cl_31802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26068 v h) (hints_cons _ _ _ (der_31802 v h) (by intro d hd; cases hd)))
def cl_31810 : CNF.NClause := [(61,false),(55,false),(52,false),(53,false),(98,true)]
theorem der_31810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31810 :=
  CNF.rup_sound cl_31810 [cl_26073,cl_26069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26073 v h) (hints_cons _ _ _ (der_26069 v h) (by intro d hd; cases hd)))
def cl_31814 : CNF.NClause := [(61,false),(54,false),(52,false),(53,false),(98,true)]
theorem der_31814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31814 :=
  CNF.rup_sound cl_31814 [cl_26077,cl_26069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26077 v h) (hints_cons _ _ _ (der_26069 v h) (by intro d hd; cases hd)))
def cl_31815 : CNF.NClause := [(61,false),(54,false),(53,false),(51,true),(98,true)]
theorem der_31815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31815 :=
  CNF.rup_sound cl_31815 [cl_26078,cl_31814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26078 v h) (hints_cons _ _ _ (der_31814 v h) (by intro d hd; cases hd)))
def cl_31816 : CNF.NClause := [(61,false),(54,false),(52,false),(53,true),(98,true)]
theorem der_31816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31816 :=
  CNF.rup_sound cl_31816 [cl_26079,cl_23730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26079 v h) (hints_cons _ _ _ (der_23730 v h) (by intro d hd; cases hd)))
def cl_31817 : CNF.NClause := [(61,false),(54,false),(53,true),(51,true),(98,true)]
theorem der_31817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31817 :=
  CNF.rup_sound cl_31817 [cl_26080,cl_31816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26080 v h) (hints_cons _ _ _ (der_31816 v h) (by intro d hd; cases hd)))
def cl_31818 : CNF.NClause := [(61,false),(52,false),(53,false),(55,true),(98,true)]
theorem der_31818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31818 :=
  CNF.rup_sound cl_31818 [cl_26081,cl_31814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26081 v h) (hints_cons _ _ _ (der_31814 v h) (by intro d hd; cases hd)))
def cl_31819 : CNF.NClause := [(61,false),(54,true),(53,false),(52,true),(98,true)]
theorem der_31819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31819 :=
  CNF.rup_sound cl_31819 [cl_26082,cl_30095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26082 v h) (hints_cons _ _ _ (der_30095 v h) (by intro d hd; cases hd)))
def cl_31821 : CNF.NClause := [(54,false),(55,false),(52,false),(53,false),(98,true)]
theorem der_31821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31821 :=
  CNF.rup_sound cl_31821 [cl_26084,cl_31814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26084 v h) (hints_cons _ _ _ (der_31814 v h) (by intro d hd; cases hd)))
def cl_31822 : CNF.NClause := [(54,false),(55,false),(53,false),(51,true),(98,true)]
theorem der_31822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31822 :=
  CNF.rup_sound cl_31822 [cl_26085,cl_31821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26085 v h) (hints_cons _ _ _ (der_31821 v h) (by intro d hd; cases hd)))
def cl_31823 : CNF.NClause := [(54,false),(55,false),(52,false),(61,true),(98,true)]
theorem der_31823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31823 :=
  CNF.rup_sound cl_31823 [cl_26086,cl_31821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26086 v h) (hints_cons _ _ _ (der_31821 v h) (by intro d hd; cases hd)))
def cl_31824 : CNF.NClause := [(54,false),(55,false),(53,true),(52,true),(98,true)]
theorem der_31824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31824 :=
  CNF.rup_sound cl_31824 [cl_26087,cl_30076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26087 v h) (hints_cons _ _ _ (der_30076 v h) (by intro d hd; cases hd)))
def cl_31825 : CNF.NClause := [(55,false),(52,false),(53,false),(61,true),(98,true)]
theorem der_31825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31825 :=
  CNF.rup_sound cl_31825 [cl_26088,cl_31821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26088 v h) (hints_cons _ _ _ (der_31821 v h) (by intro d hd; cases hd)))
def cl_31826 : CNF.NClause := [(55,false),(54,true),(53,false),(61,true),(98,true)]
theorem der_31826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31826 :=
  CNF.rup_sound cl_31826 [cl_26089,cl_31825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26089 v h) (hints_cons _ _ _ (der_31825 v h) (by intro d hd; cases hd)))
def cl_31827 : CNF.NClause := [(55,false),(52,false),(53,true),(54,true),(98,true)]
theorem der_31827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31827 :=
  CNF.rup_sound cl_31827 [cl_26090,cl_30062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26090 v h) (hints_cons _ _ _ (der_30062 v h) (by intro d hd; cases hd)))
def cl_31828 : CNF.NClause := [(54,false),(52,false),(53,false),(51,true),(98,true)]
theorem der_31828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31828 :=
  CNF.rup_sound cl_31828 [cl_26091,cl_31822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26091 v h) (hints_cons _ _ _ (der_31822 v h) (by intro d hd; cases hd)))
def cl_31829 : CNF.NClause := [(54,false),(61,true),(53,false),(51,true),(98,true)]
theorem der_31829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31829 :=
  CNF.rup_sound cl_31829 [cl_26092,cl_31828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26092 v h) (hints_cons _ _ _ (der_31828 v h) (by intro d hd; cases hd)))
def cl_31830 : CNF.NClause := [(54,false),(52,false),(53,true),(55,true),(98,true)]
theorem der_31830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31830 :=
  CNF.rup_sound cl_31830 [cl_26093,cl_30061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26093 v h) (hints_cons _ _ _ (der_30061 v h) (by intro d hd; cases hd)))
def cl_31831 : CNF.NClause := [(52,false),(54,true),(53,false),(61,true),(98,true)]
theorem der_31831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31831 :=
  CNF.rup_sound cl_31831 [cl_26094,cl_31825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26094 v h) (hints_cons _ _ _ (der_31825 v h) (by intro d hd; cases hd)))
def cl_31834 : CNF.NClause := [(46,false),(56,false),(41,true),(51,true),(123,true)]
theorem der_31834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31834 :=
  CNF.rup_sound cl_31834 [cl_26097,cl_31113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26097 v h) (hints_cons _ _ _ (der_31113 v h) (by intro d hd; cases hd)))
def cl_31836 : CNF.NClause := [(59,false),(48,false),(45,false),(34,false),(101,true)]
theorem der_31836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31836 :=
  CNF.rup_sound cl_31836 [cl_26099,cl_30790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26099 v h) (hints_cons _ _ _ (der_30790 v h) (by intro d hd; cases hd)))
def cl_31837 : CNF.NClause := [(59,false),(48,false),(37,false),(45,true),(101,true)]
theorem der_31837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31837 :=
  CNF.rup_sound cl_31837 [cl_26100,cl_31244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26100 v h) (hints_cons _ _ _ (der_31244 v h) (by intro d hd; cases hd)))
def cl_31838 : CNF.NClause := [(59,false),(34,false),(45,true),(48,true),(101,true)]
theorem der_31838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31838 :=
  CNF.rup_sound cl_31838 [cl_26101,cl_30791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26101 v h) (hints_cons _ _ _ (der_30791 v h) (by intro d hd; cases hd)))
def cl_31839 : CNF.NClause := [(49,false),(40,false),(33,false),(58,true),(100,true)]
theorem der_31839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31839 :=
  CNF.rup_sound cl_31839 [cl_26103,cl_31214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26103 v h) (hints_cons _ _ _ (der_31214 v h) (by intro d hd; cases hd)))
def cl_31840 : CNF.NClause := [(41,false),(46,false),(36,true),(56,true),(123,true)]
theorem der_31840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31840 :=
  CNF.rup_sound cl_31840 [cl_26104,cl_31127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26104 v h) (hints_cons _ _ _ (der_31127 v h) (by intro d hd; cases hd)))
def cl_31841 : CNF.NClause := [(41,false),(36,false),(46,false),(56,true),(123,true)]
theorem der_31841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31841 :=
  CNF.rup_sound cl_31841 [cl_26105,cl_31124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26105 v h) (hints_cons _ _ _ (der_31124 v h) (by intro d hd; cases hd)))
def cl_31842 : CNF.NClause := [(60,false),(39,false),(43,false),(47,false),(99,true)]
theorem der_31842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31842 :=
  CNF.rup_sound cl_31842 [cl_26106,cl_31714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26106 v h) (hints_cons _ _ _ (der_31714 v h) (by intro d hd; cases hd)))
def cl_31843 : CNF.NClause := [(58,false),(49,false),(40,true),(51,true),(100,true)]
theorem der_31843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31843 :=
  CNF.rup_sound cl_31843 [cl_26108,cl_31480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26108 v h) (hints_cons _ _ _ (der_31480 v h) (by intro d hd; cases hd)))
def cl_31844 : CNF.NClause := [(42,false),(49,false),(40,true),(58,true),(100,true)]
theorem der_31844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31844 :=
  CNF.rup_sound cl_31844 [cl_26109,cl_31490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26109 v h) (hints_cons _ _ _ (der_31490 v h) (by intro d hd; cases hd)))
def cl_31845 : CNF.NClause := [(41,false),(36,false),(56,false),(51,true),(123,true)]
theorem der_31845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31845 :=
  CNF.rup_sound cl_31845 [cl_26110,cl_31114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26110 v h) (hints_cons _ _ _ (der_31114 v h) (by intro d hd; cases hd)))
def cl_31847 : CNF.NClause := [(41,false),(36,false),(46,true),(56,true),(123,true)]
theorem der_31847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31847 :=
  CNF.rup_sound cl_31847 [cl_26112,cl_31128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26112 v h) (hints_cons _ _ _ (der_31128 v h) (by intro d hd; cases hd)))
def cl_31848 : CNF.NClause := [(35,false),(60,false),(43,false),(47,true),(99,true)]
theorem der_31848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31848 :=
  CNF.rup_sound cl_31848 [cl_26113,cl_30747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26113 v h) (hints_cons _ _ _ (der_30747 v h) (by intro d hd; cases hd)))
def cl_31849 : CNF.NClause := [(35,false),(39,false),(43,false),(47,true),(99,true)]
theorem der_31849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31849 :=
  CNF.rup_sound cl_31849 [cl_26114,cl_31848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26114 v h) (hints_cons _ _ _ (der_31848 v h) (by intro d hd; cases hd)))
def cl_31850 : CNF.NClause := [(42,false),(58,false),(40,false),(49,true),(100,true)]
theorem der_31850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31850 :=
  CNF.rup_sound cl_31850 [cl_26115,cl_31481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26115 v h) (hints_cons _ _ _ (der_31481 v h) (by intro d hd; cases hd)))
def cl_31851 : CNF.NClause := [(42,false),(40,false),(49,true),(58,true),(100,true)]
theorem der_31851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31851 :=
  CNF.rup_sound cl_31851 [cl_26116,cl_31492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26116 v h) (hints_cons _ _ _ (der_31492 v h) (by intro d hd; cases hd)))
def cl_31852 : CNF.NClause := [(42,false),(58,false),(33,false),(49,true),(100,true)]
theorem der_31852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31852 :=
  CNF.rup_sound cl_31852 [cl_26117,cl_31850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26117 v h) (hints_cons _ _ _ (der_31850 v h) (by intro d hd; cases hd)))
def cl_31853 : CNF.NClause := [(42,false),(40,true),(33,false),(58,true),(100,true)]
theorem der_31853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31853 :=
  CNF.rup_sound cl_31853 [cl_26118,cl_30966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26118 v h) (hints_cons _ _ _ (der_30966 v h) (by intro d hd; cases hd)))
def cl_31854 : CNF.NClause := [(45,false),(34,false),(59,true),(51,true),(101,true)]
theorem der_31854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31854 :=
  CNF.rup_sound cl_31854 [cl_26119,cl_30797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26119 v h) (hints_cons _ _ _ (der_30797 v h) (by intro d hd; cases hd)))
def cl_31855 : CNF.NClause := [(59,false),(34,false),(48,true),(51,true),(101,true)]
theorem der_31855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31855 :=
  CNF.rup_sound cl_31855 [cl_26120,cl_31838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26120 v h) (hints_cons _ _ _ (der_31838 v h) (by intro d hd; cases hd)))
def cl_31856 : CNF.NClause := [(37,false),(34,false),(45,true),(48,true),(101,true)]
theorem der_31856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31856 :=
  CNF.rup_sound cl_31856 [cl_26121,cl_31838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26121 v h) (hints_cons _ _ _ (der_31838 v h) (by intro d hd; cases hd)))
def cl_31857 : CNF.NClause := [(48,false),(37,false),(45,true),(51,true),(101,true)]
theorem der_31857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31857 :=
  CNF.rup_sound cl_31857 [cl_26122,cl_31837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26122 v h) (hints_cons _ _ _ (der_31837 v h) (by intro d hd; cases hd)))
def cl_31858 : CNF.NClause := [(32,false),(57,false),(44,false),(51,true),(102,true)]
theorem der_31858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31858 :=
  CNF.rup_sound cl_31858 [cl_26123,cl_23908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26123 v h) (hints_cons _ _ _ (der_23908 v h) (by intro d hd; cases hd)))
def cl_31859 : CNF.NClause := [(32,false),(51,false),(44,false),(57,true),(102,true)]
theorem der_31859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31859 :=
  CNF.rup_sound cl_31859 [cl_26124,cl_23912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26124 v h) (hints_cons _ _ _ (der_23912 v h) (by intro d hd; cases hd)))
def cl_31860 : CNF.NClause := [(32,false),(38,false),(44,false),(51,true),(102,true)]
theorem der_31860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31860 :=
  CNF.rup_sound cl_31860 [cl_26125,cl_30125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26125 v h) (hints_cons _ _ _ (der_30125 v h) (by intro d hd; cases hd)))
def cl_31863 : CNF.NClause := [(35,false),(40,false),(55,false),(50,true),(94,true)]
theorem der_31863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31863 :=
  CNF.rup_sound cl_31863 [cl_26128,cl_31396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26128 v h) (hints_cons _ _ _ (der_31396 v h) (by intro d hd; cases hd)))
def cl_31864 : CNF.NClause := [(40,false),(45,false),(56,true),(55,true),(94,true)]
theorem der_31864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31864 :=
  CNF.rup_sound cl_31864 [cl_26129,cl_31695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26129 v h) (hints_cons _ _ _ (der_31695 v h) (by intro d hd; cases hd)))
def cl_31865 : CNF.NClause := [(41,false),(54,false),(60,false),(37,false),(105,true)]
theorem der_31865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31865 :=
  CNF.rup_sound cl_31865 [cl_26130,cl_31509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26130 v h) (hints_cons _ _ _ (der_31509 v h) (by intro d hd; cases hd)))
def cl_31866 : CNF.NClause := [(41,false),(60,false),(37,false),(54,true),(105,true)]
theorem der_31866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31866 :=
  CNF.rup_sound cl_31866 [cl_26131,cl_31498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26131 v h) (hints_cons _ _ _ (der_31498 v h) (by intro d hd; cases hd)))
def cl_31867 : CNF.NClause := [(54,true),(37,false),(33,false),(60,true),(105,true)]
theorem der_31867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31867 :=
  CNF.rup_sound cl_31867 [cl_26132,cl_31650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26132 v h) (hints_cons _ _ _ (der_31650 v h) (by intro d hd; cases hd)))
def cl_31868 : CNF.NClause := [(35,false),(56,false),(40,true),(55,true),(94,true)]
theorem der_31868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31868 :=
  CNF.rup_sound cl_31868 [cl_26133,cl_31393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26133 v h) (hints_cons _ _ _ (der_31393 v h) (by intro d hd; cases hd)))
def cl_31869 : CNF.NClause := [(45,false),(55,false),(40,true),(56,true),(94,true)]
theorem der_31869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31869 :=
  CNF.rup_sound cl_31869 [cl_26134,cl_31690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26134 v h) (hints_cons _ _ _ (der_31690 v h) (by intro d hd; cases hd)))
def cl_31870 : CNF.NClause := [(35,false),(45,false),(40,true),(55,true),(94,true)]
theorem der_31870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31870 :=
  CNF.rup_sound cl_31870 [cl_26135,cl_31868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26135 v h) (hints_cons _ _ _ (der_31868 v h) (by intro d hd; cases hd)))
def cl_31871 : CNF.NClause := [(35,false),(40,false),(56,true),(55,true),(94,true)]
theorem der_31871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31871 :=
  CNF.rup_sound cl_31871 [cl_26136,cl_31864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26136 v h) (hints_cons _ _ _ (der_31864 v h) (by intro d hd; cases hd)))
def cl_31872 : CNF.NClause := [(35,false),(55,false),(45,true),(40,true),(94,true)]
theorem der_31872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31872 :=
  CNF.rup_sound cl_31872 [cl_26137,cl_31393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26137 v h) (hints_cons _ _ _ (der_31393 v h) (by intro d hd; cases hd)))
def cl_31873 : CNF.NClause := [(46,false),(47,false),(49,true),(50,true),(108,true)]
theorem der_31873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31873 :=
  CNF.rup_sound cl_31873 [cl_26138,cl_31407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26138 v h) (hints_cons _ _ _ (der_31407 v h) (by intro d hd; cases hd)))
def cl_31874 : CNF.NClause := [(48,false),(47,false),(49,false),(50,true),(108,true)]
theorem der_31874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31874 :=
  CNF.rup_sound cl_31874 [cl_26139,cl_31169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26139 v h) (hints_cons _ _ _ (der_31169 v h) (by intro d hd; cases hd)))
def cl_31875 : CNF.NClause := [(58,false),(36,false),(43,false),(52,true),(116,true)]
theorem der_31875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31875 :=
  CNF.rup_sound cl_31875 [cl_26140,cl_31313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26140 v h) (hints_cons _ _ _ (der_31313 v h) (by intro d hd; cases hd)))
def cl_31876 : CNF.NClause := [(36,false),(52,true),(34,false),(43,false),(116,true)]
theorem der_31876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31876 :=
  CNF.rup_sound cl_31876 [cl_26141,cl_31875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26141 v h) (hints_cons _ _ _ (der_31875 v h) (by intro d hd; cases hd)))
def cl_31877 : CNF.NClause := [(48,false),(46,false),(49,true),(61,true),(108,true)]
theorem der_31877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31877 :=
  CNF.rup_sound cl_31877 [cl_26142,cl_30114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26142 v h) (hints_cons _ _ _ (der_30114 v h) (by intro d hd; cases hd)))
def cl_31878 : CNF.NClause := [(59,false),(42,false),(39,false),(31,true),(121,true)]
theorem der_31878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31878 :=
  CNF.rup_sound cl_31878 [cl_26143,cl_23760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26143 v h) (hints_cons _ _ _ (der_23760 v h) (by intro d hd; cases hd)))
def cl_31879 : CNF.NClause := [(59,false),(31,true),(53,false),(39,true),(121,true)]
theorem der_31879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31879 :=
  CNF.rup_sound cl_31879 [cl_26144,cl_31060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26144 v h) (hints_cons _ _ _ (der_31060 v h) (by intro d hd; cases hd)))
def cl_31880 : CNF.NClause := [(48,false),(49,false),(50,true),(61,true),(108,true)]
theorem der_31880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31880 :=
  CNF.rup_sound cl_31880 [cl_26145,cl_31169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26145 v h) (hints_cons _ _ _ (der_31169 v h) (by intro d hd; cases hd)))
def cl_31881 : CNF.NClause := [(41,false),(54,false),(37,false),(60,true),(105,true)]
theorem der_31881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31881 :=
  CNF.rup_sound cl_31881 [cl_26148,cl_31509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26148 v h) (hints_cons _ _ _ (der_31509 v h) (by intro d hd; cases hd)))
def cl_31882 : CNF.NClause := [(42,false),(43,false),(45,false),(44,false),(103,true)]
theorem der_31882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31882 :=
  CNF.rup_sound cl_31882 [cl_26149,cl_31627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26149 v h) (hints_cons _ _ _ (der_31627 v h) (by intro d hd; cases hd)))
def cl_31883 : CNF.NClause := [(35,false),(37,false),(46,false),(44,false),(109,true)]
theorem der_31883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31883 :=
  CNF.rup_sound cl_31883 [cl_26151,cl_30968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26151 v h) (hints_cons _ _ _ (der_30968 v h) (by intro d hd; cases hd)))
def cl_31884 : CNF.NClause := [(59,false),(36,false),(33,false),(47,false),(115,true)]
theorem der_31884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31884 :=
  CNF.rup_sound cl_31884 [cl_26152,cl_31540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26152 v h) (hints_cons _ _ _ (der_31540 v h) (by intro d hd; cases hd)))
def cl_31885 : CNF.NClause := [(41,false),(42,false),(43,false),(45,true),(103,true)]
theorem der_31885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31885 :=
  CNF.rup_sound cl_31885 [cl_26154,cl_31619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26154 v h) (hints_cons _ _ _ (der_31619 v h) (by intro d hd; cases hd)))
def cl_31886 : CNF.NClause := [(39,false),(34,false),(44,false),(49,true),(96,true)]
theorem der_31886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31886 :=
  CNF.rup_sound cl_31886 [cl_26155,cl_25580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26155 v h) (hints_cons _ _ _ (der_25580 v h) (by intro d hd; cases hd)))
def cl_31887 : CNF.NClause := [(35,false),(58,false),(44,false),(46,true),(109,true)]
theorem der_31887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31887 :=
  CNF.rup_sound cl_31887 [cl_26157,cl_31746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26157 v h) (hints_cons _ _ _ (der_31746 v h) (by intro d hd; cases hd)))
def cl_31888 : CNF.NClause := [(59,false),(44,false),(33,false),(47,true),(115,true)]
theorem der_31888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31888 :=
  CNF.rup_sound cl_31888 [cl_26158,cl_31543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26158 v h) (hints_cons _ _ _ (der_31543 v h) (by intro d hd; cases hd)))
def cl_31889 : CNF.NClause := [(48,false),(60,false),(44,false),(40,true),(119,true)]
theorem der_31889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31889 :=
  CNF.rup_sound cl_31889 [cl_26160,cl_31012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26160 v h) (hints_cons _ _ _ (der_31012 v h) (by intro d hd; cases hd)))
def cl_31890 : CNF.NClause := [(60,false),(40,false),(31,true),(52,true),(119,true)]
theorem der_31890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31890 :=
  CNF.rup_sound cl_31890 [cl_26162,cl_26161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26162 v h) (hints_cons _ _ _ (der_26161 v h) (by intro d hd; cases hd)))
def cl_31891 : CNF.NClause := [(48,false),(52,false),(31,true),(60,true),(119,true)]
theorem der_31891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31891 :=
  CNF.rup_sound cl_31891 [cl_26163,cl_23890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26163 v h) (hints_cons _ _ _ (der_23890 v h) (by intro d hd; cases hd)))
def cl_31892 : CNF.NClause := [(40,false),(52,false),(44,false),(48,true),(119,true)]
theorem der_31892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31892 :=
  CNF.rup_sound cl_31892 [cl_26164,cl_31020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26164 v h) (hints_cons _ _ _ (der_31020 v h) (by intro d hd; cases hd)))
def cl_31893 : CNF.NClause := [(48,false),(40,false),(31,true),(52,true),(119,true)]
theorem der_31893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31893 :=
  CNF.rup_sound cl_31893 [cl_26165,cl_26161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26165 v h) (hints_cons _ _ _ (der_26161 v h) (by intro d hd; cases hd)))
def cl_31894 : CNF.NClause := [(40,false),(44,false),(48,true),(60,true),(119,true)]
theorem der_31894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31894 :=
  CNF.rup_sound cl_31894 [cl_26166,cl_31028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26166 v h) (hints_cons _ _ _ (der_31028 v h) (by intro d hd; cases hd)))
def cl_31895 : CNF.NClause := [(60,false),(44,false),(40,true),(48,true),(119,true)]
theorem der_31895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31895 :=
  CNF.rup_sound cl_31895 [cl_26167,cl_31015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26167 v h) (hints_cons _ _ _ (der_31015 v h) (by intro d hd; cases hd)))
def cl_31904 : CNF.NClause := [(42,false),(37,false),(47,false),(56,false),(97,true)]
theorem der_31904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31904 :=
  CNF.rup_sound cl_31904 [cl_26179,cl_26171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26179 v h) (hints_cons _ _ _ (der_26171 v h) (by intro d hd; cases hd)))
def cl_31908 : CNF.NClause := [(42,false),(37,false),(56,false),(32,true),(97,true)]
theorem der_31908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31908 :=
  CNF.rup_sound cl_31908 [cl_26183,cl_31904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26183 v h) (hints_cons _ _ _ (der_31904 v h) (by intro d hd; cases hd)))
def cl_31911 : CNF.NClause := [(42,false),(37,false),(52,false),(47,false),(97,true)]
theorem der_31911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31911 :=
  CNF.rup_sound cl_31911 [cl_26186,cl_26171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26186 v h) (hints_cons _ _ _ (der_26171 v h) (by intro d hd; cases hd)))
def cl_31912 : CNF.NClause := [(42,false),(52,false),(47,false),(37,true),(97,true)]
theorem der_31912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31912 :=
  CNF.rup_sound cl_31912 [cl_26187,cl_30775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26187 v h) (hints_cons _ _ _ (der_30775 v h) (by intro d hd; cases hd)))
def cl_31913 : CNF.NClause := [(37,false),(52,false),(47,false),(42,true),(97,true)]
theorem der_31913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31913 :=
  CNF.rup_sound cl_31913 [cl_26188,cl_31216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26188 v h) (hints_cons _ _ _ (der_31216 v h) (by intro d hd; cases hd)))
def cl_31914 : CNF.NClause := [(52,false),(47,false),(37,true),(42,true),(97,true)]
theorem der_31914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31914 :=
  CNF.rup_sound cl_31914 [cl_26189,cl_30774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26189 v h) (hints_cons _ _ _ (der_30774 v h) (by intro d hd; cases hd)))
def cl_31915 : CNF.NClause := [(42,false),(37,false),(52,false),(56,true),(97,true)]
theorem der_31915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31915 :=
  CNF.rup_sound cl_31915 [cl_26190,cl_31911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26190 v h) (hints_cons _ _ _ (der_31911 v h) (by intro d hd; cases hd)))
def cl_31916 : CNF.NClause := [(42,false),(52,false),(47,true),(37,true),(97,true)]
theorem der_31916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31916 :=
  CNF.rup_sound cl_31916 [cl_26191,cl_30775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26191 v h) (hints_cons _ _ _ (der_30775 v h) (by intro d hd; cases hd)))
def cl_31917 : CNF.NClause := [(37,false),(52,false),(47,true),(42,true),(97,true)]
theorem der_31917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31917 :=
  CNF.rup_sound cl_31917 [cl_26192,cl_31216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26192 v h) (hints_cons _ _ _ (der_31216 v h) (by intro d hd; cases hd)))
def cl_31918 : CNF.NClause := [(42,false),(37,false),(47,false),(56,true),(97,true)]
theorem der_31918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31918 :=
  CNF.rup_sound cl_31918 [cl_26193,cl_31915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26193 v h) (hints_cons _ _ _ (der_31915 v h) (by intro d hd; cases hd)))
def cl_31919 : CNF.NClause := [(42,false),(47,false),(56,true),(52,true),(97,true)]
theorem der_31919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31919 :=
  CNF.rup_sound cl_31919 [cl_26194,cl_24786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26194 v h) (hints_cons _ _ _ (der_24786 v h) (by intro d hd; cases hd)))
def cl_31920 : CNF.NClause := [(37,false),(47,false),(42,true),(32,true),(97,true)]
theorem der_31920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31920 :=
  CNF.rup_sound cl_31920 [cl_26195,cl_31913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26195 v h) (hints_cons _ _ _ (der_31913 v h) (by intro d hd; cases hd)))
def cl_31921 : CNF.NClause := [(42,false),(37,false),(56,true),(52,true),(97,true)]
theorem der_31921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31921 :=
  CNF.rup_sound cl_31921 [cl_26196,cl_31918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26196 v h) (hints_cons _ _ _ (der_31918 v h) (by intro d hd; cases hd)))
def cl_31922 : CNF.NClause := [(57,false),(51,false),(50,false),(44,false),(102,true)]
theorem der_31922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31922 :=
  CNF.rup_sound cl_31922 [cl_26198,cl_26197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26198 v h) (hints_cons _ _ _ (der_26197 v h) (by intro d hd; cases hd)))
def cl_31924 : CNF.NClause := [(57,false),(51,false),(38,false),(44,false),(102,true)]
theorem der_31924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31924 :=
  CNF.rup_sound cl_31924 [cl_26201,cl_26197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26201 v h) (hints_cons _ _ _ (der_26197 v h) (by intro d hd; cases hd)))
def cl_31925 : CNF.NClause := [(57,false),(51,false),(44,false),(38,true),(102,true)]
theorem der_31925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31925 :=
  CNF.rup_sound cl_31925 [cl_26202,cl_31922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26202 v h) (hints_cons _ _ _ (der_31922 v h) (by intro d hd; cases hd)))
def cl_31926 : CNF.NClause := [(57,false),(51,false),(38,false),(50,true),(102,true)]
theorem der_31926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31926 :=
  CNF.rup_sound cl_31926 [cl_26203,cl_31924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26203 v h) (hints_cons _ _ _ (der_31924 v h) (by intro d hd; cases hd)))
def cl_31927 : CNF.NClause := [(57,false),(51,false),(38,true),(44,true),(102,true)]
theorem der_31927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31927 :=
  CNF.rup_sound cl_31927 [cl_26204,cl_23917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26204 v h) (hints_cons _ _ _ (der_23917 v h) (by intro d hd; cases hd)))
def cl_31928 : CNF.NClause := [(57,false),(50,false),(38,false),(44,false),(102,true)]
theorem der_31928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31928 :=
  CNF.rup_sound cl_31928 [cl_26205,cl_26197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26205 v h) (hints_cons _ _ _ (der_26197 v h) (by intro d hd; cases hd)))
def cl_31929 : CNF.NClause := [(57,false),(50,false),(44,false),(32,true),(102,true)]
theorem der_31929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31929 :=
  CNF.rup_sound cl_31929 [cl_26206,cl_31928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26206 v h) (hints_cons _ _ _ (der_31928 v h) (by intro d hd; cases hd)))
def cl_31930 : CNF.NClause := [(57,false),(50,false),(38,false),(32,true),(102,true)]
theorem der_31930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31930 :=
  CNF.rup_sound cl_31930 [cl_26207,cl_31928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26207 v h) (hints_cons _ _ _ (der_31928 v h) (by intro d hd; cases hd)))
def cl_31931 : CNF.NClause := [(57,false),(50,false),(38,true),(44,true),(102,true)]
theorem der_31931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31931 :=
  CNF.rup_sound cl_31931 [cl_26208,cl_30131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26208 v h) (hints_cons _ _ _ (der_30131 v h) (by intro d hd; cases hd)))
def cl_31932 : CNF.NClause := [(57,false),(38,false),(44,false),(51,true),(102,true)]
theorem der_31932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31932 :=
  CNF.rup_sound cl_31932 [cl_26209,cl_31928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26209 v h) (hints_cons _ _ _ (der_31928 v h) (by intro d hd; cases hd)))
def cl_31933 : CNF.NClause := [(57,false),(44,false),(38,true),(32,true),(102,true)]
theorem der_31933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31933 :=
  CNF.rup_sound cl_31933 [cl_26210,cl_31929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26210 v h) (hints_cons _ _ _ (der_31929 v h) (by intro d hd; cases hd)))
def cl_31934 : CNF.NClause := [(57,false),(38,false),(44,true),(50,true),(102,true)]
theorem der_31934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31934 :=
  CNF.rup_sound cl_31934 [cl_26211,cl_23894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26211 v h) (hints_cons _ _ _ (der_23894 v h) (by intro d hd; cases hd)))
def cl_31935 : CNF.NClause := [(51,false),(50,false),(38,false),(44,false),(102,true)]
theorem der_31935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31935 :=
  CNF.rup_sound cl_31935 [cl_26212,cl_31928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26212 v h) (hints_cons _ _ _ (der_31928 v h) (by intro d hd; cases hd)))
def cl_31936 : CNF.NClause := [(51,false),(50,false),(44,false),(32,true),(102,true)]
theorem der_31936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31936 :=
  CNF.rup_sound cl_31936 [cl_26213,cl_31935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26213 v h) (hints_cons _ _ _ (der_31935 v h) (by intro d hd; cases hd)))
def cl_31937 : CNF.NClause := [(51,false),(50,false),(38,false),(32,true),(102,true)]
theorem der_31937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31937 :=
  CNF.rup_sound cl_31937 [cl_26214,cl_31936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26214 v h) (hints_cons _ _ _ (der_31936 v h) (by intro d hd; cases hd)))
def cl_31938 : CNF.NClause := [(51,false),(50,false),(38,true),(44,true),(102,true)]
theorem der_31938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31938 :=
  CNF.rup_sound cl_31938 [cl_26215,cl_31931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26215 v h) (hints_cons _ _ _ (der_31931 v h) (by intro d hd; cases hd)))
def cl_31939 : CNF.NClause := [(51,false),(38,false),(44,false),(50,true),(102,true)]
theorem der_31939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31939 :=
  CNF.rup_sound cl_31939 [cl_26216,cl_31924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26216 v h) (hints_cons _ _ _ (der_31924 v h) (by intro d hd; cases hd)))
def cl_31940 : CNF.NClause := [(51,false),(44,false),(50,true),(32,true),(102,true)]
theorem der_31940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31940 :=
  CNF.rup_sound cl_31940 [cl_26217,cl_31939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26217 v h) (hints_cons _ _ _ (der_31939 v h) (by intro d hd; cases hd)))
def cl_31941 : CNF.NClause := [(51,false),(38,false),(50,true),(57,true),(102,true)]
theorem der_31941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31941 :=
  CNF.rup_sound cl_31941 [cl_26218,cl_31939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26218 v h) (hints_cons _ _ _ (der_31939 v h) (by intro d hd; cases hd)))
def cl_31942 : CNF.NClause := [(50,false),(38,false),(44,false),(51,true),(102,true)]
theorem der_31942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31942 :=
  CNF.rup_sound cl_31942 [cl_26219,cl_30130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26219 v h) (hints_cons _ _ _ (der_30130 v h) (by intro d hd; cases hd)))
def cl_31943 : CNF.NClause := [(50,false),(44,false),(51,true),(32,true),(102,true)]
theorem der_31943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31943 :=
  CNF.rup_sound cl_31943 [cl_26220,cl_31942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26220 v h) (hints_cons _ _ _ (der_31942 v h) (by intro d hd; cases hd)))
def cl_31944 : CNF.NClause := [(50,false),(38,false),(44,true),(32,true),(102,true)]
theorem der_31944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31944 :=
  CNF.rup_sound cl_31944 [cl_26221,cl_31930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26221 v h) (hints_cons _ _ _ (der_31930 v h) (by intro d hd; cases hd)))
def cl_31945 : CNF.NClause := [(38,false),(44,false),(50,true),(51,true),(102,true)]
theorem der_31945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31945 :=
  CNF.rup_sound cl_31945 [cl_26222,cl_31932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26222 v h) (hints_cons _ _ _ (der_31932 v h) (by intro d hd; cases hd)))
def cl_31946 : CNF.NClause := [(41,false),(48,false),(58,false),(55,false),(107,true)]
theorem der_31946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31946 :=
  CNF.rup_sound cl_31946 [cl_26224,cl_26223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26224 v h) (hints_cons _ _ _ (der_26223 v h) (by intro d hd; cases hd)))
def cl_31947 : CNF.NClause := [(48,false),(39,false),(58,false),(55,false),(107,true)]
theorem der_31947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31947 :=
  CNF.rup_sound cl_31947 [cl_26225,cl_26223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26225 v h) (hints_cons _ _ _ (der_26223 v h) (by intro d hd; cases hd)))
def cl_31948 : CNF.NClause := [(48,false),(58,false),(55,false),(39,true),(107,true)]
theorem der_31948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31948 :=
  CNF.rup_sound cl_31948 [cl_26226,cl_31946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26226 v h) (hints_cons _ _ _ (der_31946 v h) (by intro d hd; cases hd)))
def cl_31949 : CNF.NClause := [(41,false),(39,false),(58,false),(55,false),(107,true)]
theorem der_31949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31949 :=
  CNF.rup_sound cl_31949 [cl_26227,cl_26223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26227 v h) (hints_cons _ _ _ (der_26223 v h) (by intro d hd; cases hd)))
def cl_31950 : CNF.NClause := [(41,false),(58,false),(55,false),(39,true),(107,true)]
theorem der_31950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31950 :=
  CNF.rup_sound cl_31950 [cl_26228,cl_30736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26228 v h) (hints_cons _ _ _ (der_30736 v h) (by intro d hd; cases hd)))
def cl_31951 : CNF.NClause := [(39,false),(58,false),(55,false),(41,true),(107,true)]
theorem der_31951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31951 :=
  CNF.rup_sound cl_31951 [cl_26229,cl_31947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26229 v h) (hints_cons _ _ _ (der_31947 v h) (by intro d hd; cases hd)))
def cl_31952 : CNF.NClause := [(58,false),(55,false),(39,true),(41,true),(107,true)]
theorem der_31952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31952 :=
  CNF.rup_sound cl_31952 [cl_26230,cl_31948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26230 v h) (hints_cons _ _ _ (der_31948 v h) (by intro d hd; cases hd)))
def cl_31953 : CNF.NClause := [(41,false),(48,false),(39,false),(58,false),(107,true)]
theorem der_31953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31953 :=
  CNF.rup_sound cl_31953 [cl_26231,cl_26223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26231 v h) (hints_cons _ _ _ (der_26223 v h) (by intro d hd; cases hd)))
def cl_31954 : CNF.NClause := [(41,false),(48,false),(58,false),(55,true),(107,true)]
theorem der_31954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31954 :=
  CNF.rup_sound cl_31954 [cl_26232,cl_31953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26232 v h) (hints_cons _ _ _ (der_31953 v h) (by intro d hd; cases hd)))
def cl_31955 : CNF.NClause := [(48,false),(39,false),(58,false),(55,true),(107,true)]
theorem der_31955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31955 :=
  CNF.rup_sound cl_31955 [cl_26233,cl_31954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26233 v h) (hints_cons _ _ _ (der_31954 v h) (by intro d hd; cases hd)))
def cl_31956 : CNF.NClause := [(48,false),(58,false),(39,true),(41,true),(107,true)]
theorem der_31956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31956 :=
  CNF.rup_sound cl_31956 [cl_26234,cl_30735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26234 v h) (hints_cons _ _ _ (der_30735 v h) (by intro d hd; cases hd)))
def cl_31957 : CNF.NClause := [(41,false),(39,false),(58,false),(55,true),(107,true)]
theorem der_31957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31957 :=
  CNF.rup_sound cl_31957 [cl_26235,cl_31953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26235 v h) (hints_cons _ _ _ (der_31953 v h) (by intro d hd; cases hd)))
def cl_31958 : CNF.NClause := [(41,false),(58,false),(39,true),(48,true),(107,true)]
theorem der_31958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31958 :=
  CNF.rup_sound cl_31958 [cl_26236,cl_31950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26236 v h) (hints_cons _ _ _ (der_31950 v h) (by intro d hd; cases hd)))
def cl_31959 : CNF.NClause := [(39,false),(58,false),(55,true),(41,true),(107,true)]
theorem der_31959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31959 :=
  CNF.rup_sound cl_31959 [cl_26237,cl_31955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26237 v h) (hints_cons _ _ _ (der_31955 v h) (by intro d hd; cases hd)))
def cl_31960 : CNF.NClause := [(41,false),(48,false),(39,false),(55,false),(107,true)]
theorem der_31960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31960 :=
  CNF.rup_sound cl_31960 [cl_26238,cl_31953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26238 v h) (hints_cons _ _ _ (der_31953 v h) (by intro d hd; cases hd)))
def cl_31961 : CNF.NClause := [(41,false),(48,false),(55,false),(39,true),(107,true)]
theorem der_31961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31961 :=
  CNF.rup_sound cl_31961 [cl_26239,cl_30739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26239 v h) (hints_cons _ _ _ (der_30739 v h) (by intro d hd; cases hd)))
def cl_31962 : CNF.NClause := [(48,false),(39,false),(55,false),(58,true),(107,true)]
theorem der_31962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31962 :=
  CNF.rup_sound cl_31962 [cl_26240,cl_31960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26240 v h) (hints_cons _ _ _ (der_31960 v h) (by intro d hd; cases hd)))
def cl_31963 : CNF.NClause := [(48,false),(55,false),(39,true),(41,true),(107,true)]
theorem der_31963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31963 :=
  CNF.rup_sound cl_31963 [cl_26241,cl_30738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26241 v h) (hints_cons _ _ _ (der_30738 v h) (by intro d hd; cases hd)))
def cl_31964 : CNF.NClause := [(41,false),(39,false),(55,false),(58,true),(107,true)]
theorem der_31964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31964 :=
  CNF.rup_sound cl_31964 [cl_26242,cl_31960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26242 v h) (hints_cons _ _ _ (der_31960 v h) (by intro d hd; cases hd)))
def cl_31965 : CNF.NClause := [(41,false),(55,false),(39,true),(58,true),(107,true)]
theorem der_31965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31965 :=
  CNF.rup_sound cl_31965 [cl_26243,cl_30739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26243 v h) (hints_cons _ _ _ (der_30739 v h) (by intro d hd; cases hd)))
def cl_31966 : CNF.NClause := [(39,false),(55,false),(58,true),(41,true),(107,true)]
theorem der_31966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31966 :=
  CNF.rup_sound cl_31966 [cl_26244,cl_31962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26244 v h) (hints_cons _ _ _ (der_31962 v h) (by intro d hd; cases hd)))
def cl_31967 : CNF.NClause := [(41,false),(48,false),(39,false),(55,true),(107,true)]
theorem der_31967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31967 :=
  CNF.rup_sound cl_31967 [cl_26245,cl_31953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26245 v h) (hints_cons _ _ _ (der_31953 v h) (by intro d hd; cases hd)))
def cl_31968 : CNF.NClause := [(41,false),(48,false),(39,true),(58,true),(107,true)]
theorem der_31968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31968 :=
  CNF.rup_sound cl_31968 [cl_26246,cl_30742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26246 v h) (hints_cons _ _ _ (der_30742 v h) (by intro d hd; cases hd)))
def cl_31969 : CNF.NClause := [(48,false),(39,false),(55,true),(41,true),(107,true)]
theorem der_31969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31969 :=
  CNF.rup_sound cl_31969 [cl_26247,cl_31955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26247 v h) (hints_cons _ _ _ (der_31955 v h) (by intro d hd; cases hd)))
def cl_31970 : CNF.NClause := [(41,false),(39,false),(48,true),(55,true),(107,true)]
theorem der_31970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31970 :=
  CNF.rup_sound cl_31970 [cl_26248,cl_31957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26248 v h) (hints_cons _ _ _ (der_31957 v h) (by intro d hd; cases hd)))
def cl_31971 : CNF.NClause := [(59,false),(54,false),(43,false),(46,false),(112,true)]
theorem der_31971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31971 :=
  CNF.rup_sound cl_31971 [cl_26250,cl_26249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26250 v h) (hints_cons _ _ _ (der_26249 v h) (by intro d hd; cases hd)))
def cl_31972 : CNF.NClause := [(59,false),(54,false),(40,false),(46,false),(112,true)]
theorem der_31972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31972 :=
  CNF.rup_sound cl_31972 [cl_26251,cl_26249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26251 v h) (hints_cons _ _ _ (der_26249 v h) (by intro d hd; cases hd)))
def cl_31974 : CNF.NClause := [(59,false),(40,false),(54,false),(43,false),(112,true)]
theorem der_31974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31974 :=
  CNF.rup_sound cl_31974 [cl_26253,cl_26249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26253 v h) (hints_cons _ _ _ (der_26249 v h) (by intro d hd; cases hd)))
def cl_31975 : CNF.NClause := [(59,false),(54,false),(43,false),(46,true),(112,true)]
theorem der_31975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31975 :=
  CNF.rup_sound cl_31975 [cl_26254,cl_31974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26254 v h) (hints_cons _ _ _ (der_31974 v h) (by intro d hd; cases hd)))
def cl_31976 : CNF.NClause := [(59,false),(54,false),(40,false),(46,true),(112,true)]
theorem der_31976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31976 :=
  CNF.rup_sound cl_31976 [cl_26255,cl_31974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26255 v h) (hints_cons _ _ _ (der_31974 v h) (by intro d hd; cases hd)))
def cl_31977 : CNF.NClause := [(59,false),(46,false),(40,false),(43,false),(112,true)]
theorem der_31977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31977 :=
  CNF.rup_sound cl_31977 [cl_26257,cl_31974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26257 v h) (hints_cons _ _ _ (der_31974 v h) (by intro d hd; cases hd)))
def cl_31978 : CNF.NClause := [(59,false),(46,false),(43,false),(40,true),(112,true)]
theorem der_31978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31978 :=
  CNF.rup_sound cl_31978 [cl_26258,cl_31971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26258 v h) (hints_cons _ _ _ (der_31971 v h) (by intro d hd; cases hd)))
def cl_31979 : CNF.NClause := [(59,false),(40,false),(46,false),(43,true),(112,true)]
theorem der_31979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31979 :=
  CNF.rup_sound cl_31979 [cl_26259,cl_31972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26259 v h) (hints_cons _ _ _ (der_31972 v h) (by intro d hd; cases hd)))
def cl_31980 : CNF.NClause := [(59,false),(46,false),(40,true),(32,true),(112,true)]
theorem der_31980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31980 :=
  CNF.rup_sound cl_31980 [cl_26260,cl_31978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26260 v h) (hints_cons _ _ _ (der_31978 v h) (by intro d hd; cases hd)))
def cl_31981 : CNF.NClause := [(59,false),(40,false),(43,false),(46,true),(112,true)]
theorem der_31981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31981 :=
  CNF.rup_sound cl_31981 [cl_26261,cl_31974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26261 v h) (hints_cons _ _ _ (der_31974 v h) (by intro d hd; cases hd)))
def cl_31982 : CNF.NClause := [(59,false),(54,true),(40,true),(43,false),(112,true)]
theorem der_31982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31982 :=
  CNF.rup_sound cl_31982 [cl_26262,cl_31978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26262 v h) (hints_cons _ _ _ (der_31978 v h) (by intro d hd; cases hd)))
def cl_31983 : CNF.NClause := [(59,false),(40,false),(46,true),(54,true),(112,true)]
theorem der_31983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31983 :=
  CNF.rup_sound cl_31983 [cl_26263,cl_31981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26263 v h) (hints_cons _ _ _ (der_31981 v h) (by intro d hd; cases hd)))
def cl_31984 : CNF.NClause := [(54,false),(40,false),(43,false),(46,false),(112,true)]
theorem der_31984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31984 :=
  CNF.rup_sound cl_31984 [cl_26264,cl_31974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26264 v h) (hints_cons _ _ _ (der_31974 v h) (by intro d hd; cases hd)))
def cl_31985 : CNF.NClause := [(54,false),(32,true),(46,false),(43,false),(112,true)]
theorem der_31985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31985 :=
  CNF.rup_sound cl_31985 [cl_26265,cl_31984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26265 v h) (hints_cons _ _ _ (der_31984 v h) (by intro d hd; cases hd)))
def cl_31986 : CNF.NClause := [(54,false),(40,false),(46,false),(32,true),(112,true)]
theorem der_31986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31986 :=
  CNF.rup_sound cl_31986 [cl_26266,cl_31984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26266 v h) (hints_cons _ _ _ (der_31984 v h) (by intro d hd; cases hd)))
def cl_31987 : CNF.NClause := [(54,false),(46,false),(40,true),(43,true),(112,true)]
theorem der_31987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31987 :=
  CNF.rup_sound cl_31987 [cl_26267,cl_31442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26267 v h) (hints_cons _ _ _ (der_31442 v h) (by intro d hd; cases hd)))
def cl_31988 : CNF.NClause := [(54,false),(59,true),(40,false),(43,false),(112,true)]
theorem der_31988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31988 :=
  CNF.rup_sound cl_31988 [cl_26268,cl_31984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26268 v h) (hints_cons _ _ _ (der_31984 v h) (by intro d hd; cases hd)))
def cl_31989 : CNF.NClause := [(54,false),(112,true),(59,true),(32,true),(43,false)]
theorem der_31989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31989 :=
  CNF.rup_sound cl_31989 [cl_26269,cl_31988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26269 v h) (hints_cons _ _ _ (der_31988 v h) (by intro d hd; cases hd)))
def cl_31990 : CNF.NClause := [(54,false),(40,false),(43,true),(59,true),(112,true)]
theorem der_31990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31990 :=
  CNF.rup_sound cl_31990 [cl_26270,cl_31419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26270 v h) (hints_cons _ _ _ (der_31419 v h) (by intro d hd; cases hd)))
def cl_31991 : CNF.NClause := [(40,false),(46,false),(43,false),(59,true),(112,true)]
theorem der_31991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31991 :=
  CNF.rup_sound cl_31991 [cl_26271,cl_31984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26271 v h) (hints_cons _ _ _ (der_31984 v h) (by intro d hd; cases hd)))
def cl_31992 : CNF.NClause := [(46,false),(43,false),(54,true),(59,true),(112,true)]
theorem der_31992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31992 :=
  CNF.rup_sound cl_31992 [cl_26272,cl_31991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26272 v h) (hints_cons _ _ _ (der_31991 v h) (by intro d hd; cases hd)))
def cl_31993 : CNF.NClause := [(40,false),(46,false),(43,true),(32,true),(112,true)]
theorem der_31993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31993 :=
  CNF.rup_sound cl_31993 [cl_26273,cl_31986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26273 v h) (hints_cons _ _ _ (der_31986 v h) (by intro d hd; cases hd)))
def cl_31994 : CNF.NClause := [(40,false),(46,true),(54,true),(43,false),(112,true)]
theorem der_31994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31994 :=
  CNF.rup_sound cl_31994 [cl_26274,cl_31981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26274 v h) (hints_cons _ _ _ (der_31981 v h) (by intro d hd; cases hd)))
def cl_31995 : CNF.NClause := [(60,false),(45,false),(53,false),(49,false),(117,true)]
theorem der_31995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31995 :=
  CNF.rup_sound cl_31995 [cl_26276,cl_26275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26276 v h) (hints_cons _ _ _ (der_26275 v h) (by intro d hd; cases hd)))
def cl_31997 : CNF.NClause := [(60,false),(36,true),(49,false),(53,false),(117,true)]
theorem der_31997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31997 :=
  CNF.rup_sound cl_31997 [cl_26278,cl_31995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26278 v h) (hints_cons _ _ _ (der_31995 v h) (by intro d hd; cases hd)))
def cl_31998 : CNF.NClause := [(60,false),(36,false),(45,false),(53,false),(117,true)]
theorem der_31998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31998 :=
  CNF.rup_sound cl_31998 [cl_26279,cl_26275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26279 v h) (hints_cons _ _ _ (der_26275 v h) (by intro d hd; cases hd)))
def cl_31999 : CNF.NClause := [(60,false),(45,false),(53,false),(32,true),(117,true)]
theorem der_31999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31999 :=
  CNF.rup_sound cl_31999 [cl_26280,cl_31998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26280 v h) (hints_cons _ _ _ (der_31998 v h) (by intro d hd; cases hd)))
def cl_32000 : CNF.NClause := [(60,false),(36,false),(53,false),(32,true),(117,true)]
theorem der_32000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32000 :=
  CNF.rup_sound cl_32000 [cl_26281,cl_31998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26281 v h) (hints_cons _ _ _ (der_31998 v h) (by intro d hd; cases hd)))
def cl_32001 : CNF.NClause := [(60,false),(45,true),(53,false),(36,true),(117,true)]
theorem der_32001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32001 :=
  CNF.rup_sound cl_32001 [cl_26282,cl_31997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26282 v h) (hints_cons _ _ _ (der_31997 v h) (by intro d hd; cases hd)))
def cl_32002 : CNF.NClause := [(60,false),(36,false),(45,false),(49,false),(117,true)]
theorem der_32002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32002 :=
  CNF.rup_sound cl_32002 [cl_26283,cl_26275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26283 v h) (hints_cons _ _ _ (der_26275 v h) (by intro d hd; cases hd)))
def cl_32003 : CNF.NClause := [(60,false),(45,false),(49,false),(32,true),(117,true)]
theorem der_32003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32003 :=
  CNF.rup_sound cl_32003 [cl_26284,cl_32002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26284 v h) (hints_cons _ _ _ (der_32002 v h) (by intro d hd; cases hd)))
def cl_32004 : CNF.NClause := [(60,false),(36,false),(49,false),(53,true),(117,true)]
theorem der_32004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32004 :=
  CNF.rup_sound cl_32004 [cl_26285,cl_32002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26285 v h) (hints_cons _ _ _ (der_32002 v h) (by intro d hd; cases hd)))
def cl_32005 : CNF.NClause := [(60,false),(49,false),(45,true),(36,true),(117,true)]
theorem der_32005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32005 :=
  CNF.rup_sound cl_32005 [cl_26286,cl_30852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26286 v h) (hints_cons _ _ _ (der_30852 v h) (by intro d hd; cases hd)))
def cl_32006 : CNF.NClause := [(60,false),(36,false),(45,false),(53,true),(117,true)]
theorem der_32006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32006 :=
  CNF.rup_sound cl_32006 [cl_26287,cl_32004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26287 v h) (hints_cons _ _ _ (der_32004 v h) (by intro d hd; cases hd)))
def cl_32007 : CNF.NClause := [(60,false),(45,false),(36,true),(32,true),(117,true)]
theorem der_32007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32007 :=
  CNF.rup_sound cl_32007 [cl_26288,cl_32003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26288 v h) (hints_cons _ _ _ (der_32003 v h) (by intro d hd; cases hd)))
def cl_32008 : CNF.NClause := [(60,false),(36,false),(49,true),(32,true),(117,true)]
theorem der_32008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32008 :=
  CNF.rup_sound cl_32008 [cl_26289,cl_32000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26289 v h) (hints_cons _ _ _ (der_32000 v h) (by intro d hd; cases hd)))
def cl_32009 : CNF.NClause := [(36,false),(45,false),(53,false),(49,false),(117,true)]
theorem der_32009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32009 :=
  CNF.rup_sound cl_32009 [cl_26290,cl_32002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26290 v h) (hints_cons _ _ _ (der_32002 v h) (by intro d hd; cases hd)))
def cl_32010 : CNF.NClause := [(45,false),(49,false),(36,true),(53,false),(117,true)]
theorem der_32010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32010 :=
  CNF.rup_sound cl_32010 [cl_26291,cl_30848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26291 v h) (hints_cons _ _ _ (der_30848 v h) (by intro d hd; cases hd)))
def cl_32011 : CNF.NClause := [(36,false),(49,false),(53,false),(60,true),(117,true)]
theorem der_32011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32011 :=
  CNF.rup_sound cl_32011 [cl_26292,cl_32009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26292 v h) (hints_cons _ _ _ (der_32009 v h) (by intro d hd; cases hd)))
def cl_32012 : CNF.NClause := [(49,false),(117,true),(45,true),(36,true),(53,false)]
theorem der_32012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32012 :=
  CNF.rup_sound cl_32012 [cl_26293,cl_30852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26293 v h) (hints_cons _ _ _ (der_30852 v h) (by intro d hd; cases hd)))
def cl_32013 : CNF.NClause := [(36,false),(45,false),(53,false),(60,true),(117,true)]
theorem der_32013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32013 :=
  CNF.rup_sound cl_32013 [cl_26294,cl_32009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26294 v h) (hints_cons _ _ _ (der_32009 v h) (by intro d hd; cases hd)))
def cl_32014 : CNF.NClause := [(45,false),(36,true),(49,true),(53,false),(117,true)]
theorem der_32014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32014 :=
  CNF.rup_sound cl_32014 [cl_26295,cl_30849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26295 v h) (hints_cons _ _ _ (der_30849 v h) (by intro d hd; cases hd)))
def cl_32015 : CNF.NClause := [(36,false),(117,true),(45,true),(32,true),(53,false)]
theorem der_32015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32015 :=
  CNF.rup_sound cl_32015 [cl_26296,cl_32000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26296 v h) (hints_cons _ _ _ (der_32000 v h) (by intro d hd; cases hd)))
def cl_32016 : CNF.NClause := [(36,false),(45,false),(49,false),(32,true),(117,true)]
theorem der_32016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32016 :=
  CNF.rup_sound cl_32016 [cl_26297,cl_32003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26297 v h) (hints_cons _ _ _ (der_32003 v h) (by intro d hd; cases hd)))
def cl_32017 : CNF.NClause := [(45,false),(49,false),(53,true),(36,true),(117,true)]
theorem der_32017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32017 :=
  CNF.rup_sound cl_32017 [cl_26298,cl_30851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26298 v h) (hints_cons _ _ _ (der_30851 v h) (by intro d hd; cases hd)))
def cl_32018 : CNF.NClause := [(36,false),(49,false),(45,true),(53,true),(117,true)]
theorem der_32018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32018 :=
  CNF.rup_sound cl_32018 [cl_26299,cl_32004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26299 v h) (hints_cons _ _ _ (der_32004 v h) (by intro d hd; cases hd)))
def cl_32019 : CNF.NClause := [(36,false),(45,false),(49,true),(60,true),(117,true)]
theorem der_32019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32019 :=
  CNF.rup_sound cl_32019 [cl_26300,cl_32013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26300 v h) (hints_cons _ _ _ (der_32013 v h) (by intro d hd; cases hd)))
def cl_32020 : CNF.NClause := [(35,false),(34,false),(33,true),(61,true),(118,true)]
theorem der_32020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32020 :=
  CNF.rup_sound cl_32020 [cl_26301,cl_30998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26301 v h) (hints_cons _ _ _ (der_30998 v h) (by intro d hd; cases hd)))
def cl_32021 : CNF.NClause := [(61,true),(34,false),(31,true),(33,false),(118,true)]
theorem der_32021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32021 :=
  CNF.rup_sound cl_32021 [cl_26302,cl_26041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26302 v h) (hints_cons _ _ _ (der_26041 v h) (by intro d hd; cases hd)))
def cl_32023 : CNF.NClause := [(5,true),(17,false),(26,true),(23,false),(4,false),(83,true)]
theorem der_32023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32023 :=
  CNF.rup_sound cl_32023 [cl_1383,cl_30238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1383 v h) (hints_cons _ _ _ (der_30238 v h) (by intro d hd; cases hd)))
def cl_32025 : CNF.NClause := [(1,false),(28,true),(12,true),(15,false),(23,false),(81,true)]
theorem der_32025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32025 :=
  CNF.rup_sound cl_32025 [cl_1255,cl_30355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1255 v h) (hints_cons _ _ _ (der_30355 v h) (by intro d hd; cases hd)))
def cl_32026 : CNF.NClause := [(47,false),(84,false),(68,true),(89,false),(16,true),(66,false)]
theorem der_32026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32026 :=
  CNF.rup_sound cl_32026 [cl_26305,cl_26304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26305 v h) (hints_cons _ _ _ (der_26304 v h) (by intro d hd; cases hd)))
def cl_32027 : CNF.NClause := [(47,false),(77,false),(68,true),(16,true),(89,false),(66,false)]
theorem der_32027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32027 :=
  CNF.rup_sound cl_32027 [cl_26307,cl_26306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26307 v h) (hints_cons _ _ _ (der_26306 v h) (by intro d hd; cases hd)))
def cl_32028 : CNF.NClause := [(47,false),(75,false),(68,true),(89,false),(66,false),(16,true)]
theorem der_32028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32028 :=
  CNF.rup_sound cl_32028 [cl_26308,cl_26306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26308 v h) (hints_cons _ _ _ (der_26306 v h) (by intro d hd; cases hd)))
def cl_32029 : CNF.NClause := [(47,false),(89,false),(68,true),(84,true),(16,true),(66,false)]
theorem der_32029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32029 :=
  CNF.rup_sound cl_32029 [cl_26309,cl_32027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26309 v h) (hints_cons _ _ _ (der_32027 v h) (by intro d hd; cases hd)))
def cl_32030 : CNF.NClause := [(47,false),(68,true),(16,true),(77,false),(66,false),(84,false)]
theorem der_32030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32030 :=
  CNF.rup_sound cl_32030 [cl_26311,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26311 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_32031 : CNF.NClause := [(47,false),(75,false),(68,true),(66,false),(16,true),(84,false)]
theorem der_32031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32031 :=
  CNF.rup_sound cl_32031 [cl_26312,cl_26304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26312 v h) (hints_cons _ _ _ (der_26304 v h) (by intro d hd; cases hd)))
def cl_32032 : CNF.NClause := [(47,false),(84,false),(68,true),(75,true),(16,true),(66,false)]
theorem der_32032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32032 :=
  CNF.rup_sound cl_32032 [cl_26313,cl_32030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26313 v h) (hints_cons _ _ _ (der_32030 v h) (by intro d hd; cases hd)))
def cl_32034 : CNF.NClause := [(47,false),(68,true),(16,true),(77,false),(66,false),(89,true)]
theorem der_32034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32034 :=
  CNF.rup_sound cl_32034 [cl_26315,cl_32030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26315 v h) (hints_cons _ _ _ (der_32030 v h) (by intro d hd; cases hd)))
def cl_32035 : CNF.NClause := [(47,false),(68,true),(77,true),(16,true),(66,false),(75,false)]
theorem der_32035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32035 :=
  CNF.rup_sound cl_32035 [cl_26316,cl_32031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26316 v h) (hints_cons _ _ _ (der_32031 v h) (by intro d hd; cases hd)))
def cl_32036 : CNF.NClause := [(47,false),(68,true),(75,true),(77,true),(16,true),(66,false)]
theorem der_32036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32036 :=
  CNF.rup_sound cl_32036 [cl_26317,cl_32032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26317 v h) (hints_cons _ _ _ (der_32032 v h) (by intro d hd; cases hd)))
def cl_32037 : CNF.NClause := [(81,true),(9,true),(23,false),(15,true),(1,false),(12,false)]
theorem der_32037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32037 :=
  CNF.rup_sound cl_32037 [cl_1227,cl_23570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1227 v h) (hints_cons _ _ _ (der_23570 v h) (by intro d hd; cases hd)))
def cl_32038 : CNF.NClause := [(68,false),(20,true),(4,true),(16,true),(8,true),(29,true)]
theorem der_32038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32038 :=
  CNF.rup_sound cl_32038 [cl_444,cl_23667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_444 v h) (hints_cons _ _ _ (der_23667 v h) (by intro d hd; cases hd)))
def cl_32040 : CNF.NClause := [(73,false),(18,true),(28,true),(10,true),(21,true),(7,true)]
theorem der_32040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32040 :=
  CNF.rup_sound cl_32040 [cl_767,cl_23678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_767 v h) (hints_cons _ _ _ (der_23678 v h) (by intro d hd; cases hd)))
def cl_32041 : CNF.NClause := [(27,false),(11,true),(69,true),(20,false),(2,true),(9,false)]
theorem der_32041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32041 :=
  CNF.rup_sound cl_32041 [cl_462,cl_24386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_462 v h) (hints_cons _ _ _ (der_24386 v h) (by intro d hd; cases hd)))
def cl_32042 : CNF.NClause := [(69,false),(9,true),(2,true),(18,true),(27,true),(20,true)]
theorem der_32042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32042 :=
  CNF.rup_sound cl_32042 [cl_508,cl_23688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_508 v h) (hints_cons _ _ _ (der_23688 v h) (by intro d hd; cases hd)))
def cl_32044 : CNF.NClause := [(73,false),(28,true),(18,true),(4,true),(21,true),(7,true)]
theorem der_32044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32044 :=
  CNF.rup_sound cl_32044 [cl_764,cl_23678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_764 v h) (hints_cons _ _ _ (der_23678 v h) (by intro d hd; cases hd)))
def cl_32054 : CNF.NClause := [(85,false),(19,true),(21,true),(12,true),(5,true),(3,true)]
theorem der_32054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32054 :=
  CNF.rup_sound cl_32054 [cl_1504,cl_23642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1504 v h) (hints_cons _ _ _ (der_23642 v h) (by intro d hd; cases hd)))
def cl_32055 : CNF.NClause := [(84,false),(13,true),(16,true),(5,true),(28,true),(2,true)]
theorem der_32055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32055 :=
  CNF.rup_sound cl_32055 [cl_1456,cl_23660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1456 v h) (hints_cons _ _ _ (der_23660 v h) (by intro d hd; cases hd)))
def cl_32056 : CNF.NClause := [(84,false),(13,true),(2,true),(5,true),(24,true),(28,true)]
theorem der_32056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32056 :=
  CNF.rup_sound cl_32056 [cl_1464,cl_23660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1464 v h) (hints_cons _ _ _ (der_23660 v h) (by intro d hd; cases hd)))
def cl_32057 : CNF.NClause := [(84,false),(28,true),(5,true),(2,true),(16,true),(24,true)]
theorem der_32057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32057 :=
  CNF.rup_sound cl_32057 [cl_1468,cl_23660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1468 v h) (hints_cons _ _ _ (der_23660 v h) (by intro d hd; cases hd)))
def cl_32058 : CNF.NClause := [(84,false),(13,true),(2,true),(16,true),(24,true),(28,true)]
theorem der_32058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32058 :=
  CNF.rup_sound cl_32058 [cl_1470,cl_23660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1470 v h) (hints_cons _ _ _ (der_23660 v h) (by intro d hd; cases hd)))
def cl_32059 : CNF.NClause := [(84,false),(13,true),(24,true),(16,true),(5,true),(28,true)]
theorem der_32059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32059 :=
  CNF.rup_sound cl_32059 [cl_1471,cl_23660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1471 v h) (hints_cons _ _ _ (der_23660 v h) (by intro d hd; cases hd)))
def cl_32060 : CNF.NClause := [(83,false),(4,true),(17,true),(23,true),(11,true),(5,true)]
theorem der_32060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32060 :=
  CNF.rup_sound cl_32060 [cl_1376,cl_23661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1376 v h) (hints_cons _ _ _ (der_23661 v h) (by intro d hd; cases hd)))
def cl_32061 : CNF.NClause := [(83,false),(4,true),(5,true),(17,true),(11,true),(26,true)]
theorem der_32061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32061 :=
  CNF.rup_sound cl_32061 [cl_1392,cl_23661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1392 v h) (hints_cons _ _ _ (der_23661 v h) (by intro d hd; cases hd)))
def cl_32062 : CNF.NClause := [(83,false),(4,true),(26,true),(5,true),(23,true),(11,true)]
theorem der_32062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32062 :=
  CNF.rup_sound cl_32062 [cl_1400,cl_23661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1400 v h) (hints_cons _ _ _ (der_23661 v h) (by intro d hd; cases hd)))
def cl_32063 : CNF.NClause := [(83,false),(17,true),(23,true),(4,true),(26,true),(5,true)]
theorem der_32063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32063 :=
  CNF.rup_sound cl_32063 [cl_1404,cl_23661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1404 v h) (hints_cons _ _ _ (der_23661 v h) (by intro d hd; cases hd)))
def cl_32064 : CNF.NClause := [(83,false),(23,true),(11,true),(26,true),(5,true),(17,true)]
theorem der_32064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32064 :=
  CNF.rup_sound cl_32064 [cl_1407,cl_23661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1407 v h) (hints_cons _ _ _ (der_23661 v h) (by intro d hd; cases hd)))
def cl_32065 : CNF.NClause := [(78,false),(13,true),(27,true),(6,true),(15,true),(4,true)]
theorem der_32065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32065 :=
  CNF.rup_sound cl_32065 [cl_1072,cl_23663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1072 v h) (hints_cons _ _ _ (der_23663 v h) (by intro d hd; cases hd)))
def cl_32066 : CNF.NClause := [(78,false),(13,true),(27,true),(6,true),(22,true),(4,true)]
theorem der_32066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32066 :=
  CNF.rup_sound cl_32066 [cl_1080,cl_23663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1080 v h) (hints_cons _ _ _ (der_23663 v h) (by intro d hd; cases hd)))
def cl_32067 : CNF.NClause := [(78,false),(4,true),(15,true),(27,true),(6,true),(22,true)]
theorem der_32067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32067 :=
  CNF.rup_sound cl_32067 [cl_1084,cl_23663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1084 v h) (hints_cons _ _ _ (der_23663 v h) (by intro d hd; cases hd)))
def cl_32068 : CNF.NClause := [(78,false),(13,true),(15,true),(27,true),(4,true),(22,true)]
theorem der_32068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32068 :=
  CNF.rup_sound cl_32068 [cl_1086,cl_23663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1086 v h) (hints_cons _ _ _ (der_23663 v h) (by intro d hd; cases hd)))
def cl_32069 : CNF.NClause := [(78,false),(13,true),(6,true),(22,true),(15,true),(27,true)]
theorem der_32069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32069 :=
  CNF.rup_sound cl_32069 [cl_1087,cl_23663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1087 v h) (hints_cons _ _ _ (der_23663 v h) (by intro d hd; cases hd)))
def cl_32070 : CNF.NClause := [(46,false),(78,false),(77,true),(15,false),(79,false),(81,false)]
theorem der_32070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32070 :=
  CNF.rup_sound cl_32070 [cl_26328,cl_26325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26328 v h) (hints_cons _ _ _ (der_26325 v h) (by intro d hd; cases hd)))
def cl_32071 : CNF.NClause := [(46,false),(80,true),(15,false),(77,true),(78,false),(79,false)]
theorem der_32071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32071 :=
  CNF.rup_sound cl_32071 [cl_26329,cl_26326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26329 v h) (hints_cons _ _ _ (der_26326 v h) (by intro d hd; cases hd)))
def cl_32072 : CNF.NClause := [(76,false),(10,true),(1,true),(8,true),(27,true),(17,true)]
theorem der_32072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32072 :=
  CNF.rup_sound cl_32072 [cl_944,cl_23664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_944 v h) (hints_cons _ _ _ (der_23664 v h) (by intro d hd; cases hd)))
def cl_32073 : CNF.NClause := [(76,false),(27,true),(1,true),(24,true),(10,true),(8,true)]
theorem der_32073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32073 :=
  CNF.rup_sound cl_32073 [cl_952,cl_23664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_952 v h) (hints_cons _ _ _ (der_23664 v h) (by intro d hd; cases hd)))
def cl_32074 : CNF.NClause := [(76,false),(24,true),(1,true),(17,true),(8,true),(27,true)]
theorem der_32074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32074 :=
  CNF.rup_sound cl_32074 [cl_956,cl_23664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_956 v h) (hints_cons _ _ _ (der_23664 v h) (by intro d hd; cases hd)))
def cl_32075 : CNF.NClause := [(76,false),(27,true),(1,true),(17,true),(24,true),(10,true)]
theorem der_32075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32075 :=
  CNF.rup_sound cl_32075 [cl_958,cl_23664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_958 v h) (hints_cons _ _ _ (der_23664 v h) (by intro d hd; cases hd)))
def cl_32076 : CNF.NClause := [(76,false),(17,true),(8,true),(27,true),(24,true),(10,true)]
theorem der_32076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32076 :=
  CNF.rup_sound cl_32076 [cl_959,cl_23664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_959 v h) (hints_cons _ _ _ (der_23664 v h) (by intro d hd; cases hd)))
def cl_32077 : CNF.NClause := [(74,false),(2,true),(6,true),(19,true),(23,true),(10,true)]
theorem der_32077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32077 :=
  CNF.rup_sound cl_32077 [cl_800,cl_23665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_800 v h) (hints_cons _ _ _ (der_23665 v h) (by intro d hd; cases hd)))
def cl_32078 : CNF.NClause := [(74,false),(10,true),(19,true),(2,true),(6,true),(29,true)]
theorem der_32078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32078 :=
  CNF.rup_sound cl_32078 [cl_816,cl_23665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_816 v h) (hints_cons _ _ _ (der_23665 v h) (by intro d hd; cases hd)))
def cl_32079 : CNF.NClause := [(74,false),(29,true),(2,true),(6,true),(19,true),(23,true)]
theorem der_32079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32079 :=
  CNF.rup_sound cl_32079 [cl_828,cl_23665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_828 v h) (hints_cons _ _ _ (der_23665 v h) (by intro d hd; cases hd)))
def cl_32080 : CNF.NClause := [(74,false),(10,true),(2,true),(19,true),(23,true),(29,true)]
theorem der_32080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32080 :=
  CNF.rup_sound cl_32080 [cl_830,cl_23665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_830 v h) (hints_cons _ _ _ (der_23665 v h) (by intro d hd; cases hd)))
def cl_32081 : CNF.NClause := [(74,false),(10,true),(19,true),(23,true),(29,true),(6,true)]
theorem der_32081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32081 :=
  CNF.rup_sound cl_32081 [cl_831,cl_23665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_831 v h) (hints_cons _ _ _ (der_23665 v h) (by intro d hd; cases hd)))
def cl_32082 : CNF.NClause := [(59,false),(70,false),(62,true),(84,false),(28,true),(90,true)]
theorem der_32082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32082 :=
  CNF.rup_sound cl_32082 [cl_26334,cl_26332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26334 v h) (hints_cons _ _ _ (der_26332 v h) (by intro d hd; cases hd)))
def cl_32083 : CNF.NClause := [(59,false),(90,true),(62,true),(81,false),(70,false),(28,true)]
theorem der_32083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32083 :=
  CNF.rup_sound cl_32083 [cl_26336,cl_26332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26336 v h) (hints_cons _ _ _ (der_26332 v h) (by intro d hd; cases hd)))
def cl_32084 : CNF.NClause := [(59,false),(90,true),(62,true),(73,false),(70,false),(28,true)]
theorem der_32084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32084 :=
  CNF.rup_sound cl_32084 [cl_26337,cl_26335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26337 v h) (hints_cons _ _ _ (der_26335 v h) (by intro d hd; cases hd)))
def cl_32085 : CNF.NClause := [(59,false),(70,false),(62,true),(81,true),(28,true),(90,true)]
theorem der_32085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32085 :=
  CNF.rup_sound cl_32085 [cl_26338,cl_32084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26338 v h) (hints_cons _ _ _ (der_32084 v h) (by intro d hd; cases hd)))
def cl_32086 : CNF.NClause := [(48,false),(83,true),(88,false),(64,false),(70,false),(17,true)]
theorem der_32086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32086 :=
  CNF.rup_sound cl_32086 [cl_26342,cl_26341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26342 v h) (hints_cons _ _ _ (der_26341 v h) (by intro d hd; cases hd)))
def cl_32087 : CNF.NClause := [(48,false),(76,true),(17,true),(64,false),(83,false),(70,false)]
theorem der_32087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32087 :=
  CNF.rup_sound cl_32087 [cl_26344,cl_26343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26344 v h) (hints_cons _ _ _ (der_26343 v h) (by intro d hd; cases hd)))
def cl_32088 : CNF.NClause := [(48,false),(64,false),(76,false),(70,false),(83,true),(17,true)]
theorem der_32088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32088 :=
  CNF.rup_sound cl_32088 [cl_26347,cl_32086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26347 v h) (hints_cons _ _ _ (der_32086 v h) (by intro d hd; cases hd)))
def cl_32089 : CNF.NClause := [(48,false),(76,true),(88,true),(64,false),(70,false),(17,true)]
theorem der_32089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32089 :=
  CNF.rup_sound cl_32089 [cl_26348,cl_26346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26348 v h) (hints_cons _ _ _ (der_26346 v h) (by intro d hd; cases hd)))
def cl_32090 : CNF.NClause := [(68,false),(8,true),(20,true),(4,true),(16,true),(12,true)]
theorem der_32090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32090 :=
  CNF.rup_sound cl_32090 [cl_416,cl_23667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_416 v h) (hints_cons _ _ _ (der_23667 v h) (by intro d hd; cases hd)))
def cl_32091 : CNF.NClause := [(68,false),(12,true),(8,true),(4,true),(29,true),(16,true)]
theorem der_32091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32091 :=
  CNF.rup_sound cl_32091 [cl_432,cl_23667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_432 v h) (hints_cons _ _ _ (der_23667 v h) (by intro d hd; cases hd)))
def cl_32092 : CNF.NClause := [(68,false),(20,true),(12,true),(8,true),(4,true),(29,true)]
theorem der_32092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32092 :=
  CNF.rup_sound cl_32092 [cl_440,cl_23667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_440 v h) (hints_cons _ _ _ (der_23667 v h) (by intro d hd; cases hd)))
def cl_32093 : CNF.NClause := [(68,false),(12,true),(20,true),(4,true),(29,true),(16,true)]
theorem der_32093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32093 :=
  CNF.rup_sound cl_32093 [cl_446,cl_23667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_446 v h) (hints_cons _ _ _ (der_23667 v h) (by intro d hd; cases hd)))
def cl_32094 : CNF.NClause := [(52,false),(67,true),(85,false),(88,false),(21,true),(66,false)]
theorem der_32094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32094 :=
  CNF.rup_sound cl_32094 [cl_26351,cl_26349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26351 v h) (hints_cons _ _ _ (der_26349 v h) (by intro d hd; cases hd)))
def cl_32095 : CNF.NClause := [(52,false),(88,false),(79,false),(66,false),(21,true),(67,true)]
theorem der_32095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32095 :=
  CNF.rup_sound cl_32095 [cl_26353,cl_26349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26353 v h) (hints_cons _ _ _ (der_26349 v h) (by intro d hd; cases hd)))
def cl_32096 : CNF.NClause := [(52,false),(73,false),(88,false),(66,false),(21,true),(67,true)]
theorem der_32096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32096 :=
  CNF.rup_sound cl_32096 [cl_26354,cl_26352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26354 v h) (hints_cons _ _ _ (der_26352 v h) (by intro d hd; cases hd)))
def cl_32097 : CNF.NClause := [(52,false),(73,true),(88,false),(66,false),(21,true),(67,true)]
theorem der_32097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32097 :=
  CNF.rup_sound cl_32097 [cl_26355,cl_32094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26355 v h) (hints_cons _ _ _ (der_32094 v h) (by intro d hd; cases hd)))
def cl_32098 : CNF.NClause := [(52,false),(85,false),(21,true),(79,false),(66,false),(67,true)]
theorem der_32098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32098 :=
  CNF.rup_sound cl_32098 [cl_26357,cl_26356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26357 v h) (hints_cons _ _ _ (der_26356 v h) (by intro d hd; cases hd)))
def cl_32099 : CNF.NClause := [(52,false),(73,false),(85,false),(66,false),(21,true),(67,true)]
theorem der_32099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32099 :=
  CNF.rup_sound cl_32099 [cl_26358,cl_26356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26358 v h) (hints_cons _ _ _ (der_26356 v h) (by intro d hd; cases hd)))
def cl_32100 : CNF.NClause := [(52,false),(67,true),(85,false),(66,false),(21,true),(88,true)]
theorem der_32100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32100 :=
  CNF.rup_sound cl_32100 [cl_26359,cl_32099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26359 v h) (hints_cons _ _ _ (der_32099 v h) (by intro d hd; cases hd)))
def cl_32101 : CNF.NClause := [(52,false),(79,false),(21,true),(66,false),(73,false),(67,true)]
theorem der_32101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32101 :=
  CNF.rup_sound cl_32101 [cl_26360,cl_32095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26360 v h) (hints_cons _ _ _ (der_32095 v h) (by intro d hd; cases hd)))
def cl_32102 : CNF.NClause := [(52,false),(21,true),(79,false),(66,false),(85,true),(67,true)]
theorem der_32102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32102 :=
  CNF.rup_sound cl_32102 [cl_26361,cl_32101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26361 v h) (hints_cons _ _ _ (der_32101 v h) (by intro d hd; cases hd)))
def cl_32103 : CNF.NClause := [(52,false),(85,true),(66,false),(73,false),(21,true),(67,true)]
theorem der_32103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32103 :=
  CNF.rup_sound cl_32103 [cl_26362,cl_32101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26362 v h) (hints_cons _ _ _ (der_32101 v h) (by intro d hd; cases hd)))
def cl_32104 : CNF.NClause := [(52,false),(67,true),(79,true),(66,false),(21,true),(88,true)]
theorem der_32104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32104 :=
  CNF.rup_sound cl_32104 [cl_26363,cl_32100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26363 v h) (hints_cons _ _ _ (der_32100 v h) (by intro d hd; cases hd)))
def cl_32105 : CNF.NClause := [(47,false),(84,false),(89,false),(66,false),(75,false),(16,true)]
theorem der_32105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32105 :=
  CNF.rup_sound cl_32105 [cl_26365,cl_26364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26365 v h) (hints_cons _ _ _ (der_26364 v h) (by intro d hd; cases hd)))
def cl_32106 : CNF.NClause := [(39,false),(90,false),(8,true),(79,false),(82,false),(76,false)]
theorem der_32106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32106 :=
  CNF.rup_sound cl_32106 [cl_26369,cl_26366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26369 v h) (hints_cons _ _ _ (der_26366 v h) (by intro d hd; cases hd)))
def cl_32107 : CNF.NClause := [(39,false),(76,true),(90,false),(79,false),(82,false),(68,false)]
theorem der_32107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32107 :=
  CNF.rup_sound cl_32107 [cl_26372,cl_26370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26372 v h) (hints_cons _ _ _ (der_26370 v h) (by intro d hd; cases hd)))
def cl_32108 : CNF.NClause := [(39,false),(82,false),(90,false),(79,false),(8,true),(65,false)]
theorem der_32108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32108 :=
  CNF.rup_sound cl_32108 [cl_26374,cl_26367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26374 v h) (hints_cons _ _ _ (der_26367 v h) (by intro d hd; cases hd)))
def cl_32109 : CNF.NClause := [(39,false),(65,true),(8,false),(90,false),(79,false),(82,false)]
theorem der_32109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32109 :=
  CNF.rup_sound cl_32109 [cl_26375,cl_26368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26375 v h) (hints_cons _ _ _ (der_26368 v h) (by intro d hd; cases hd)))
def cl_32110 : CNF.NClause := [(39,false),(68,true),(8,true),(90,false),(79,false),(82,false)]
theorem der_32110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32110 :=
  CNF.rup_sound cl_32110 [cl_26376,cl_32106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26376 v h) (hints_cons _ _ _ (der_32106 v h) (by intro d hd; cases hd)))
def cl_32111 : CNF.NClause := [(39,false),(76,false),(79,true),(90,false),(82,false),(65,false)]
theorem der_32111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32111 :=
  CNF.rup_sound cl_32111 [cl_26381,cl_26380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26381 v h) (hints_cons _ _ _ (der_26380 v h) (by intro d hd; cases hd)))
def cl_32112 : CNF.NClause := [(39,false),(90,false),(79,true),(8,false),(82,false),(76,false)]
theorem der_32112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32112 :=
  CNF.rup_sound cl_32112 [cl_26382,cl_32111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26382 v h) (hints_cons _ _ _ (der_32111 v h) (by intro d hd; cases hd)))
def cl_32113 : CNF.NClause := [(39,false),(68,true),(79,true),(90,false),(82,false),(76,false)]
theorem der_32113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32113 :=
  CNF.rup_sound cl_32113 [cl_26383,cl_32111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26383 v h) (hints_cons _ _ _ (der_32111 v h) (by intro d hd; cases hd)))
def cl_32114 : CNF.NClause := [(39,false),(68,false),(90,false),(82,false),(8,true),(65,false)]
theorem der_32114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32114 :=
  CNF.rup_sound cl_32114 [cl_26385,cl_26377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26385 v h) (hints_cons _ _ _ (der_26377 v h) (by intro d hd; cases hd)))
def cl_32115 : CNF.NClause := [(39,false),(79,true),(8,false),(90,false),(82,false),(68,false)]
theorem der_32115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32115 :=
  CNF.rup_sound cl_32115 [cl_26386,cl_32112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26386 v h) (hints_cons _ _ _ (der_32112 v h) (by intro d hd; cases hd)))
def cl_32116 : CNF.NClause := [(39,false),(68,false),(76,true),(79,true),(90,false),(82,false)]
theorem der_32116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32116 :=
  CNF.rup_sound cl_32116 [cl_26387,cl_32115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26387 v h) (hints_cons _ _ _ (der_32115 v h) (by intro d hd; cases hd)))
def cl_32118 : CNF.NClause := [(39,false),(82,false),(76,true),(90,false),(8,true),(65,false)]
theorem der_32118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32118 :=
  CNF.rup_sound cl_32118 [cl_26389,cl_32114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26389 v h) (hints_cons _ _ _ (der_32114 v h) (by intro d hd; cases hd)))
def cl_32119 : CNF.NClause := [(39,false),(76,true),(79,true),(8,false),(90,false),(82,false)]
theorem der_32119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32119 :=
  CNF.rup_sound cl_32119 [cl_26390,cl_32116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26390 v h) (hints_cons _ _ _ (der_32116 v h) (by intro d hd; cases hd)))
def cl_32120 : CNF.NClause := [(39,false),(65,true),(76,true),(79,true),(90,false),(82,false)]
theorem der_32120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32120 :=
  CNF.rup_sound cl_32120 [cl_26391,cl_32119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26391 v h) (hints_cons _ _ _ (der_32119 v h) (by intro d hd; cases hd)))
def cl_32121 : CNF.NClause := [(39,false),(68,false),(65,true),(90,false),(79,false),(76,false)]
theorem der_32121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32121 :=
  CNF.rup_sound cl_32121 [cl_26394,cl_26393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26394 v h) (hints_cons _ _ _ (der_26393 v h) (by intro d hd; cases hd)))
def cl_32122 : CNF.NClause := [(39,false),(65,false),(90,false),(79,false),(76,false),(8,true)]
theorem der_32122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32122 :=
  CNF.rup_sound cl_32122 [cl_26396,cl_26367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26396 v h) (hints_cons _ _ _ (der_26367 v h) (by intro d hd; cases hd)))
def cl_32123 : CNF.NClause := [(39,false),(90,false),(68,true),(8,true),(79,false),(76,false)]
theorem der_32123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32123 :=
  CNF.rup_sound cl_32123 [cl_26398,cl_32122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26398 v h) (hints_cons _ _ _ (der_32122 v h) (by intro d hd; cases hd)))
def cl_32124 : CNF.NClause := [(39,false),(65,false),(90,false),(79,false),(68,false),(8,true)]
theorem der_32124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32124 :=
  CNF.rup_sound cl_32124 [cl_26400,cl_32108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26400 v h) (hints_cons _ _ _ (der_32108 v h) (by intro d hd; cases hd)))
def cl_32125 : CNF.NClause := [(39,false),(76,true),(8,false),(90,false),(79,false),(68,false)]
theorem der_32125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32125 :=
  CNF.rup_sound cl_32125 [cl_26401,cl_32107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26401 v h) (hints_cons _ _ _ (der_32107 v h) (by intro d hd; cases hd)))
def cl_32126 : CNF.NClause := [(39,false),(68,false),(65,true),(90,false),(79,false),(8,true)]
theorem der_32126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32126 :=
  CNF.rup_sound cl_32126 [cl_26402,cl_32121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26402 v h) (hints_cons _ _ _ (der_32121 v h) (by intro d hd; cases hd)))
def cl_32127 : CNF.NClause := [(39,false),(76,true),(8,false),(90,false),(79,false),(65,false)]
theorem der_32127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32127 :=
  CNF.rup_sound cl_32127 [cl_26403,cl_26399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26403 v h) (hints_cons _ _ _ (der_26399 v h) (by intro d hd; cases hd)))
def cl_32128 : CNF.NClause := [(39,false),(68,true),(65,false),(90,false),(79,false),(8,true)]
theorem der_32128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32128 :=
  CNF.rup_sound cl_32128 [cl_26404,cl_32122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26404 v h) (hints_cons _ _ _ (der_32122 v h) (by intro d hd; cases hd)))
def cl_32129 : CNF.NClause := [(39,false),(76,true),(8,false),(90,false),(79,false),(82,true)]
theorem der_32129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32129 :=
  CNF.rup_sound cl_32129 [cl_26405,cl_32125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26405 v h) (hints_cons _ _ _ (der_32125 v h) (by intro d hd; cases hd)))
def cl_32130 : CNF.NClause := [(39,false),(68,true),(8,true),(90,false),(79,false),(82,true)]
theorem der_32130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32130 :=
  CNF.rup_sound cl_32130 [cl_26406,cl_32123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26406 v h) (hints_cons _ _ _ (der_32123 v h) (by intro d hd; cases hd)))
def cl_32131 : CNF.NClause := [(39,false),(90,false),(79,true),(76,false),(68,false),(65,false)]
theorem der_32131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32131 :=
  CNF.rup_sound cl_32131 [cl_26408,cl_26407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26408 v h) (hints_cons _ _ _ (der_26407 v h) (by intro d hd; cases hd)))
def cl_32132 : CNF.NClause := [(39,false),(65,true),(79,true),(90,false),(76,false),(68,false)]
theorem der_32132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32132 :=
  CNF.rup_sound cl_32132 [cl_26410,cl_26379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26410 v h) (hints_cons _ _ _ (der_26379 v h) (by intro d hd; cases hd)))
def cl_32133 : CNF.NClause := [(39,false),(65,false),(79,true),(90,false),(76,false),(8,true)]
theorem der_32133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32133 :=
  CNF.rup_sound cl_32133 [cl_26412,cl_32111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26412 v h) (hints_cons _ _ _ (der_32111 v h) (by intro d hd; cases hd)))
def cl_32135 : CNF.NClause := [(39,false),(90,false),(68,true),(8,true),(76,false),(82,true)]
theorem der_32135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32135 :=
  CNF.rup_sound cl_32135 [cl_26414,cl_32123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26414 v h) (hints_cons _ _ _ (der_32123 v h) (by intro d hd; cases hd)))
def cl_32136 : CNF.NClause := [(39,false),(68,false),(79,true),(90,false),(8,true),(65,false)]
theorem der_32136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32136 :=
  CNF.rup_sound cl_32136 [cl_26416,cl_32114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26416 v h) (hints_cons _ _ _ (der_32114 v h) (by intro d hd; cases hd)))
def cl_32138 : CNF.NClause := [(39,false),(76,true),(8,true),(79,true),(90,false),(68,false)]
theorem der_32138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32138 :=
  CNF.rup_sound cl_32138 [cl_26418,cl_32116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26418 v h) (hints_cons _ _ _ (der_32116 v h) (by intro d hd; cases hd)))
def cl_32139 : CNF.NClause := [(39,false),(76,true),(8,false),(90,false),(82,true),(65,false)]
theorem der_32139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32139 :=
  CNF.rup_sound cl_32139 [cl_26419,cl_32127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26419 v h) (hints_cons _ _ _ (der_32127 v h) (by intro d hd; cases hd)))
def cl_32140 : CNF.NClause := [(39,false),(65,false),(79,true),(90,false),(8,true),(82,true)]
theorem der_32140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32140 :=
  CNF.rup_sound cl_32140 [cl_26420,cl_32133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26420 v h) (hints_cons _ _ _ (der_32133 v h) (by intro d hd; cases hd)))
def cl_32141 : CNF.NClause := [(39,false),(76,true),(79,true),(8,false),(90,false),(82,true)]
theorem der_32141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32141 :=
  CNF.rup_sound cl_32141 [cl_26421,cl_32139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26421 v h) (hints_cons _ _ _ (der_32139 v h) (by intro d hd; cases hd)))
def cl_32142 : CNF.NClause := [(39,false),(68,true),(8,true),(65,true),(90,false),(82,true)]
theorem der_32142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32142 :=
  CNF.rup_sound cl_32142 [cl_26422,cl_32135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26422 v h) (hints_cons _ _ _ (der_32135 v h) (by intro d hd; cases hd)))
def cl_32143 : CNF.NClause := [(39,false),(79,false),(65,true),(82,false),(76,false),(68,false)]
theorem der_32143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32143 :=
  CNF.rup_sound cl_32143 [cl_26425,cl_26424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26425 v h) (hints_cons _ _ _ (der_26424 v h) (by intro d hd; cases hd)))
def cl_32144 : CNF.NClause := [(39,false),(65,true),(8,false),(79,false),(82,false),(76,false)]
theorem der_32144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32144 :=
  CNF.rup_sound cl_32144 [cl_26428,cl_32109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26428 v h) (hints_cons _ _ _ (der_32109 v h) (by intro d hd; cases hd)))
def cl_32145 : CNF.NClause := [(39,false),(65,true),(8,true),(79,false),(82,false),(76,false)]
theorem der_32145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32145 :=
  CNF.rup_sound cl_32145 [cl_26429,cl_32143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26429 v h) (hints_cons _ _ _ (der_32143 v h) (by intro d hd; cases hd)))
def cl_32146 : CNF.NClause := [(39,false),(76,true),(79,false),(82,false),(68,false),(65,false)]
theorem der_32146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32146 :=
  CNF.rup_sound cl_32146 [cl_26431,cl_32107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26431 v h) (hints_cons _ _ _ (der_32107 v h) (by intro d hd; cases hd)))
def cl_32147 : CNF.NClause := [(39,false),(65,true),(8,false),(79,false),(82,false),(68,false)]
theorem der_32147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32147 :=
  CNF.rup_sound cl_32147 [cl_26432,cl_32144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26432 v h) (hints_cons _ _ _ (der_32144 v h) (by intro d hd; cases hd)))
def cl_32148 : CNF.NClause := [(39,false),(65,true),(8,true),(79,false),(82,false),(68,false)]
theorem der_32148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32148 :=
  CNF.rup_sound cl_32148 [cl_26433,cl_32145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26433 v h) (hints_cons _ _ _ (der_32145 v h) (by intro d hd; cases hd)))
def cl_32149 : CNF.NClause := [(39,false),(8,false),(79,false),(82,false),(65,false),(90,true)]
theorem der_32149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32149 :=
  CNF.rup_sound cl_32149 [cl_26434,cl_26430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26434 v h) (hints_cons _ _ _ (der_26430 v h) (by intro d hd; cases hd)))
def cl_32150 : CNF.NClause := [(39,false),(76,true),(8,true),(79,false),(82,false),(65,false)]
theorem der_32150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32150 :=
  CNF.rup_sound cl_32150 [cl_26435,cl_32146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26435 v h) (hints_cons _ _ _ (der_32146 v h) (by intro d hd; cases hd)))
def cl_32151 : CNF.NClause := [(39,false),(68,true),(65,true),(8,false),(79,false),(82,false)]
theorem der_32151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32151 :=
  CNF.rup_sound cl_32151 [cl_26436,cl_32144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26436 v h) (hints_cons _ _ _ (der_32144 v h) (by intro d hd; cases hd)))
def cl_32152 : CNF.NClause := [(39,false),(76,true),(68,true),(8,true),(79,false),(82,false)]
theorem der_32152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32152 :=
  CNF.rup_sound cl_32152 [cl_26437,cl_32110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26437 v h) (hints_cons _ _ _ (der_32110 v h) (by intro d hd; cases hd)))
def cl_32153 : CNF.NClause := [(39,false),(65,false),(82,false),(76,false),(68,false),(8,true)]
theorem der_32153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32153 :=
  CNF.rup_sound cl_32153 [cl_26439,cl_26423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26439 v h) (hints_cons _ _ _ (der_26423 v h) (by intro d hd; cases hd)))
def cl_32154 : CNF.NClause := [(39,false),(76,false),(8,false),(82,false),(65,true),(68,false)]
theorem der_32154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32154 :=
  CNF.rup_sound cl_32154 [cl_26440,cl_32144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26440 v h) (hints_cons _ _ _ (der_32144 v h) (by intro d hd; cases hd)))
def cl_32155 : CNF.NClause := [(39,false),(90,true),(65,true),(82,false),(76,false),(68,false)]
theorem der_32155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32155 :=
  CNF.rup_sound cl_32155 [cl_26441,cl_32154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26441 v h) (hints_cons _ _ _ (der_32154 v h) (by intro d hd; cases hd)))
def cl_32156 : CNF.NClause := [(39,false),(65,false),(8,false),(82,false),(76,false),(79,true)]
theorem der_32156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32156 :=
  CNF.rup_sound cl_32156 [cl_26442,cl_32111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26442 v h) (hints_cons _ _ _ (der_32111 v h) (by intro d hd; cases hd)))
def cl_32157 : CNF.NClause := [(39,false),(65,false),(79,true),(82,false),(76,false),(8,true)]
theorem der_32157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32157 :=
  CNF.rup_sound cl_32157 [cl_26443,cl_32111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26443 v h) (hints_cons _ _ _ (der_32111 v h) (by intro d hd; cases hd)))
def cl_32159 : CNF.NClause := [(39,false),(82,false),(8,true),(65,true),(76,false),(90,true)]
theorem der_32159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32159 :=
  CNF.rup_sound cl_32159 [cl_26445,cl_32155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26445 v h) (hints_cons _ _ _ (der_32155 v h) (by intro d hd; cases hd)))
def cl_32160 : CNF.NClause := [(39,false),(79,true),(8,false),(82,false),(68,false),(65,false)]
theorem der_32160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32160 :=
  CNF.rup_sound cl_32160 [cl_26446,cl_26438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26446 v h) (hints_cons _ _ _ (der_26438 v h) (by intro d hd; cases hd)))
def cl_32161 : CNF.NClause := [(39,false),(65,false),(79,true),(82,false),(68,false),(90,true)]
theorem der_32161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32161 :=
  CNF.rup_sound cl_32161 [cl_26447,cl_32160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26447 v h) (hints_cons _ _ _ (der_32160 v h) (by intro d hd; cases hd)))
def cl_32162 : CNF.NClause := [(39,false),(65,true),(8,false),(82,false),(68,false),(90,true)]
theorem der_32162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32162 :=
  CNF.rup_sound cl_32162 [cl_26448,cl_32154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26448 v h) (hints_cons _ _ _ (der_32154 v h) (by intro d hd; cases hd)))
def cl_32163 : CNF.NClause := [(39,false),(76,true),(65,true),(79,true),(82,false),(68,false)]
theorem der_32163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32163 :=
  CNF.rup_sound cl_32163 [cl_26449,cl_32120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26449 v h) (hints_cons _ _ _ (der_32120 v h) (by intro d hd; cases hd)))
def cl_32164 : CNF.NClause := [(39,false),(76,true),(79,true),(8,false),(82,false),(65,false)]
theorem der_32164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32164 :=
  CNF.rup_sound cl_32164 [cl_26450,cl_32119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26450 v h) (hints_cons _ _ _ (der_32119 v h) (by intro d hd; cases hd)))
def cl_32165 : CNF.NClause := [(39,false),(65,false),(68,true),(76,true),(82,false),(8,true)]
theorem der_32165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32165 :=
  CNF.rup_sound cl_32165 [cl_26451,cl_32118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26451 v h) (hints_cons _ _ _ (der_32118 v h) (by intro d hd; cases hd)))
def cl_32167 : CNF.NClause := [(39,false),(68,false),(79,false),(76,false),(8,true),(65,false)]
theorem der_32167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32167 :=
  CNF.rup_sound cl_32167 [cl_26455,cl_32122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26455 v h) (hints_cons _ _ _ (der_32122 v h) (by intro d hd; cases hd)))
def cl_32168 : CNF.NClause := [(39,false),(65,true),(8,false),(79,false),(76,false),(68,false)]
theorem der_32168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32168 :=
  CNF.rup_sound cl_32168 [cl_26456,cl_32147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26456 v h) (hints_cons _ _ _ (der_32147 v h) (by intro d hd; cases hd)))
def cl_32169 : CNF.NClause := [(39,false),(79,false),(65,true),(76,false),(82,true),(68,false)]
theorem der_32169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32169 :=
  CNF.rup_sound cl_32169 [cl_26457,cl_32168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26457 v h) (hints_cons _ _ _ (der_32168 v h) (by intro d hd; cases hd)))
def cl_32170 : CNF.NClause := [(39,false),(68,true),(8,false),(79,false),(76,false),(65,false)]
theorem der_32170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32170 :=
  CNF.rup_sound cl_32170 [cl_26458,cl_26395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26458 v h) (hints_cons _ _ _ (der_26395 v h) (by intro d hd; cases hd)))
def cl_32171 : CNF.NClause := [(39,false),(79,false),(8,true),(76,false),(65,false),(90,true)]
theorem der_32171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32171 :=
  CNF.rup_sound cl_32171 [cl_26459,cl_32167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26459 v h) (hints_cons _ _ _ (der_32167 v h) (by intro d hd; cases hd)))
def cl_32172 : CNF.NClause := [(39,false),(68,true),(65,true),(8,false),(79,false),(76,false)]
theorem der_32172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32172 :=
  CNF.rup_sound cl_32172 [cl_26460,cl_32151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26460 v h) (hints_cons _ _ _ (der_32151 v h) (by intro d hd; cases hd)))
def cl_32173 : CNF.NClause := [(39,false),(79,false),(8,true),(76,false),(82,true),(90,true)]
theorem der_32173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32173 :=
  CNF.rup_sound cl_32173 [cl_26461,cl_32171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26461 v h) (hints_cons _ _ _ (der_32171 v h) (by intro d hd; cases hd)))
def cl_32174 : CNF.NClause := [(39,false),(90,true),(79,false),(68,false),(65,false),(8,false)]
theorem der_32174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32174 :=
  CNF.rup_sound cl_32174 [cl_26462,cl_26430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26462 v h) (hints_cons _ _ _ (der_26430 v h) (by intro d hd; cases hd)))
def cl_32175 : CNF.NClause := [(39,false),(76,true),(65,false),(79,false),(68,false),(8,true)]
theorem der_32175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32175 :=
  CNF.rup_sound cl_32175 [cl_26463,cl_32146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26463 v h) (hints_cons _ _ _ (der_32146 v h) (by intro d hd; cases hd)))
def cl_32176 : CNF.NClause := [(39,false),(76,true),(65,true),(8,false),(79,false),(68,false)]
theorem der_32176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32176 :=
  CNF.rup_sound cl_32176 [cl_26464,cl_32147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26464 v h) (hints_cons _ _ _ (der_32147 v h) (by intro d hd; cases hd)))
def cl_32177 : CNF.NClause := [(39,false),(76,true),(8,true),(79,false),(82,true),(68,false)]
theorem der_32177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32177 :=
  CNF.rup_sound cl_32177 [cl_26465,cl_32175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26465 v h) (hints_cons _ _ _ (der_32175 v h) (by intro d hd; cases hd)))
def cl_32178 : CNF.NClause := [(39,false),(68,true),(8,false),(79,false),(65,false),(90,true)]
theorem der_32178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32178 :=
  CNF.rup_sound cl_32178 [cl_26466,cl_32170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26466 v h) (hints_cons _ _ _ (der_32170 v h) (by intro d hd; cases hd)))
def cl_32179 : CNF.NClause := [(39,false),(76,true),(68,true),(8,true),(79,false),(65,false)]
theorem der_32179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32179 :=
  CNF.rup_sound cl_32179 [cl_26467,cl_32152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26467 v h) (hints_cons _ _ _ (der_32152 v h) (by intro d hd; cases hd)))
def cl_32181 : CNF.NClause := [(39,false),(76,true),(68,true),(8,true),(65,true),(79,false)]
theorem der_32181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32181 :=
  CNF.rup_sound cl_32181 [cl_26469,cl_32152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26469 v h) (hints_cons _ _ _ (der_32152 v h) (by intro d hd; cases hd)))
def cl_32182 : CNF.NClause := [(39,false),(76,false),(8,false),(79,true),(68,false),(65,false)]
theorem der_32182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32182 :=
  CNF.rup_sound cl_32182 [cl_26470,cl_26407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26470 v h) (hints_cons _ _ _ (der_26407 v h) (by intro d hd; cases hd)))
def cl_32183 : CNF.NClause := [(39,false),(76,false),(8,true),(68,false),(65,false),(90,true)]
theorem der_32183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32183 :=
  CNF.rup_sound cl_32183 [cl_26471,cl_32153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26471 v h) (hints_cons _ _ _ (der_32153 v h) (by intro d hd; cases hd)))
def cl_32184 : CNF.NClause := [(39,false),(65,true),(8,true),(76,false),(82,true),(68,false)]
theorem der_32184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32184 :=
  CNF.rup_sound cl_32184 [cl_26473,cl_32169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26473 v h) (hints_cons _ _ _ (der_32169 v h) (by intro d hd; cases hd)))
def cl_32185 : CNF.NClause := [(39,false),(65,false),(8,false),(76,false),(79,true),(90,true)]
theorem der_32185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32185 :=
  CNF.rup_sound cl_32185 [cl_26474,cl_32156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26474 v h) (hints_cons _ _ _ (der_32156 v h) (by intro d hd; cases hd)))
def cl_32186 : CNF.NClause := [(39,false),(65,false),(76,false),(82,true),(8,true),(90,true)]
theorem der_32186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32186 :=
  CNF.rup_sound cl_32186 [cl_26475,cl_32183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26475 v h) (hints_cons _ _ _ (der_32183 v h) (by intro d hd; cases hd)))
def cl_32188 : CNF.NClause := [(39,false),(79,true),(8,false),(68,false),(65,false),(90,true)]
theorem der_32188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32188 :=
  CNF.rup_sound cl_32188 [cl_26478,cl_32160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26478 v h) (hints_cons _ _ _ (der_32160 v h) (by intro d hd; cases hd)))
def cl_32189 : CNF.NClause := [(39,false),(68,false),(76,true),(82,true),(8,true),(65,false)]
theorem der_32189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32189 :=
  CNF.rup_sound cl_32189 [cl_26479,cl_32177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26479 v h) (hints_cons _ _ _ (der_32177 v h) (by intro d hd; cases hd)))
def cl_32190 : CNF.NClause := [(39,false),(76,true),(79,true),(8,false),(68,false),(90,true)]
theorem der_32190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32190 :=
  CNF.rup_sound cl_32190 [cl_26480,cl_32188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26480 v h) (hints_cons _ _ _ (der_32188 v h) (by intro d hd; cases hd)))
def cl_32191 : CNF.NClause := [(39,false),(76,true),(65,true),(79,true),(68,false),(90,true)]
theorem der_32191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32191 :=
  CNF.rup_sound cl_32191 [cl_26481,cl_32190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26481 v h) (hints_cons _ _ _ (der_32190 v h) (by intro d hd; cases hd)))
def cl_32192 : CNF.NClause := [(39,false),(76,true),(79,true),(8,false),(82,true),(65,false)]
theorem der_32192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32192 :=
  CNF.rup_sound cl_32192 [cl_26482,cl_32139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26482 v h) (hints_cons _ _ _ (der_32139 v h) (by intro d hd; cases hd)))
def cl_32193 : CNF.NClause := [(39,false),(65,false),(68,true),(76,true),(8,true),(90,true)]
theorem der_32193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32193 :=
  CNF.rup_sound cl_32193 [cl_26483,cl_32179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26483 v h) (hints_cons _ _ _ (der_32179 v h) (by intro d hd; cases hd)))
def cl_32194 : CNF.NClause := [(37,false),(91,false),(66,true),(78,false),(82,false),(74,false)]
theorem der_32194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32194 :=
  CNF.rup_sound cl_32194 [cl_26490,cl_26487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26490 v h) (hints_cons _ _ _ (der_26487 v h) (by intro d hd; cases hd)))
def cl_32195 : CNF.NClause := [(37,false),(66,true),(91,false),(78,false),(82,false),(70,false)]
theorem der_32195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32195 :=
  CNF.rup_sound cl_32195 [cl_26493,cl_32194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26493 v h) (hints_cons _ _ _ (der_32194 v h) (by intro d hd; cases hd)))
def cl_32199 : CNF.NClause := [(37,false),(82,false),(6,true),(91,false),(74,false),(70,false)]
theorem der_32199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32199 :=
  CNF.rup_sound cl_32199 [cl_26500,cl_26498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26500 v h) (hints_cons _ _ _ (der_26498 v h) (by intro d hd; cases hd)))
def cl_32200 : CNF.NClause := [(37,false),(82,false),(91,false),(6,true),(66,false),(74,false)]
theorem der_32200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32200 :=
  CNF.rup_sound cl_32200 [cl_26502,cl_32199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26502 v h) (hints_cons _ _ _ (der_32199 v h) (by intro d hd; cases hd)))
def cl_32201 : CNF.NClause := [(37,false),(91,false),(6,true),(66,true),(82,false),(74,false)]
theorem der_32201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32201 :=
  CNF.rup_sound cl_32201 [cl_26504,cl_32194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26504 v h) (hints_cons _ _ _ (der_32194 v h) (by intro d hd; cases hd)))
def cl_32202 : CNF.NClause := [(37,false),(70,false),(78,true),(91,false),(82,false),(66,false)]
theorem der_32202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32202 :=
  CNF.rup_sound cl_32202 [cl_26506,cl_26505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26506 v h) (hints_cons _ _ _ (der_26505 v h) (by intro d hd; cases hd)))
def cl_32203 : CNF.NClause := [(37,false),(66,true),(91,false),(82,false),(6,false),(70,false)]
theorem der_32203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32203 :=
  CNF.rup_sound cl_32203 [cl_26507,cl_26499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26507 v h) (hints_cons _ _ _ (der_26499 v h) (by intro d hd; cases hd)))
def cl_32204 : CNF.NClause := [(37,false),(70,false),(78,true),(91,false),(6,true),(82,false)]
theorem der_32204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32204 :=
  CNF.rup_sound cl_32204 [cl_26508,cl_32199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26508 v h) (hints_cons _ _ _ (der_32199 v h) (by intro d hd; cases hd)))
def cl_32205 : CNF.NClause := [(37,false),(70,true),(91,false),(82,false),(66,false),(6,false)]
theorem der_32205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32205 :=
  CNF.rup_sound cl_32205 [cl_26509,cl_26501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26509 v h) (hints_cons _ _ _ (der_26501 v h) (by intro d hd; cases hd)))
def cl_32206 : CNF.NClause := [(37,false),(82,false),(78,true),(91,false),(6,true),(66,false)]
theorem der_32206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32206 :=
  CNF.rup_sound cl_32206 [cl_26510,cl_32200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26510 v h) (hints_cons _ _ _ (der_32200 v h) (by intro d hd; cases hd)))
def cl_32207 : CNF.NClause := [(37,false),(70,true),(78,true),(91,false),(82,false),(6,false)]
theorem der_32207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32207 :=
  CNF.rup_sound cl_32207 [cl_26511,cl_26503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26511 v h) (hints_cons _ _ _ (der_26503 v h) (by intro d hd; cases hd)))
def cl_32208 : CNF.NClause := [(37,false),(82,false),(70,true),(66,true),(6,true),(91,false)]
theorem der_32208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32208 :=
  CNF.rup_sound cl_32208 [cl_26512,cl_32201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26512 v h) (hints_cons _ _ _ (der_32201 v h) (by intro d hd; cases hd)))
def cl_32209 : CNF.NClause := [(37,false),(74,false),(91,false),(78,false),(6,true),(70,false)]
theorem der_32209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32209 :=
  CNF.rup_sound cl_32209 [cl_26513,cl_26330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26513 v h) (hints_cons _ _ _ (der_26330 v h) (by intro d hd; cases hd)))
def cl_32210 : CNF.NClause := [(37,false),(91,false),(66,true),(78,false),(74,false),(70,false)]
theorem der_32210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32210 :=
  CNF.rup_sound cl_32210 [cl_26514,cl_32209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26514 v h) (hints_cons _ _ _ (der_32209 v h) (by intro d hd; cases hd)))
def cl_32211 : CNF.NClause := [(37,false),(74,false),(70,true),(91,false),(78,false),(66,false)]
theorem der_32211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32211 :=
  CNF.rup_sound cl_32211 [cl_26516,cl_26515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26516 v h) (hints_cons _ _ _ (der_26515 v h) (by intro d hd; cases hd)))
def cl_32212 : CNF.NClause := [(37,false),(66,true),(91,false),(78,false),(6,false),(74,false)]
theorem der_32212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32212 :=
  CNF.rup_sound cl_32212 [cl_26517,cl_32210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26517 v h) (hints_cons _ _ _ (der_32210 v h) (by intro d hd; cases hd)))
def cl_32213 : CNF.NClause := [(37,false),(66,true),(91,false),(78,false),(74,false),(6,true)]
theorem der_32213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32213 :=
  CNF.rup_sound cl_32213 [cl_26518,cl_32194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26518 v h) (hints_cons _ _ _ (der_32194 v h) (by intro d hd; cases hd)))
def cl_32214 : CNF.NClause := [(37,false),(78,false),(6,true),(91,false),(66,false),(70,false)]
theorem der_32214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32214 :=
  CNF.rup_sound cl_32214 [cl_26520,cl_26491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26520 v h) (hints_cons _ _ _ (der_26491 v h) (by intro d hd; cases hd)))
def cl_32215 : CNF.NClause := [(37,false),(66,true),(91,false),(78,false),(6,false),(70,false)]
theorem der_32215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32215 :=
  CNF.rup_sound cl_32215 [cl_26521,cl_32210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26521 v h) (hints_cons _ _ _ (der_32210 v h) (by intro d hd; cases hd)))
def cl_32216 : CNF.NClause := [(37,false),(70,false),(91,false),(78,false),(82,true),(6,true)]
theorem der_32216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32216 :=
  CNF.rup_sound cl_32216 [cl_26522,cl_32209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26522 v h) (hints_cons _ _ _ (der_32209 v h) (by intro d hd; cases hd)))
def cl_32217 : CNF.NClause := [(37,false),(70,true),(91,false),(78,false),(66,false),(6,false)]
theorem der_32217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32217 :=
  CNF.rup_sound cl_32217 [cl_26523,cl_26515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26523 v h) (hints_cons _ _ _ (der_26515 v h) (by intro d hd; cases hd)))
def cl_32218 : CNF.NClause := [(37,false),(91,false),(70,true),(78,false),(66,false),(82,true)]
theorem der_32218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32218 :=
  CNF.rup_sound cl_32218 [cl_26524,cl_32211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26524 v h) (hints_cons _ _ _ (der_32211 v h) (by intro d hd; cases hd)))
def cl_32219 : CNF.NClause := [(37,false),(74,true),(66,true),(91,false),(78,false),(6,false)]
theorem der_32219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32219 :=
  CNF.rup_sound cl_32219 [cl_26525,cl_32215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26525 v h) (hints_cons _ _ _ (der_32215 v h) (by intro d hd; cases hd)))
def cl_32220 : CNF.NClause := [(37,false),(74,true),(70,true),(66,true),(91,false),(78,false)]
theorem der_32220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32220 :=
  CNF.rup_sound cl_32220 [cl_26526,cl_32219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26526 v h) (hints_cons _ _ _ (der_32219 v h) (by intro d hd; cases hd)))
def cl_32221 : CNF.NClause := [(37,false),(70,false),(91,false),(66,false),(74,false),(6,true)]
theorem der_32221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32221 :=
  CNF.rup_sound cl_32221 [cl_26528,cl_32209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26528 v h) (hints_cons _ _ _ (der_32209 v h) (by intro d hd; cases hd)))
def cl_32222 : CNF.NClause := [(37,false),(66,true),(91,false),(74,false),(82,true),(70,false)]
theorem der_32222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32222 :=
  CNF.rup_sound cl_32222 [cl_26530,cl_32210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26530 v h) (hints_cons _ _ _ (der_32210 v h) (by intro d hd; cases hd)))
def cl_32223 : CNF.NClause := [(37,false),(70,true),(91,false),(66,false),(74,false),(82,true)]
theorem der_32223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32223 :=
  CNF.rup_sound cl_32223 [cl_26532,cl_32218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26532 v h) (hints_cons _ _ _ (der_32218 v h) (by intro d hd; cases hd)))
def cl_32224 : CNF.NClause := [(37,false),(78,true),(91,false),(6,false),(74,false),(82,true)]
theorem der_32224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32224 :=
  CNF.rup_sound cl_32224 [cl_26533,cl_26529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26533 v h) (hints_cons _ _ _ (der_26529 v h) (by intro d hd; cases hd)))
def cl_32225 : CNF.NClause := [(37,false),(70,true),(82,true),(91,false),(74,false),(6,true)]
theorem der_32225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32225 :=
  CNF.rup_sound cl_32225 [cl_26534,cl_32223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26534 v h) (hints_cons _ _ _ (der_32223 v h) (by intro d hd; cases hd)))
def cl_32226 : CNF.NClause := [(37,false),(91,false),(66,false),(6,false),(82,true),(70,false)]
theorem der_32226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32226 :=
  CNF.rup_sound cl_32226 [cl_26535,cl_26519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26535 v h) (hints_cons _ _ _ (der_26519 v h) (by intro d hd; cases hd)))
def cl_32227 : CNF.NClause := [(37,false),(74,true),(78,true),(91,false),(66,false),(70,false)]
theorem der_32227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32227 :=
  CNF.rup_sound cl_32227 [cl_26536,cl_32202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26536 v h) (hints_cons _ _ _ (der_32202 v h) (by intro d hd; cases hd)))
def cl_32228 : CNF.NClause := [(37,false),(74,true),(66,true),(91,false),(6,false),(70,false)]
theorem der_32228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32228 :=
  CNF.rup_sound cl_32228 [cl_26537,cl_32203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26537 v h) (hints_cons _ _ _ (der_32203 v h) (by intro d hd; cases hd)))
def cl_32229 : CNF.NClause := [(37,false),(70,false),(78,true),(66,true),(91,false),(6,true)]
theorem der_32229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32229 :=
  CNF.rup_sound cl_32229 [cl_26538,cl_32204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26538 v h) (hints_cons _ _ _ (der_32204 v h) (by intro d hd; cases hd)))
def cl_32231 : CNF.NClause := [(37,false),(70,true),(78,true),(91,false),(66,false),(82,true)]
theorem der_32231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32231 :=
  CNF.rup_sound cl_32231 [cl_26540,cl_32223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26540 v h) (hints_cons _ _ _ (der_32223 v h) (by intro d hd; cases hd)))
def cl_32232 : CNF.NClause := [(37,false),(70,true),(78,true),(91,false),(6,false),(82,true)]
theorem der_32232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32232 :=
  CNF.rup_sound cl_32232 [cl_26541,cl_32224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26541 v h) (hints_cons _ _ _ (der_32224 v h) (by intro d hd; cases hd)))
def cl_32233 : CNF.NClause := [(37,false),(91,false),(74,true),(66,true),(70,true),(82,true)]
theorem der_32233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32233 :=
  CNF.rup_sound cl_32233 [cl_26542,cl_32220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26542 v h) (hints_cons _ _ _ (der_32220 v h) (by intro d hd; cases hd)))
def cl_32234 : CNF.NClause := [(37,false),(78,false),(6,true),(82,false),(74,false),(70,false)]
theorem der_32234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32234 :=
  CNF.rup_sound cl_32234 [cl_26545,cl_26543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26545 v h) (hints_cons _ _ _ (der_26543 v h) (by intro d hd; cases hd)))
def cl_32235 : CNF.NClause := [(37,false),(78,false),(70,true),(82,false),(66,false),(74,false)]
theorem der_32235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32235 :=
  CNF.rup_sound cl_32235 [cl_26547,cl_32211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26547 v h) (hints_cons _ _ _ (der_32211 v h) (by intro d hd; cases hd)))
def cl_32236 : CNF.NClause := [(37,false),(70,true),(78,false),(82,false),(6,false),(74,false)]
theorem der_32236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32236 :=
  CNF.rup_sound cl_32236 [cl_26548,cl_26546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26548 v h) (hints_cons _ _ _ (der_26546 v h) (by intro d hd; cases hd)))
def cl_32237 : CNF.NClause := [(37,false),(78,false),(66,true),(6,true),(82,false),(74,false)]
theorem der_32237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32237 :=
  CNF.rup_sound cl_32237 [cl_26549,cl_32213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26549 v h) (hints_cons _ _ _ (der_32213 v h) (by intro d hd; cases hd)))
def cl_32238 : CNF.NClause := [(37,false),(74,true),(78,false),(82,false),(6,false),(70,false)]
theorem der_32238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32238 :=
  CNF.rup_sound cl_32238 [cl_26552,cl_26550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26552 v h) (hints_cons _ _ _ (der_26550 v h) (by intro d hd; cases hd)))
def cl_32239 : CNF.NClause := [(37,false),(78,false),(6,true),(66,true),(82,false),(70,false)]
theorem der_32239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32239 :=
  CNF.rup_sound cl_32239 [cl_26553,cl_32195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26553 v h) (hints_cons _ _ _ (der_32195 v h) (by intro d hd; cases hd)))
def cl_32240 : CNF.NClause := [(37,false),(78,false),(70,true),(6,true),(82,false),(66,false)]
theorem der_32240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32240 :=
  CNF.rup_sound cl_32240 [cl_26555,cl_32235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26555 v h) (hints_cons _ _ _ (der_32235 v h) (by intro d hd; cases hd)))
def cl_32241 : CNF.NClause := [(37,false),(70,true),(66,true),(78,false),(82,false),(6,false)]
theorem der_32241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32241 :=
  CNF.rup_sound cl_32241 [cl_26556,cl_32236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26556 v h) (hints_cons _ _ _ (der_32236 v h) (by intro d hd; cases hd)))
def cl_32242 : CNF.NClause := [(37,false),(74,true),(6,true),(66,true),(78,false),(82,false)]
theorem der_32242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32242 :=
  CNF.rup_sound cl_32242 [cl_26557,cl_32239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26557 v h) (hints_cons _ _ _ (der_32239 v h) (by intro d hd; cases hd)))
def cl_32243 : CNF.NClause := [(37,false),(82,false),(6,true),(66,false),(74,false),(70,false)]
theorem der_32243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32243 :=
  CNF.rup_sound cl_32243 [cl_26559,cl_32221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26559 v h) (hints_cons _ _ _ (der_32221 v h) (by intro d hd; cases hd)))
def cl_32244 : CNF.NClause := [(37,false),(82,false),(66,true),(6,false),(74,false),(70,false)]
theorem der_32244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32244 :=
  CNF.rup_sound cl_32244 [cl_26560,cl_32203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26560 v h) (hints_cons _ _ _ (der_32203 v h) (by intro d hd; cases hd)))
def cl_32245 : CNF.NClause := [(37,false),(82,false),(66,true),(74,false),(70,false),(91,true)]
theorem der_32245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32245 :=
  CNF.rup_sound cl_32245 [cl_26561,cl_32244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26561 v h) (hints_cons _ _ _ (der_32244 v h) (by intro d hd; cases hd)))
def cl_32246 : CNF.NClause := [(37,false),(6,true),(70,true),(82,false),(66,false),(74,false)]
theorem der_32246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32246 :=
  CNF.rup_sound cl_32246 [cl_26563,cl_32240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26563 v h) (hints_cons _ _ _ (der_32240 v h) (by intro d hd; cases hd)))
def cl_32248 : CNF.NClause := [(37,false),(78,true),(82,false),(66,false),(6,false),(70,false)]
theorem der_32248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32248 :=
  CNF.rup_sound cl_32248 [cl_26566,cl_26505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26566 v h) (hints_cons _ _ _ (der_26505 v h) (by intro d hd; cases hd)))
def cl_32250 : CNF.NClause := [(37,false),(74,true),(82,false),(6,false),(70,false),(91,true)]
theorem der_32250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32250 :=
  CNF.rup_sound cl_32250 [cl_26568,cl_32238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26568 v h) (hints_cons _ _ _ (der_32238 v h) (by intro d hd; cases hd)))
def cl_32251 : CNF.NClause := [(37,false),(70,false),(74,true),(78,true),(82,false),(6,true)]
theorem der_32251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32251 :=
  CNF.rup_sound cl_32251 [cl_26569,cl_32204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26569 v h) (hints_cons _ _ _ (der_32204 v h) (by intro d hd; cases hd)))
def cl_32255 : CNF.NClause := [(37,false),(82,false),(74,true),(78,true),(6,true),(91,true)]
theorem der_32255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32255 :=
  CNF.rup_sound cl_32255 [cl_26573,cl_32251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26573 v h) (hints_cons _ _ _ (der_32251 v h) (by intro d hd; cases hd)))
def cl_32256 : CNF.NClause := [(37,false),(78,false),(6,true),(66,false),(74,false),(70,false)]
theorem der_32256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32256 :=
  CNF.rup_sound cl_32256 [cl_26575,cl_26543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26575 v h) (hints_cons _ _ _ (der_26543 v h) (by intro d hd; cases hd)))
def cl_32257 : CNF.NClause := [(37,false),(78,false),(66,true),(6,false),(74,false),(70,false)]
theorem der_32257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32257 :=
  CNF.rup_sound cl_32257 [cl_26576,cl_32210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26576 v h) (hints_cons _ _ _ (der_32210 v h) (by intro d hd; cases hd)))
def cl_32258 : CNF.NClause := [(37,false),(74,false),(78,false),(66,true),(82,true),(70,false)]
theorem der_32258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32258 :=
  CNF.rup_sound cl_32258 [cl_26577,cl_32210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26577 v h) (hints_cons _ _ _ (der_32210 v h) (by intro d hd; cases hd)))
def cl_32259 : CNF.NClause := [(37,false),(78,false),(66,false),(6,false),(74,false),(70,true)]
theorem der_32259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32259 :=
  CNF.rup_sound cl_32259 [cl_26578,cl_32217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26578 v h) (hints_cons _ _ _ (der_32217 v h) (by intro d hd; cases hd)))
def cl_32260 : CNF.NClause := [(37,false),(78,false),(66,false),(74,false),(82,true),(70,true)]
theorem der_32260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32260 :=
  CNF.rup_sound cl_32260 [cl_26579,cl_32218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26579 v h) (hints_cons _ _ _ (der_32218 v h) (by intro d hd; cases hd)))
def cl_32261 : CNF.NClause := [(37,false),(78,false),(70,true),(6,false),(74,false),(91,true)]
theorem der_32261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32261 :=
  CNF.rup_sound cl_32261 [cl_26580,cl_32236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26580 v h) (hints_cons _ _ _ (der_32236 v h) (by intro d hd; cases hd)))
def cl_32263 : CNF.NClause := [(37,false),(78,false),(66,false),(6,false),(82,true),(70,false)]
theorem der_32263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32263 :=
  CNF.rup_sound cl_32263 [cl_26582,cl_26519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26582 v h) (hints_cons _ _ _ (der_26519 v h) (by intro d hd; cases hd)))
def cl_32264 : CNF.NClause := [(37,false),(70,false),(78,false),(66,false),(82,true),(6,true)]
theorem der_32264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32264 :=
  CNF.rup_sound cl_32264 [cl_26583,cl_32256] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26583 v h) (hints_cons _ _ _ (der_32256 v h) (by intro d hd; cases hd)))
def cl_32265 : CNF.NClause := [(37,false),(66,true),(78,false),(6,false),(82,true),(70,false)]
theorem der_32265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32265 :=
  CNF.rup_sound cl_32265 [cl_26584,cl_32258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26584 v h) (hints_cons _ _ _ (der_32258 v h) (by intro d hd; cases hd)))
def cl_32266 : CNF.NClause := [(37,false),(66,true),(78,false),(82,true),(70,false),(91,true)]
theorem der_32266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32266 :=
  CNF.rup_sound cl_32266 [cl_26585,cl_32258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26585 v h) (hints_cons _ _ _ (der_32258 v h) (by intro d hd; cases hd)))
def cl_32268 : CNF.NClause := [(37,false),(70,true),(78,false),(66,false),(82,true),(91,true)]
theorem der_32268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32268 :=
  CNF.rup_sound cl_32268 [cl_26587,cl_32260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26587 v h) (hints_cons _ _ _ (der_32260 v h) (by intro d hd; cases hd)))
def cl_32269 : CNF.NClause := [(37,false),(70,true),(78,false),(6,false),(82,true),(91,true)]
theorem der_32269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32269 :=
  CNF.rup_sound cl_32269 [cl_26588,cl_32261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26588 v h) (hints_cons _ _ _ (der_32261 v h) (by intro d hd; cases hd)))
def cl_32270 : CNF.NClause := [(37,false),(66,true),(70,true),(78,false),(82,true),(91,true)]
theorem der_32270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32270 :=
  CNF.rup_sound cl_32270 [cl_26589,cl_32269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26589 v h) (hints_cons _ _ _ (der_32269 v h) (by intro d hd; cases hd)))
def cl_32271 : CNF.NClause := [(37,false),(66,false),(6,false),(74,false),(82,true),(70,false)]
theorem der_32271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32271 :=
  CNF.rup_sound cl_32271 [cl_26590,cl_26574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26590 v h) (hints_cons _ _ _ (der_26574 v h) (by intro d hd; cases hd)))
def cl_32272 : CNF.NClause := [(37,false),(66,true),(6,false),(74,false),(82,true),(70,false)]
theorem der_32272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32272 :=
  CNF.rup_sound cl_32272 [cl_26592,cl_32257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26592 v h) (hints_cons _ _ _ (der_32257 v h) (by intro d hd; cases hd)))
def cl_32273 : CNF.NClause := [(37,false),(70,false),(66,true),(74,false),(82,true),(6,true)]
theorem der_32273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32273 :=
  CNF.rup_sound cl_32273 [cl_26593,cl_32258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26593 v h) (hints_cons _ _ _ (der_32258 v h) (by intro d hd; cases hd)))
def cl_32274 : CNF.NClause := [(37,false),(70,true),(66,false),(6,false),(74,false),(82,true)]
theorem der_32274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32274 :=
  CNF.rup_sound cl_32274 [cl_26594,cl_32260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26594 v h) (hints_cons _ _ _ (der_32260 v h) (by intro d hd; cases hd)))
def cl_32275 : CNF.NClause := [(37,false),(70,true),(6,false),(74,false),(82,true),(91,true)]
theorem der_32275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32275 :=
  CNF.rup_sound cl_32275 [cl_26596,cl_32274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26596 v h) (hints_cons _ _ _ (der_32274 v h) (by intro d hd; cases hd)))
def cl_32276 : CNF.NClause := [(37,false),(91,true),(70,true),(66,true),(74,false),(82,true)]
theorem der_32276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32276 :=
  CNF.rup_sound cl_32276 [cl_26597,cl_32275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26597 v h) (hints_cons _ _ _ (der_32275 v h) (by intro d hd; cases hd)))
def cl_32277 : CNF.NClause := [(37,false),(74,true),(78,true),(66,false),(6,false),(70,false)]
theorem der_32277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32277 :=
  CNF.rup_sound cl_32277 [cl_26598,cl_32227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26598 v h) (hints_cons _ _ _ (der_32227 v h) (by intro d hd; cases hd)))
def cl_32278 : CNF.NClause := [(37,false),(70,false),(74,true),(78,true),(66,false),(6,true)]
theorem der_32278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32278 :=
  CNF.rup_sound cl_32278 [cl_26599,cl_32251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26599 v h) (hints_cons _ _ _ (der_32251 v h) (by intro d hd; cases hd)))
def cl_32279 : CNF.NClause := [(37,false),(74,true),(66,true),(6,false),(82,true),(70,false)]
theorem der_32279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32279 :=
  CNF.rup_sound cl_32279 [cl_26600,cl_32228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26600 v h) (hints_cons _ _ _ (der_32228 v h) (by intro d hd; cases hd)))
def cl_32280 : CNF.NClause := [(37,false),(70,false),(78,true),(66,true),(82,true),(6,true)]
theorem der_32280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32280 :=
  CNF.rup_sound cl_32280 [cl_26601,cl_32229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26601 v h) (hints_cons _ _ _ (der_32229 v h) (by intro d hd; cases hd)))
def cl_32281 : CNF.NClause := [(37,false),(91,true),(74,true),(78,true),(66,false),(6,false)]
theorem der_32281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32281 :=
  CNF.rup_sound cl_32281 [cl_26602,cl_32277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26602 v h) (hints_cons _ _ _ (der_32277 v h) (by intro d hd; cases hd)))
def cl_32282 : CNF.NClause := [(37,false),(91,true),(70,true),(74,true),(78,true),(66,false)]
theorem der_32282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32282 :=
  CNF.rup_sound cl_32282 [cl_26603,cl_32281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26603 v h) (hints_cons _ _ _ (der_32281 v h) (by intro d hd; cases hd)))
def cl_32284 : CNF.NClause := [(37,false),(91,true),(70,true),(74,true),(78,true),(6,true)]
theorem der_32284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32284 :=
  CNF.rup_sound cl_32284 [cl_26605,cl_32282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26605 v h) (hints_cons _ _ _ (der_32282 v h) (by intro d hd; cases hd)))
def cl_32285 : CNF.NClause := [(36,false),(86,false),(92,false),(85,false),(5,true),(83,false)]
theorem der_32285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32285 :=
  CNF.rup_sound cl_32285 [cl_26613,cl_26611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26613 v h) (hints_cons _ _ _ (der_26611 v h) (by intro d hd; cases hd)))
def cl_32286 : CNF.NClause := [(36,false),(85,false),(92,false),(5,true),(82,false),(86,false)]
theorem der_32286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32286 :=
  CNF.rup_sound cl_32286 [cl_26615,cl_26611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26615 v h) (hints_cons _ _ _ (der_26611 v h) (by intro d hd; cases hd)))
def cl_32287 : CNF.NClause := [(36,false),(84,true),(5,false),(92,false),(85,false),(86,false)]
theorem der_32287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32287 :=
  CNF.rup_sound cl_32287 [cl_26616,cl_26614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26616 v h) (hints_cons _ _ _ (der_26614 v h) (by intro d hd; cases hd)))
def cl_32288 : CNF.NClause := [(36,false),(85,false),(92,false),(5,true),(86,false),(83,true)]
theorem der_32288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32288 :=
  CNF.rup_sound cl_32288 [cl_26617,cl_32286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26617 v h) (hints_cons _ _ _ (der_32286 v h) (by intro d hd; cases hd)))
def cl_32289 : CNF.NClause := [(36,false),(86,false),(92,false),(5,true),(82,false),(84,false)]
theorem der_32289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32289 :=
  CNF.rup_sound cl_32289 [cl_26622,cl_32286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26622 v h) (hints_cons _ _ _ (der_32286 v h) (by intro d hd; cases hd)))
def cl_32290 : CNF.NClause := [(36,false),(86,false),(5,false),(92,false),(84,false),(85,true)]
theorem der_32290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32290 :=
  CNF.rup_sound cl_32290 [cl_26623,cl_26621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26623 v h) (hints_cons _ _ _ (der_26621 v h) (by intro d hd; cases hd)))
def cl_32291 : CNF.NClause := [(36,false),(86,false),(92,false),(5,true),(84,false),(83,true)]
theorem der_32291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32291 :=
  CNF.rup_sound cl_32291 [cl_26624,cl_32289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26624 v h) (hints_cons _ _ _ (der_32289 v h) (by intro d hd; cases hd)))
def cl_32292 : CNF.NClause := [(36,false),(82,false),(5,true),(92,false),(86,false),(83,false)]
theorem der_32292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32292 :=
  CNF.rup_sound cl_32292 [cl_26626,cl_32286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26626 v h) (hints_cons _ _ _ (der_32286 v h) (by intro d hd; cases hd)))
def cl_32293 : CNF.NClause := [(36,false),(82,false),(5,false),(92,false),(86,false),(85,true)]
theorem der_32293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32293 :=
  CNF.rup_sound cl_32293 [cl_26629,cl_26621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26629 v h) (hints_cons _ _ _ (der_26621 v h) (by intro d hd; cases hd)))
def cl_32295 : CNF.NClause := [(36,false),(5,false),(92,false),(86,false),(85,true),(82,true)]
theorem der_32295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32295 :=
  CNF.rup_sound cl_32295 [cl_26631,cl_32290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26631 v h) (hints_cons _ _ _ (der_32290 v h) (by intro d hd; cases hd)))
def cl_32296 : CNF.NClause := [(36,false),(84,true),(92,false),(86,false),(85,true),(82,true)]
theorem der_32296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32296 :=
  CNF.rup_sound cl_32296 [cl_26632,cl_26628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26632 v h) (hints_cons _ _ _ (der_26628 v h) (by intro d hd; cases hd)))
def cl_32297 : CNF.NClause := [(36,false),(85,false),(92,false),(86,true),(82,false),(84,false)]
theorem der_32297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32297 :=
  CNF.rup_sound cl_32297 [cl_26637,cl_26633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26637 v h) (hints_cons _ _ _ (der_26633 v h) (by intro d hd; cases hd)))
def cl_32298 : CNF.NClause := [(36,false),(92,false),(86,true),(5,false),(85,false),(84,false)]
theorem der_32298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32298 :=
  CNF.rup_sound cl_32298 [cl_26638,cl_32297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26638 v h) (hints_cons _ _ _ (der_32297 v h) (by intro d hd; cases hd)))
def cl_32299 : CNF.NClause := [(36,false),(85,false),(92,false),(5,true),(84,false),(82,true)]
theorem der_32299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32299 :=
  CNF.rup_sound cl_32299 [cl_26639,cl_26635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26639 v h) (hints_cons _ _ _ (der_26635 v h) (by intro d hd; cases hd)))
def cl_32300 : CNF.NClause := [(36,false),(92,false),(5,true),(85,false),(82,false),(83,false)]
theorem der_32300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32300 :=
  CNF.rup_sound cl_32300 [cl_26641,cl_32286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26641 v h) (hints_cons _ _ _ (der_32286 v h) (by intro d hd; cases hd)))
def cl_32301 : CNF.NClause := [(36,false),(5,false),(86,true),(92,false),(85,false),(82,false)]
theorem der_32301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32301 :=
  CNF.rup_sound cl_32301 [cl_26644,cl_32298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26644 v h) (hints_cons _ _ _ (der_32298 v h) (by intro d hd; cases hd)))
def cl_32302 : CNF.NClause := [(36,false),(92,false),(86,true),(85,false),(82,false),(83,true)]
theorem der_32302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32302 :=
  CNF.rup_sound cl_32302 [cl_26645,cl_32297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26645 v h) (hints_cons _ _ _ (der_32297 v h) (by intro d hd; cases hd)))
def chunk018 : List CNF.NClause := [cl_31736,cl_31737,cl_31738,cl_31739,cl_31740,cl_31741,cl_31743,cl_31744,cl_31745,cl_31746,cl_31747,cl_31748,cl_31749,cl_31750,cl_31751,cl_31752,cl_31753,cl_31754,cl_31755,cl_31756,cl_31757,cl_31758,cl_31759,cl_31761,cl_31762,cl_31763,cl_31764,cl_31765,cl_31766,cl_31767,cl_31768,cl_31769,cl_31770,cl_31771,cl_31772,cl_31773,cl_31774,cl_31775,cl_31776,cl_31777,cl_31778,cl_31779,cl_31780,cl_31781,cl_31782,cl_31783,cl_31784,cl_31785,cl_31788,cl_31789,cl_31790,cl_31791,cl_31792,cl_31793,cl_31795,cl_31796,cl_31797,cl_31798,cl_31799,cl_31800,cl_31801,cl_31802,cl_31803,cl_31804,cl_31805,cl_31806,cl_31807,cl_31810,cl_31814,cl_31815,cl_31816,cl_31817,cl_31818,cl_31819,cl_31821,cl_31822,cl_31823,cl_31824,cl_31825,cl_31826,cl_31827,cl_31828,cl_31829,cl_31830,cl_31831,cl_31834,cl_31836,cl_31837,cl_31838,cl_31839,cl_31840,cl_31841,cl_31842,cl_31843,cl_31844,cl_31845,cl_31847,cl_31848,cl_31849,cl_31850,cl_31851,cl_31852,cl_31853,cl_31854,cl_31855,cl_31856,cl_31857,cl_31858,cl_31859,cl_31860,cl_31863,cl_31864,cl_31865,cl_31866,cl_31867,cl_31868,cl_31869,cl_31870,cl_31871,cl_31872,cl_31873,cl_31874,cl_31875,cl_31876,cl_31877,cl_31878,cl_31879,cl_31880,cl_31881,cl_31882,cl_31883,cl_31884,cl_31885,cl_31886,cl_31887,cl_31888,cl_31889,cl_31890,cl_31891,cl_31892,cl_31893,cl_31894,cl_31895,cl_31904,cl_31908,cl_31911,cl_31912,cl_31913,cl_31914,cl_31915,cl_31916,cl_31917,cl_31918,cl_31919,cl_31920,cl_31921,cl_31922,cl_31924,cl_31925,cl_31926,cl_31927,cl_31928,cl_31929,cl_31930,cl_31931,cl_31932,cl_31933,cl_31934,cl_31935,cl_31936,cl_31937,cl_31938,cl_31939,cl_31940,cl_31941,cl_31942,cl_31943,cl_31944,cl_31945,cl_31946,cl_31947,cl_31948,cl_31949,cl_31950,cl_31951,cl_31952,cl_31953,cl_31954,cl_31955,cl_31956,cl_31957,cl_31958,cl_31959,cl_31960,cl_31961,cl_31962,cl_31963,cl_31964,cl_31965,cl_31966,cl_31967,cl_31968,cl_31969,cl_31970,cl_31971,cl_31972,cl_31974,cl_31975,cl_31976,cl_31977,cl_31978,cl_31979,cl_31980,cl_31981,cl_31982,cl_31983,cl_31984,cl_31985,cl_31986,cl_31987,cl_31988,cl_31989,cl_31990,cl_31991,cl_31992,cl_31993,cl_31994,cl_31995,cl_31997,cl_31998,cl_31999,cl_32000,cl_32001,cl_32002,cl_32003,cl_32004,cl_32005,cl_32006,cl_32007,cl_32008,cl_32009,cl_32010,cl_32011,cl_32012,cl_32013,cl_32014,cl_32015,cl_32016,cl_32017,cl_32018,cl_32019,cl_32020,cl_32021,cl_32023,cl_32025,cl_32026,cl_32027,cl_32028,cl_32029,cl_32030,cl_32031,cl_32032,cl_32034,cl_32035,cl_32036,cl_32037,cl_32038,cl_32040,cl_32041,cl_32042,cl_32044,cl_32054,cl_32055,cl_32056,cl_32057,cl_32058,cl_32059,cl_32060,cl_32061,cl_32062,cl_32063,cl_32064,cl_32065,cl_32066,cl_32067,cl_32068,cl_32069,cl_32070,cl_32071,cl_32072,cl_32073,cl_32074,cl_32075,cl_32076,cl_32077,cl_32078,cl_32079,cl_32080,cl_32081,cl_32082,cl_32083,cl_32084,cl_32085,cl_32086,cl_32087,cl_32088,cl_32089,cl_32090,cl_32091,cl_32092,cl_32093,cl_32094,cl_32095,cl_32096,cl_32097,cl_32098,cl_32099,cl_32100,cl_32101,cl_32102,cl_32103,cl_32104,cl_32105,cl_32106,cl_32107,cl_32108,cl_32109,cl_32110,cl_32111,cl_32112,cl_32113,cl_32114,cl_32115,cl_32116,cl_32118,cl_32119,cl_32120,cl_32121,cl_32122,cl_32123,cl_32124,cl_32125,cl_32126,cl_32127,cl_32128,cl_32129,cl_32130,cl_32131,cl_32132,cl_32133,cl_32135,cl_32136,cl_32138,cl_32139,cl_32140,cl_32141,cl_32142,cl_32143,cl_32144,cl_32145,cl_32146,cl_32147,cl_32148,cl_32149,cl_32150,cl_32151,cl_32152,cl_32153,cl_32154,cl_32155,cl_32156,cl_32157,cl_32159,cl_32160,cl_32161,cl_32162,cl_32163,cl_32164,cl_32165,cl_32167,cl_32168,cl_32169,cl_32170,cl_32171,cl_32172,cl_32173,cl_32174,cl_32175,cl_32176,cl_32177,cl_32178,cl_32179,cl_32181,cl_32182,cl_32183,cl_32184,cl_32185,cl_32186,cl_32188,cl_32189,cl_32190,cl_32191,cl_32192,cl_32193,cl_32194,cl_32195,cl_32199,cl_32200,cl_32201,cl_32202,cl_32203,cl_32204,cl_32205,cl_32206,cl_32207,cl_32208,cl_32209,cl_32210,cl_32211,cl_32212,cl_32213,cl_32214,cl_32215,cl_32216,cl_32217,cl_32218,cl_32219,cl_32220,cl_32221,cl_32222,cl_32223,cl_32224,cl_32225,cl_32226,cl_32227,cl_32228,cl_32229,cl_32231,cl_32232,cl_32233,cl_32234,cl_32235,cl_32236,cl_32237,cl_32238,cl_32239,cl_32240,cl_32241,cl_32242,cl_32243,cl_32244,cl_32245,cl_32246,cl_32248,cl_32250,cl_32251,cl_32255,cl_32256,cl_32257,cl_32258,cl_32259,cl_32260,cl_32261,cl_32263,cl_32264,cl_32265,cl_32266,cl_32268,cl_32269,cl_32270,cl_32271,cl_32272,cl_32273,cl_32274,cl_32275,cl_32276,cl_32277,cl_32278,cl_32279,cl_32280,cl_32281,cl_32282,cl_32284,cl_32285,cl_32286,cl_32287,cl_32288,cl_32289,cl_32290,cl_32291,cl_32292,cl_32293,cl_32295,cl_32296,cl_32297,cl_32298,cl_32299,cl_32300,cl_32301,cl_32302]
theorem chunk_sound018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk018, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_31736 v h) (hints_cons _ _ _ (der_31737 v h) (hints_cons _ _ _ (der_31738 v h) (hints_cons _ _ _ (der_31739 v h) (hints_cons _ _ _ (der_31740 v h) (hints_cons _ _ _ (der_31741 v h) (hints_cons _ _ _ (der_31743 v h) (hints_cons _ _ _ (der_31744 v h) (hints_cons _ _ _ (der_31745 v h) (hints_cons _ _ _ (der_31746 v h) (hints_cons _ _ _ (der_31747 v h) (hints_cons _ _ _ (der_31748 v h) (hints_cons _ _ _ (der_31749 v h) (hints_cons _ _ _ (der_31750 v h) (hints_cons _ _ _ (der_31751 v h) (hints_cons _ _ _ (der_31752 v h) (hints_cons _ _ _ (der_31753 v h) (hints_cons _ _ _ (der_31754 v h) (hints_cons _ _ _ (der_31755 v h) (hints_cons _ _ _ (der_31756 v h) (hints_cons _ _ _ (der_31757 v h) (hints_cons _ _ _ (der_31758 v h) (hints_cons _ _ _ (der_31759 v h) (hints_cons _ _ _ (der_31761 v h) (hints_cons _ _ _ (der_31762 v h) (hints_cons _ _ _ (der_31763 v h) (hints_cons _ _ _ (der_31764 v h) (hints_cons _ _ _ (der_31765 v h) (hints_cons _ _ _ (der_31766 v h) (hints_cons _ _ _ (der_31767 v h) (hints_cons _ _ _ (der_31768 v h) (hints_cons _ _ _ (der_31769 v h) (hints_cons _ _ _ (der_31770 v h) (hints_cons _ _ _ (der_31771 v h) (hints_cons _ _ _ (der_31772 v h) (hints_cons _ _ _ (der_31773 v h) (hints_cons _ _ _ (der_31774 v h) (hints_cons _ _ _ (der_31775 v h) (hints_cons _ _ _ (der_31776 v h) (hints_cons _ _ _ (der_31777 v h) (hints_cons _ _ _ (der_31778 v h) (hints_cons _ _ _ (der_31779 v h) (hints_cons _ _ _ (der_31780 v h) (hints_cons _ _ _ (der_31781 v h) (hints_cons _ _ _ (der_31782 v h) (hints_cons _ _ _ (der_31783 v h) (hints_cons _ _ _ (der_31784 v h) (hints_cons _ _ _ (der_31785 v h) (hints_cons _ _ _ (der_31788 v h) (hints_cons _ _ _ (der_31789 v h) (hints_cons _ _ _ (der_31790 v h) (hints_cons _ _ _ (der_31791 v h) (hints_cons _ _ _ (der_31792 v h) (hints_cons _ _ _ (der_31793 v h) (hints_cons _ _ _ (der_31795 v h) (hints_cons _ _ _ (der_31796 v h) (hints_cons _ _ _ (der_31797 v h) (hints_cons _ _ _ (der_31798 v h) (hints_cons _ _ _ (der_31799 v h) (hints_cons _ _ _ (der_31800 v h) (hints_cons _ _ _ (der_31801 v h) (hints_cons _ _ _ (der_31802 v h) (hints_cons _ _ _ (der_31803 v h) (hints_cons _ _ _ (der_31804 v h) (hints_cons _ _ _ (der_31805 v h) (hints_cons _ _ _ (der_31806 v h) (hints_cons _ _ _ (der_31807 v h) (hints_cons _ _ _ (der_31810 v h) (hints_cons _ _ _ (der_31814 v h) (hints_cons _ _ _ (der_31815 v h) (hints_cons _ _ _ (der_31816 v h) (hints_cons _ _ _ (der_31817 v h) (hints_cons _ _ _ (der_31818 v h) (hints_cons _ _ _ (der_31819 v h) (hints_cons _ _ _ (der_31821 v h) (hints_cons _ _ _ (der_31822 v h) (hints_cons _ _ _ (der_31823 v h) (hints_cons _ _ _ (der_31824 v h) (hints_cons _ _ _ (der_31825 v h) (hints_cons _ _ _ (der_31826 v h) (hints_cons _ _ _ (der_31827 v h) (hints_cons _ _ _ (der_31828 v h) (hints_cons _ _ _ (der_31829 v h) (hints_cons _ _ _ (der_31830 v h) (hints_cons _ _ _ (der_31831 v h) (hints_cons _ _ _ (der_31834 v h) (hints_cons _ _ _ (der_31836 v h) (hints_cons _ _ _ (der_31837 v h) (hints_cons _ _ _ (der_31838 v h) (hints_cons _ _ _ (der_31839 v h) (hints_cons _ _ _ (der_31840 v h) (hints_cons _ _ _ (der_31841 v h) (hints_cons _ _ _ (der_31842 v h) (hints_cons _ _ _ (der_31843 v h) (hints_cons _ _ _ (der_31844 v h) (hints_cons _ _ _ (der_31845 v h) (hints_cons _ _ _ (der_31847 v h) (hints_cons _ _ _ (der_31848 v h) (hints_cons _ _ _ (der_31849 v h) (hints_cons _ _ _ (der_31850 v h) (hints_cons _ _ _ (der_31851 v h) (hints_cons _ _ _ (der_31852 v h) (hints_cons _ _ _ (der_31853 v h) (hints_cons _ _ _ (der_31854 v h) (hints_cons _ _ _ (der_31855 v h) (hints_cons _ _ _ (der_31856 v h) (hints_cons _ _ _ (der_31857 v h) (hints_cons _ _ _ (der_31858 v h) (hints_cons _ _ _ (der_31859 v h) (hints_cons _ _ _ (der_31860 v h) (hints_cons _ _ _ (der_31863 v h) (hints_cons _ _ _ (der_31864 v h) (hints_cons _ _ _ (der_31865 v h) (hints_cons _ _ _ (der_31866 v h) (hints_cons _ _ _ (der_31867 v h) (hints_cons _ _ _ (der_31868 v h) (hints_cons _ _ _ (der_31869 v h) (hints_cons _ _ _ (der_31870 v h) (hints_cons _ _ _ (der_31871 v h) (hints_cons _ _ _ (der_31872 v h) (hints_cons _ _ _ (der_31873 v h) (hints_cons _ _ _ (der_31874 v h) (hints_cons _ _ _ (der_31875 v h) (hints_cons _ _ _ (der_31876 v h) (hints_cons _ _ _ (der_31877 v h) (hints_cons _ _ _ (der_31878 v h) (hints_cons _ _ _ (der_31879 v h) (hints_cons _ _ _ (der_31880 v h) (hints_cons _ _ _ (der_31881 v h) (hints_cons _ _ _ (der_31882 v h) (hints_cons _ _ _ (der_31883 v h) (hints_cons _ _ _ (der_31884 v h) (hints_cons _ _ _ (der_31885 v h) (hints_cons _ _ _ (der_31886 v h) (hints_cons _ _ _ (der_31887 v h) (hints_cons _ _ _ (der_31888 v h) (hints_cons _ _ _ (der_31889 v h) (hints_cons _ _ _ (der_31890 v h) (hints_cons _ _ _ (der_31891 v h) (hints_cons _ _ _ (der_31892 v h) (hints_cons _ _ _ (der_31893 v h) (hints_cons _ _ _ (der_31894 v h) (hints_cons _ _ _ (der_31895 v h) (hints_cons _ _ _ (der_31904 v h) (hints_cons _ _ _ (der_31908 v h) (hints_cons _ _ _ (der_31911 v h) (hints_cons _ _ _ (der_31912 v h) (hints_cons _ _ _ (der_31913 v h) (hints_cons _ _ _ (der_31914 v h) (hints_cons _ _ _ (der_31915 v h) (hints_cons _ _ _ (der_31916 v h) (hints_cons _ _ _ (der_31917 v h) (hints_cons _ _ _ (der_31918 v h) (hints_cons _ _ _ (der_31919 v h) (hints_cons _ _ _ (der_31920 v h) (hints_cons _ _ _ (der_31921 v h) (hints_cons _ _ _ (der_31922 v h) (hints_cons _ _ _ (der_31924 v h) (hints_cons _ _ _ (der_31925 v h) (hints_cons _ _ _ (der_31926 v h) (hints_cons _ _ _ (der_31927 v h) (hints_cons _ _ _ (der_31928 v h) (hints_cons _ _ _ (der_31929 v h) (hints_cons _ _ _ (der_31930 v h) (hints_cons _ _ _ (der_31931 v h) (hints_cons _ _ _ (der_31932 v h) (hints_cons _ _ _ (der_31933 v h) (hints_cons _ _ _ (der_31934 v h) (hints_cons _ _ _ (der_31935 v h) (hints_cons _ _ _ (der_31936 v h) (hints_cons _ _ _ (der_31937 v h) (hints_cons _ _ _ (der_31938 v h) (hints_cons _ _ _ (der_31939 v h) (hints_cons _ _ _ (der_31940 v h) (hints_cons _ _ _ (der_31941 v h) (hints_cons _ _ _ (der_31942 v h) (hints_cons _ _ _ (der_31943 v h) (hints_cons _ _ _ (der_31944 v h) (hints_cons _ _ _ (der_31945 v h) (hints_cons _ _ _ (der_31946 v h) (hints_cons _ _ _ (der_31947 v h) (hints_cons _ _ _ (der_31948 v h) (hints_cons _ _ _ (der_31949 v h) (hints_cons _ _ _ (der_31950 v h) (hints_cons _ _ _ (der_31951 v h) (hints_cons _ _ _ (der_31952 v h) (hints_cons _ _ _ (der_31953 v h) (hints_cons _ _ _ (der_31954 v h) (hints_cons _ _ _ (der_31955 v h) (hints_cons _ _ _ (der_31956 v h) (hints_cons _ _ _ (der_31957 v h) (hints_cons _ _ _ (der_31958 v h) (hints_cons _ _ _ (der_31959 v h) (hints_cons _ _ _ (der_31960 v h) (hints_cons _ _ _ (der_31961 v h) (hints_cons _ _ _ (der_31962 v h) (hints_cons _ _ _ (der_31963 v h) (hints_cons _ _ _ (der_31964 v h) (hints_cons _ _ _ (der_31965 v h) (hints_cons _ _ _ (der_31966 v h) (hints_cons _ _ _ (der_31967 v h) (hints_cons _ _ _ (der_31968 v h) (hints_cons _ _ _ (der_31969 v h) (hints_cons _ _ _ (der_31970 v h) (hints_cons _ _ _ (der_31971 v h) (hints_cons _ _ _ (der_31972 v h) (hints_cons _ _ _ (der_31974 v h) (hints_cons _ _ _ (der_31975 v h) (hints_cons _ _ _ (der_31976 v h) (hints_cons _ _ _ (der_31977 v h) (hints_cons _ _ _ (der_31978 v h) (hints_cons _ _ _ (der_31979 v h) (hints_cons _ _ _ (der_31980 v h) (hints_cons _ _ _ (der_31981 v h) (hints_cons _ _ _ (der_31982 v h) (hints_cons _ _ _ (der_31983 v h) (hints_cons _ _ _ (der_31984 v h) (hints_cons _ _ _ (der_31985 v h) (hints_cons _ _ _ (der_31986 v h) (hints_cons _ _ _ (der_31987 v h) (hints_cons _ _ _ (der_31988 v h) (hints_cons _ _ _ (der_31989 v h) (hints_cons _ _ _ (der_31990 v h) (hints_cons _ _ _ (der_31991 v h) (hints_cons _ _ _ (der_31992 v h) (hints_cons _ _ _ (der_31993 v h) (hints_cons _ _ _ (der_31994 v h) (hints_cons _ _ _ (der_31995 v h) (hints_cons _ _ _ (der_31997 v h) (hints_cons _ _ _ (der_31998 v h) (hints_cons _ _ _ (der_31999 v h) (hints_cons _ _ _ (der_32000 v h) (hints_cons _ _ _ (der_32001 v h) (hints_cons _ _ _ (der_32002 v h) (hints_cons _ _ _ (der_32003 v h) (hints_cons _ _ _ (der_32004 v h) (hints_cons _ _ _ (der_32005 v h) (hints_cons _ _ _ (der_32006 v h) (hints_cons _ _ _ (der_32007 v h) (hints_cons _ _ _ (der_32008 v h) (hints_cons _ _ _ (der_32009 v h) (hints_cons _ _ _ (der_32010 v h) (hints_cons _ _ _ (der_32011 v h) (hints_cons _ _ _ (der_32012 v h) (hints_cons _ _ _ (der_32013 v h) (hints_cons _ _ _ (der_32014 v h) (hints_cons _ _ _ (der_32015 v h) (hints_cons _ _ _ (der_32016 v h) (hints_cons _ _ _ (der_32017 v h) (hints_cons _ _ _ (der_32018 v h) (hints_cons _ _ _ (der_32019 v h) (hints_cons _ _ _ (der_32020 v h) (hints_cons _ _ _ (der_32021 v h) (hints_cons _ _ _ (der_32023 v h) (hints_cons _ _ _ (der_32025 v h) (hints_cons _ _ _ (der_32026 v h) (hints_cons _ _ _ (der_32027 v h) (hints_cons _ _ _ (der_32028 v h) (hints_cons _ _ _ (der_32029 v h) (hints_cons _ _ _ (der_32030 v h) (hints_cons _ _ _ (der_32031 v h) (hints_cons _ _ _ (der_32032 v h) (hints_cons _ _ _ (der_32034 v h) (hints_cons _ _ _ (der_32035 v h) (hints_cons _ _ _ (der_32036 v h) (hints_cons _ _ _ (der_32037 v h) (hints_cons _ _ _ (der_32038 v h) (hints_cons _ _ _ (der_32040 v h) (hints_cons _ _ _ (der_32041 v h) (hints_cons _ _ _ (der_32042 v h) (hints_cons _ _ _ (der_32044 v h) (hints_cons _ _ _ (der_32054 v h) (hints_cons _ _ _ (der_32055 v h) (hints_cons _ _ _ (der_32056 v h) (hints_cons _ _ _ (der_32057 v h) (hints_cons _ _ _ (der_32058 v h) (hints_cons _ _ _ (der_32059 v h) (hints_cons _ _ _ (der_32060 v h) (hints_cons _ _ _ (der_32061 v h) (hints_cons _ _ _ (der_32062 v h) (hints_cons _ _ _ (der_32063 v h) (hints_cons _ _ _ (der_32064 v h) (hints_cons _ _ _ (der_32065 v h) (hints_cons _ _ _ (der_32066 v h) (hints_cons _ _ _ (der_32067 v h) (hints_cons _ _ _ (der_32068 v h) (hints_cons _ _ _ (der_32069 v h) (hints_cons _ _ _ (der_32070 v h) (hints_cons _ _ _ (der_32071 v h) (hints_cons _ _ _ (der_32072 v h) (hints_cons _ _ _ (der_32073 v h) (hints_cons _ _ _ (der_32074 v h) (hints_cons _ _ _ (der_32075 v h) (hints_cons _ _ _ (der_32076 v h) (hints_cons _ _ _ (der_32077 v h) (hints_cons _ _ _ (der_32078 v h) (hints_cons _ _ _ (der_32079 v h) (hints_cons _ _ _ (der_32080 v h) (hints_cons _ _ _ (der_32081 v h) (hints_cons _ _ _ (der_32082 v h) (hints_cons _ _ _ (der_32083 v h) (hints_cons _ _ _ (der_32084 v h) (hints_cons _ _ _ (der_32085 v h) (hints_cons _ _ _ (der_32086 v h) (hints_cons _ _ _ (der_32087 v h) (hints_cons _ _ _ (der_32088 v h) (hints_cons _ _ _ (der_32089 v h) (hints_cons _ _ _ (der_32090 v h) (hints_cons _ _ _ (der_32091 v h) (hints_cons _ _ _ (der_32092 v h) (hints_cons _ _ _ (der_32093 v h) (hints_cons _ _ _ (der_32094 v h) (hints_cons _ _ _ (der_32095 v h) (hints_cons _ _ _ (der_32096 v h) (hints_cons _ _ _ (der_32097 v h) (hints_cons _ _ _ (der_32098 v h) (hints_cons _ _ _ (der_32099 v h) (hints_cons _ _ _ (der_32100 v h) (hints_cons _ _ _ (der_32101 v h) (hints_cons _ _ _ (der_32102 v h) (hints_cons _ _ _ (der_32103 v h) (hints_cons _ _ _ (der_32104 v h) (hints_cons _ _ _ (der_32105 v h) (hints_cons _ _ _ (der_32106 v h) (hints_cons _ _ _ (der_32107 v h) (hints_cons _ _ _ (der_32108 v h) (hints_cons _ _ _ (der_32109 v h) (hints_cons _ _ _ (der_32110 v h) (hints_cons _ _ _ (der_32111 v h) (hints_cons _ _ _ (der_32112 v h) (hints_cons _ _ _ (der_32113 v h) (hints_cons _ _ _ (der_32114 v h) (hints_cons _ _ _ (der_32115 v h) (hints_cons _ _ _ (der_32116 v h) (hints_cons _ _ _ (der_32118 v h) (hints_cons _ _ _ (der_32119 v h) (hints_cons _ _ _ (der_32120 v h) (hints_cons _ _ _ (der_32121 v h) (hints_cons _ _ _ (der_32122 v h) (hints_cons _ _ _ (der_32123 v h) (hints_cons _ _ _ (der_32124 v h) (hints_cons _ _ _ (der_32125 v h) (hints_cons _ _ _ (der_32126 v h) (hints_cons _ _ _ (der_32127 v h) (hints_cons _ _ _ (der_32128 v h) (hints_cons _ _ _ (der_32129 v h) (hints_cons _ _ _ (der_32130 v h) (hints_cons _ _ _ (der_32131 v h) (hints_cons _ _ _ (der_32132 v h) (hints_cons _ _ _ (der_32133 v h) (hints_cons _ _ _ (der_32135 v h) (hints_cons _ _ _ (der_32136 v h) (hints_cons _ _ _ (der_32138 v h) (hints_cons _ _ _ (der_32139 v h) (hints_cons _ _ _ (der_32140 v h) (hints_cons _ _ _ (der_32141 v h) (hints_cons _ _ _ (der_32142 v h) (hints_cons _ _ _ (der_32143 v h) (hints_cons _ _ _ (der_32144 v h) (hints_cons _ _ _ (der_32145 v h) (hints_cons _ _ _ (der_32146 v h) (hints_cons _ _ _ (der_32147 v h) (hints_cons _ _ _ (der_32148 v h) (hints_cons _ _ _ (der_32149 v h) (hints_cons _ _ _ (der_32150 v h) (hints_cons _ _ _ (der_32151 v h) (hints_cons _ _ _ (der_32152 v h) (hints_cons _ _ _ (der_32153 v h) (hints_cons _ _ _ (der_32154 v h) (hints_cons _ _ _ (der_32155 v h) (hints_cons _ _ _ (der_32156 v h) (hints_cons _ _ _ (der_32157 v h) (hints_cons _ _ _ (der_32159 v h) (hints_cons _ _ _ (der_32160 v h) (hints_cons _ _ _ (der_32161 v h) (hints_cons _ _ _ (der_32162 v h) (hints_cons _ _ _ (der_32163 v h) (hints_cons _ _ _ (der_32164 v h) (hints_cons _ _ _ (der_32165 v h) (hints_cons _ _ _ (der_32167 v h) (hints_cons _ _ _ (der_32168 v h) (hints_cons _ _ _ (der_32169 v h) (hints_cons _ _ _ (der_32170 v h) (hints_cons _ _ _ (der_32171 v h) (hints_cons _ _ _ (der_32172 v h) (hints_cons _ _ _ (der_32173 v h) (hints_cons _ _ _ (der_32174 v h) (hints_cons _ _ _ (der_32175 v h) (hints_cons _ _ _ (der_32176 v h) (hints_cons _ _ _ (der_32177 v h) (hints_cons _ _ _ (der_32178 v h) (hints_cons _ _ _ (der_32179 v h) (hints_cons _ _ _ (der_32181 v h) (hints_cons _ _ _ (der_32182 v h) (hints_cons _ _ _ (der_32183 v h) (hints_cons _ _ _ (der_32184 v h) (hints_cons _ _ _ (der_32185 v h) (hints_cons _ _ _ (der_32186 v h) (hints_cons _ _ _ (der_32188 v h) (hints_cons _ _ _ (der_32189 v h) (hints_cons _ _ _ (der_32190 v h) (hints_cons _ _ _ (der_32191 v h) (hints_cons _ _ _ (der_32192 v h) (hints_cons _ _ _ (der_32193 v h) (hints_cons _ _ _ (der_32194 v h) (hints_cons _ _ _ (der_32195 v h) (hints_cons _ _ _ (der_32199 v h) (hints_cons _ _ _ (der_32200 v h) (hints_cons _ _ _ (der_32201 v h) (hints_cons _ _ _ (der_32202 v h) (hints_cons _ _ _ (der_32203 v h) (hints_cons _ _ _ (der_32204 v h) (hints_cons _ _ _ (der_32205 v h) (hints_cons _ _ _ (der_32206 v h) (hints_cons _ _ _ (der_32207 v h) (hints_cons _ _ _ (der_32208 v h) (hints_cons _ _ _ (der_32209 v h) (hints_cons _ _ _ (der_32210 v h) (hints_cons _ _ _ (der_32211 v h) (hints_cons _ _ _ (der_32212 v h) (hints_cons _ _ _ (der_32213 v h) (hints_cons _ _ _ (der_32214 v h) (hints_cons _ _ _ (der_32215 v h) (hints_cons _ _ _ (der_32216 v h) (hints_cons _ _ _ (der_32217 v h) (hints_cons _ _ _ (der_32218 v h) (hints_cons _ _ _ (der_32219 v h) (hints_cons _ _ _ (der_32220 v h) (hints_cons _ _ _ (der_32221 v h) (hints_cons _ _ _ (der_32222 v h) (hints_cons _ _ _ (der_32223 v h) (hints_cons _ _ _ (der_32224 v h) (hints_cons _ _ _ (der_32225 v h) (hints_cons _ _ _ (der_32226 v h) (hints_cons _ _ _ (der_32227 v h) (hints_cons _ _ _ (der_32228 v h) (hints_cons _ _ _ (der_32229 v h) (hints_cons _ _ _ (der_32231 v h) (hints_cons _ _ _ (der_32232 v h) (hints_cons _ _ _ (der_32233 v h) (hints_cons _ _ _ (der_32234 v h) (hints_cons _ _ _ (der_32235 v h) (hints_cons _ _ _ (der_32236 v h) (hints_cons _ _ _ (der_32237 v h) (hints_cons _ _ _ (der_32238 v h) (hints_cons _ _ _ (der_32239 v h) (hints_cons _ _ _ (der_32240 v h) (hints_cons _ _ _ (der_32241 v h) (hints_cons _ _ _ (der_32242 v h) (hints_cons _ _ _ (der_32243 v h) (hints_cons _ _ _ (der_32244 v h) (hints_cons _ _ _ (der_32245 v h) (hints_cons _ _ _ (der_32246 v h) (hints_cons _ _ _ (der_32248 v h) (hints_cons _ _ _ (der_32250 v h) (hints_cons _ _ _ (der_32251 v h) (hints_cons _ _ _ (der_32255 v h) (hints_cons _ _ _ (der_32256 v h) (hints_cons _ _ _ (der_32257 v h) (hints_cons _ _ _ (der_32258 v h) (hints_cons _ _ _ (der_32259 v h) (hints_cons _ _ _ (der_32260 v h) (hints_cons _ _ _ (der_32261 v h) (hints_cons _ _ _ (der_32263 v h) (hints_cons _ _ _ (der_32264 v h) (hints_cons _ _ _ (der_32265 v h) (hints_cons _ _ _ (der_32266 v h) (hints_cons _ _ _ (der_32268 v h) (hints_cons _ _ _ (der_32269 v h) (hints_cons _ _ _ (der_32270 v h) (hints_cons _ _ _ (der_32271 v h) (hints_cons _ _ _ (der_32272 v h) (hints_cons _ _ _ (der_32273 v h) (hints_cons _ _ _ (der_32274 v h) (hints_cons _ _ _ (der_32275 v h) (hints_cons _ _ _ (der_32276 v h) (hints_cons _ _ _ (der_32277 v h) (hints_cons _ _ _ (der_32278 v h) (hints_cons _ _ _ (der_32279 v h) (hints_cons _ _ _ (der_32280 v h) (hints_cons _ _ _ (der_32281 v h) (hints_cons _ _ _ (der_32282 v h) (hints_cons _ _ _ (der_32284 v h) (hints_cons _ _ _ (der_32285 v h) (hints_cons _ _ _ (der_32286 v h) (hints_cons _ _ _ (der_32287 v h) (hints_cons _ _ _ (der_32288 v h) (hints_cons _ _ _ (der_32289 v h) (hints_cons _ _ _ (der_32290 v h) (hints_cons _ _ _ (der_32291 v h) (hints_cons _ _ _ (der_32292 v h) (hints_cons _ _ _ (der_32293 v h) (hints_cons _ _ _ (der_32295 v h) (hints_cons _ _ _ (der_32296 v h) (hints_cons _ _ _ (der_32297 v h) (hints_cons _ _ _ (der_32298 v h) (hints_cons _ _ _ (der_32299 v h) (hints_cons _ _ _ (der_32300 v h) (hints_cons _ _ _ (der_32301 v h) (hints_cons _ _ _ (der_32302 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix018 := prefix017 ++ chunk018
theorem prefix_sound018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix018, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound017 v h c hc
  · exact chunk_sound018 v h c hc
end Percolation.NReplay
