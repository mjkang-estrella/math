import ChordComb2Five0
import ChordComb2Five1
import ChordComb2Five2
import ChordComb2Five3
import ChordComb2Five4
import ChordComb2Five5
import ChordComb2Five6
import ChordComb2Five7
import ChordComb2Five8
import ChordComb2Five9
import ChordComb2Five10
import ChordComb2Five11
import ChordComb2Five12
import ChordComb2Five13
import ChordComb2Five14
import ChordComb2Five15
import ChordComb2Five16
import ChordComb2Five17
import ChordComb2Five18
import ChordComb2Five19
import ChordComb2Five20
import ChordComb2Five21
import ChordComb2Five22
import ChordComb2Five23
import ChordComb2Five24
import ChordComb2Five25
import ChordComb2Five26
import ChordComb2Five27
import ChordComb2Five28
import ChordComb2Five29
import ChordComb2Five30
import ChordComb2Five31
import ChordComb2Five32
import ChordComb2Five33
import ChordComb2Five34
import ChordComb2Five35
import ChordComb2Five36
import ChordComb2Five37
import ChordComb2Five38
import ChordComb2Five39
import ChordComb2Five40
import ChordComb2Five41
import ChordComb2Five42
import ChordComb2Five43
import ChordComb2Five44
import ChordComb2Five45
import ChordComb2Five46
import ChordComb2Five47
import ChordComb2Five48
import ChordComb2Five49
import ChordComb2Five50
import ChordComb2Five51
import ChordComb2Five52
import ChordComb2Five53
import ChordComb2Five54
import ChordComb2Five55
import ChordComb2Five56
import ChordComb2Five57
import ChordComb2Five58
import ChordComb2Five59
import ChordComb2Five60
import ChordComb2Five61
import ChordComb2Five62
namespace Chord.Comb2
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
theorem fiveChordLemma : FiveChordLemma := by
  intro D
  have opts : D.partner 0 = 1 ∨ D.partner 0 = 2 ∨ D.partner 0 = 3 ∨ D.partner 0 = 4 ∨ D.partner 0 = 5 ∨ D.partner 0 = 6 ∨ D.partner 0 = 7 ∨ D.partner 0 = 8 ∨ D.partner 0 = 9 := by
    have inv := D.involutive 0
    have nf := D.noFixed 0
    generalize hv : D.partner 0 = v
    fin_cases v <;> simp_all
  rcases opts with h0_1 | h0_2 | h0_3 | h0_4 | h0_5 | h0_6 | h0_7 | h0_8 | h0_9
  · have h0 := h0_1
    have h1 : D.partner 1 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 2 = 3 ∨ D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 ∨ D.partner 2 = 8 ∨ D.partner 2 = 9 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_3 | h2_4 | h2_5 | h2_6 | h2_7 | h2_8 | h2_9
    · have h2 := h2_3
      have h3 : D.partner 3 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_0 D h0 h1 h2 h3
    · have h2 := h2_4
      have h4 : D.partner 4 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_1 D h0 h1 h2 h4
    · have h2 := h2_5
      have h5 : D.partner 5 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_2 D h0 h1 h2 h5
    · have h2 := h2_6
      have h6 : D.partner 6 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_3 D h0 h1 h2 h6
    · have h2 := h2_7
      have h7 : D.partner 7 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_4 D h0 h1 h2 h7
    · have h2 := h2_8
      have h8 : D.partner 8 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_5 D h0 h1 h2 h8
    · have h2 := h2_9
      have h9 : D.partner 9 = 2 := by simpa only [h2] using D.involutive 2
      exact closed5_6 D h0 h1 h2 h9
  · have h0 := h0_2
    have h2 : D.partner 2 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 ∨ D.partner 1 = 8 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8 | h1_9
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_7 D h0 h2 h1 h3
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_8 D h0 h2 h1 h4
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_9 D h0 h2 h1 h5
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_10 D h0 h2 h1 h6
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_11 D h0 h2 h1 h7
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_12 D h0 h2 h1 h8
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_13 D h0 h2 h1 h9
  · have h0 := h0_3
    have h3 : D.partner 3 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 ∨ D.partner 1 = 8 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8 | h1_9
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_14 D h0 h3 h1 h2
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_15 D h0 h3 h1 h4
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_16 D h0 h3 h1 h5
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_17 D h0 h3 h1 h6
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_18 D h0 h3 h1 h7
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_19 D h0 h3 h1 h8
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_20 D h0 h3 h1 h9
  · have h0 := h0_4
    have h4 : D.partner 4 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 ∨ D.partner 1 = 8 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_5 | h1_6 | h1_7 | h1_8 | h1_9
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_21 D h0 h4 h1 h2
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_22 D h0 h4 h1 h3
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_23 D h0 h4 h1 h5
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_24 D h0 h4 h1 h6
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_25 D h0 h4 h1 h7
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_26 D h0 h4 h1 h8
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_27 D h0 h4 h1 h9
  · have h0 := h0_5
    have h5 : D.partner 5 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 ∨ D.partner 1 = 8 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_4 | h1_6 | h1_7 | h1_8 | h1_9
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_28 D h0 h5 h1 h2
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_29 D h0 h5 h1 h3
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_30 D h0 h5 h1 h4
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_31 D h0 h5 h1 h6
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_32 D h0 h5 h1 h7
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_33 D h0 h5 h1 h8
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_34 D h0 h5 h1 h9
  · have h0 := h0_6
    have h6 : D.partner 6 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 7 ∨ D.partner 1 = 8 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_4 | h1_5 | h1_7 | h1_8 | h1_9
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_35 D h0 h6 h1 h2
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_36 D h0 h6 h1 h3
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_37 D h0 h6 h1 h4
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_38 D h0 h6 h1 h5
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_39 D h0 h6 h1 h7
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_40 D h0 h6 h1 h8
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_41 D h0 h6 h1 h9
  · have h0 := h0_7
    have h7 : D.partner 7 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 8 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_8 | h1_9
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_42 D h0 h7 h1 h2
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_43 D h0 h7 h1 h3
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_44 D h0 h7 h1 h4
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_45 D h0 h7 h1 h5
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_46 D h0 h7 h1 h6
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_47 D h0 h7 h1 h8
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_48 D h0 h7 h1 h9
  · have h0 := h0_8
    have h8 : D.partner 8 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 ∨ D.partner 1 = 9 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_9
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_49 D h0 h8 h1 h2
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_50 D h0 h8 h1 h3
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_51 D h0 h8 h1 h4
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_52 D h0 h8 h1 h5
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_53 D h0 h8 h1 h6
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_54 D h0 h8 h1 h7
    · have h1 := h1_9
      have h9 : D.partner 9 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_55 D h0 h8 h1 h9
  · have h0 := h0_9
    have h9 : D.partner 9 = 0 := by simpa only [h0] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 ∨ D.partner 1 = 8 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_4 | h1_5 | h1_6 | h1_7 | h1_8
    · have h1 := h1_2
      have h2 : D.partner 2 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_56 D h0 h9 h1 h2
    · have h1 := h1_3
      have h3 : D.partner 3 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_57 D h0 h9 h1 h3
    · have h1 := h1_4
      have h4 : D.partner 4 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_58 D h0 h9 h1 h4
    · have h1 := h1_5
      have h5 : D.partner 5 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_59 D h0 h9 h1 h5
    · have h1 := h1_6
      have h6 : D.partner 6 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_60 D h0 h9 h1 h6
    · have h1 := h1_7
      have h7 : D.partner 7 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_61 D h0 h9 h1 h7
    · have h1 := h1_8
      have h8 : D.partner 8 = 1 := by simpa only [h1] using D.involutive 1
      exact closed5_62 D h0 h9 h1 h8
#print axioms fiveChordLemma
end Chord.Comb2
