import Checker
import Mathlib.Data.Fintype.Prod
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option warningAsError true
namespace Palette
theorem code_no (a : C) (b : C) (c : C) (d : C) (e : C) (f : C) (g : C) (h : C) (i : C) (j : C) (hc : (code a b e) ≠ (code a c f) ∧ (code a b e) ≠ (code a d g) ∧ (code a b e) ≠ (code b c h) ∧ (code a b e) ≠ (code b d i) ∧ (code a b e) ≠ (code c d j) ∧ (code a b e) ≠ (code e f h) ∧ (code a b e) ≠ (code e g i) ∧ (code a b e) ≠ (code f g j) ∧ (code a b e) ≠ (code h i j) ∧ (code a c f) ≠ (code a d g) ∧ (code a c f) ≠ (code b c h) ∧ (code a c f) ≠ (code b d i) ∧ (code a c f) ≠ (code c d j) ∧ (code a c f) ≠ (code e f h) ∧ (code a c f) ≠ (code e g i) ∧ (code a c f) ≠ (code f g j) ∧ (code a c f) ≠ (code h i j) ∧ (code a d g) ≠ (code b c h) ∧ (code a d g) ≠ (code b d i) ∧ (code a d g) ≠ (code c d j) ∧ (code a d g) ≠ (code e f h) ∧ (code a d g) ≠ (code e g i) ∧ (code a d g) ≠ (code f g j) ∧ (code a d g) ≠ (code h i j) ∧ (code b c h) ≠ (code b d i) ∧ (code b c h) ≠ (code c d j) ∧ (code b c h) ≠ (code e f h) ∧ (code b c h) ≠ (code e g i) ∧ (code b c h) ≠ (code f g j) ∧ (code b c h) ≠ (code h i j) ∧ (code b d i) ≠ (code c d j) ∧ (code b d i) ≠ (code e f h) ∧ (code b d i) ≠ (code e g i) ∧ (code b d i) ≠ (code f g j) ∧ (code b d i) ≠ (code h i j) ∧ (code c d j) ≠ (code e f h) ∧ (code c d j) ≠ (code e g i) ∧ (code c d j) ≠ (code f g j) ∧ (code c d j) ≠ (code h i j) ∧ (code e f h) ≠ (code e g i) ∧ (code e f h) ≠ (code f g j) ∧ (code e f h) ≠ (code h i j) ∧ (code e g i) ≠ (code f g j) ∧ (code e g i) ≠ (code h i j) ∧ (code f g j) ≠ (code h i j)) : False := by
  rcases hc with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44⟩
  have hh0 : check0 = true := check_pass
  simp only [check0] at hh0
  have hh1 := (all4_spec _).mp hh0 a
  simp only [check1] at hh1
  have hh2 := (all4_spec _).mp hh1 b
  simp only [check2] at hh2
  have hh3 := (all4_spec _).mp hh2 c
  simp only [check3] at hh3
  have hh4 := (all4_spec _).mp hh3 d
  simp only [check4] at hh4
  have hh5 := (all4_spec _).mp hh4 e
  simp only [check5] at hh5
  have hh6 := (all4_spec _).mp hh5 f
  simp only [check6 , ite_eq_right p0] at hh6
  have hh7 := (all4_spec _).mp hh6 g
  simp only [check7 , ite_eq_right p1, ite_eq_right p9] at hh7
  have hh8 := (all4_spec _).mp hh7 h
  simp only [check8 , ite_eq_right p2, ite_eq_right p5, ite_eq_right p10, ite_eq_right p13, ite_eq_right p17, ite_eq_right p20, ite_eq_right p26] at hh8
  have hh9 := (all4_spec _).mp hh8 i
  simp only [check9 , ite_eq_right p3, ite_eq_right p6, ite_eq_right p11, ite_eq_right p14, ite_eq_right p18, ite_eq_right p21, ite_eq_right p24, ite_eq_right p27, ite_eq_right p31, ite_eq_right p32, ite_eq_right p39] at hh9
  have hh10 := (all4_spec _).mp hh9 j
  simp only [check10 , ite_eq_right p4, ite_eq_right p7, ite_eq_right p8, ite_eq_right p12, ite_eq_right p15, ite_eq_right p16, ite_eq_right p19, ite_eq_right p22, ite_eq_right p23, ite_eq_right p25, ite_eq_right p28, ite_eq_right p29, ite_eq_right p30, ite_eq_right p33, ite_eq_right p34, ite_eq_right p35, ite_eq_right p36, ite_eq_right p37, ite_eq_right p38, ite_eq_right p40, ite_eq_right p41, ite_eq_right p42, ite_eq_right p43, ite_eq_right p44] at hh10
  exact Bool.false_ne_true hh10

abbrev Triangle (n : Nat) := { t : Fin n × Fin n × Fin n // t.1 < t.2.1 ∧ t.2.1 < t.2.2 }
abbrev Edge (n : Nat) := {p : Fin n × Fin n // p.1 < p.2}
def trianglePalette {n k : Nat} (c : Edge n → Fin k) (t : Triangle n) : Finset (Fin k) :=
  {c ⟨(t.val.1,t.val.2.1),t.property.1⟩, c ⟨(t.val.1,t.val.2.2),lt_trans t.property.1 t.property.2⟩, c ⟨(t.val.2.1,t.val.2.2),t.property.2⟩}
def t0 : Triangle 5 := ⟨(0,1,2), by decide⟩
def t1 : Triangle 5 := ⟨(0,1,3), by decide⟩
def t2 : Triangle 5 := ⟨(0,1,4), by decide⟩
def t3 : Triangle 5 := ⟨(0,2,3), by decide⟩
def t4 : Triangle 5 := ⟨(0,2,4), by decide⟩
def t5 : Triangle 5 := ⟨(0,3,4), by decide⟩
def t6 : Triangle 5 := ⟨(1,2,3), by decide⟩
def t7 : Triangle 5 := ⟨(1,2,4), by decide⟩
def t8 : Triangle 5 := ⟨(1,3,4), by decide⟩
def t9 : Triangle 5 := ⟨(2,3,4), by decide⟩
theorem no_four (c : Edge 5 → C) : ¬ Function.Injective (trianglePalette c) := by
  intro hd
  apply code_no (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩)
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) he
    have ht : t0 = t1 := hd hp
    exact (by decide : t0 ≠ t1) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) he
    have ht : t0 = t2 := hd hp
    exact (by decide : t0 ≠ t2) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t0 = t3 := hd hp
    exact (by decide : t0 ≠ t3) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t0 = t4 := hd hp
    exact (by decide : t0 ≠ t4) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t0 = t5 := hd hp
    exact (by decide : t0 ≠ t5) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t0 = t6 := hd hp
    exact (by decide : t0 ≠ t6) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t0 = t7 := hd hp
    exact (by decide : t0 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t0 = t8 := hd hp
    exact (by decide : t0 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t0 = t9 := hd hp
    exact (by decide : t0 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) he
    have ht : t1 = t2 := hd hp
    exact (by decide : t1 ≠ t2) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t1 = t3 := hd hp
    exact (by decide : t1 ≠ t3) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t1 = t4 := hd hp
    exact (by decide : t1 ≠ t4) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t1 = t5 := hd hp
    exact (by decide : t1 ≠ t5) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t1 = t6 := hd hp
    exact (by decide : t1 ≠ t6) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t1 = t7 := hd hp
    exact (by decide : t1 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t1 = t8 := hd hp
    exact (by decide : t1 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t1 = t9 := hd hp
    exact (by decide : t1 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t2 = t3 := hd hp
    exact (by decide : t2 ≠ t3) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t2 = t4 := hd hp
    exact (by decide : t2 ≠ t4) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t2 = t5 := hd hp
    exact (by decide : t2 ≠ t5) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t2 = t6 := hd hp
    exact (by decide : t2 ≠ t6) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t2 = t7 := hd hp
    exact (by decide : t2 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t2 = t8 := hd hp
    exact (by decide : t2 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(0,1),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t2 = t9 := hd hp
    exact (by decide : t2 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t3 = t4 := hd hp
    exact (by decide : t3 ≠ t4) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t3 = t5 := hd hp
    exact (by decide : t3 ≠ t5) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t3 = t6 := hd hp
    exact (by decide : t3 ≠ t6) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t3 = t7 := hd hp
    exact (by decide : t3 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t3 = t8 := hd hp
    exact (by decide : t3 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t3 = t9 := hd hp
    exact (by decide : t3 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t4 = t5 := hd hp
    exact (by decide : t4 ≠ t5) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t4 = t6 := hd hp
    exact (by decide : t4 ≠ t6) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t4 = t7 := hd hp
    exact (by decide : t4 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t4 = t8 := hd hp
    exact (by decide : t4 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(0,2),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t4 = t9 := hd hp
    exact (by decide : t4 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) he
    have ht : t5 = t6 := hd hp
    exact (by decide : t5 ≠ t6) ht
  · intro he
    have hp := code_sound (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t5 = t7 := hd hp
    exact (by decide : t5 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t5 = t8 := hd hp
    exact (by decide : t5 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(0,3),by decide⟩) (c ⟨(0,4),by decide⟩) (c ⟨(3,4),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t5 = t9 := hd hp
    exact (by decide : t5 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) he
    have ht : t6 = t7 := hd hp
    exact (by decide : t6 ≠ t7) ht
  · intro he
    have hp := code_sound (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t6 = t8 := hd hp
    exact (by decide : t6 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(1,2),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t6 = t9 := hd hp
    exact (by decide : t6 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t7 = t8 := hd hp
    exact (by decide : t7 ≠ t8) ht
  · intro he
    have hp := code_sound (c ⟨(1,2),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t7 = t9 := hd hp
    exact (by decide : t7 ≠ t9) ht
  · intro he
    have hp := code_sound (c ⟨(1,3),by decide⟩) (c ⟨(1,4),by decide⟩) (c ⟨(3,4),by decide⟩) (c ⟨(2,3),by decide⟩) (c ⟨(2,4),by decide⟩) (c ⟨(3,4),by decide⟩) he
    have ht : t8 = t9 := hd hp
    exact (by decide : t8 ≠ t9) ht

def Achievable (n k : Nat) : Prop := ∃ c : Edge n → Fin k, Function.Injective (trianglePalette c)
def SourceClaim : Prop := ∀ n : Nat, 4 ≤ n → IsLeast {k : Nat | Achievable n k} (n-1)
theorem source_refutation : ¬ SourceClaim := by
  intro h
  obtain ⟨c, hc⟩ := (h 5 (by decide)).1
  exact no_four c hc
end Palette
