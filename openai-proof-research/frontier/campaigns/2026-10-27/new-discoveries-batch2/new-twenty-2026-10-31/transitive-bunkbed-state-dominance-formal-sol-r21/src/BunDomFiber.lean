import BunState
import Mathlib.Data.Fintype.EquivFin
namespace BunDom
open Bun Classical
abbrev Fresh (j : Nat) := (Fin (j+1) → Bool → Bool) × Bool

def split {n j : Nat} (hn : j+1 < n) (w : Asg n (j+1)) : Asg n j × Fresh j :=
  (res n j w, (fun i l => w (fresH hn i.1 i.2 l), w (fresV hn)))

def join {n j : Nat} (p : Asg n j × Fresh j) : Asg n (j+1) := fun t =>
  if h : tmax t.1 ≤ j then p.1 ⟨t.1, h⟩ else
  match he : t.1 with
  | Sum.inl a => p.2.1 ⟨a.fst.1, by have hh := a.hlt; have ht := t.2; rw [he] at ht; simp only [tmax] at ht; omega⟩ a.layer
  | Sum.inr _ => p.2.2

theorem join_split {n j : Nat} (hn : j+1 < n) (w : Asg n (j+1)) :
    join (split hn w) = w := by
  funext t
  unfold join
  split_ifs with h
  · rfl
  · rcases t with ⟨a, ha⟩
    cases a with
    | inl a =>
      have hs : a.snd.1 = j+1 := by simp [tmax] at h ha; omega
      have he : fresH hn a.fst.1 (by have := a.hlt; omega) a.layer =
          (⟨Sum.inl a, ha⟩ : Win n (j+1)) := by
        apply Subtype.ext
        change Sum.inl _ = Sum.inl _
        congr 1
        cases a
        congr 1
        exact Fin.ext hs.symm
      exact congrArg w he
    | inr a =>
      have hs : a.1 = j+1 := by simp [tmax] at h ha; omega
      apply congrArg w
      apply Subtype.ext
      simp only [fresV]
      congr 1
      exact Fin.ext hs.symm

theorem split_join {n j : Nat} (hn : j+1 < n) (p : Asg n j × Fresh j) :
    split hn (join p) = p := by
  apply Prod.ext
  · funext t
    change (if h : tmax t.1 ≤ j then p.1 ⟨t.1,h⟩ else _) = p.1 t
    rw [dite_eq_left t.2]
    rfl
  · apply Prod.ext
    · funext i l
      simp [split, join, fresH, tmax, htok]
    · simp [split, join, fresV, tmax]

def assignmentEquiv {n j : Nat} (hn : j+1 < n) :
    Asg n (j+1) ≃ Asg n j × Fresh j :=
  ⟨split hn, join, join_split hn, split_join hn⟩

noncomputable instance asgFintype (n j : Nat) : Fintype (Asg n j) := by
  classical
  unfold Asg Win
  infer_instance

def fiberEquiv {n j : Nat} (hn : j+1 < n) (p : Asg n j) :
    {w : Asg n (j+1) // res n j w = p} ≃ Fresh j where
  toFun w := (split hn w.1).2
  invFun f := ⟨join (p,f), congrArg Prod.fst (split_join hn (p,f))⟩
  left_inv w := by
    apply Subtype.ext
    have h := join_split hn w.1
    have hp : split hn w.1 = (p, (split hn w.1).2) :=
      Prod.ext w.2 rfl
    rw [hp] at h
    exact h
  right_inv f := congrArg Prod.snd (split_join hn (p,f))

theorem fresh_card (j : Nat) : Fintype.card (Fresh j) = 2^(2*j+3) := by
  simp only [Fresh, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  rw [← pow_mul, ← pow_succ]
  congr 1

theorem prefix_fiber_card {n j : Nat} (hn : j+1 < n) (p : Asg n j) :
    Fintype.card {w : Asg n (j+1) // res n j w = p} = 2^(2*j+3) := by
  classical
  exact (Fintype.card_congr (fiberEquiv hn p)).trans (fresh_card j)
end BunDom
