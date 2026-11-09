import BFSGeneral
import ArithmeticBase
namespace EBC337062
open SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem table_zero : ∀ t a : ZMod 32, tabDist a.val t.val = 0 ↔ a = t := by decide

theorem table_step : ∀ t a b : ZMod 32, G32.Adj a b →
    tabDist a.val t.val ≤ tabDist b.val t.val + 1 := by decide

theorem table_pred : ∀ t a : ZMod 32, a ≠ t → ∃ b : ZMod 32,
    G32.Adj a b ∧ tabDist b.val t.val + 1 = tabDist a.val t.val := by decide

theorem table_count_self : ∀ t : ZMod 32, tabCount t.val t.val = 1 := by decide

theorem table_count_rec : ∀ t a : ZMod 32, a ≠ t →
    tabCount a.val t.val = ∑ b : G32.neighborSet a,
      if tabDist b.val.val t.val + 1 = tabDist a.val t.val
      then tabCount b.val.val t.val else 0 := by decide

theorem g32_dist_table (a t : ZMod 32) : G32.dist a t = tabDist a.val t.val :=
  dist_eq_labels G32 t (fun a => tabDist a.val t.val)
    (table_zero t) (table_step t) (table_pred t) a

theorem g32_sigma_table (a t : ZMod 32) : sigma G32 a t = tabCount a.val t.val :=
  sigma_eq_of_bfs G32 t (fun a => tabDist a.val t.val) (fun a => tabCount a.val t.val)
    (table_zero t) (table_step t) (table_pred t) (table_count_self t) (table_count_rec t) a
end EBC337062
