import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
set_option maxHeartbeats 2000000
noncomputable section
namespace PageRank356988
abbrev V := Fin 4
abbrev E := Fin 8
def tail : E → V := ![0,1,1,2,2,3,3,3]
def head : E → V := ![3,2,3,1,3,0,1,2]
def degree : V → ℕ := ![1,2,2,3]
def transition (μ : ℝ) (i j : E) : ℝ :=
  if head j = tail i then
    (if head i = tail j then μ else 1) / ((degree (head j) : ℝ) - 1 + μ)
  else 0
def initial (i : E) : ℝ := 1 / (4 * degree (tail i))
def stationary (μ : ℝ) (y : E → ℝ) : Prop :=
  ∀ i, y i = (17 / 20 : ℝ) * ∑ j, transition μ i j * y j + (3 / 20 : ℝ) * initial i
def score (y : E → ℝ) (v : V) : ℝ := ∑ i, if tail i = v then y i else 0
def isPageRank (μ : ℝ) (p : V → ℝ) : Prop :=
  ∃ y : E → ℝ, (∀ i, 0 ≤ y i) ∧ (∑ i, y i) = 1 ∧ stationary μ y ∧ p = score y
-- Edge presentation is a loopless symmetric simple graph, with the listed degree function.
theorem no_loops : ∀ i, tail i ≠ head i := by decide
theorem no_parallel : Function.Injective (fun i => (tail i, head i)) := by decide
theorem reverse_exists : ∀ i, ∃ j, tail j = head i ∧ head j = tail i := by decide
theorem correct_degree : ∀ v, (Finset.univ.filter (fun i => tail i = v)).card = degree v := by decide

def witness1 : E → ℝ := ![(1771 / 12524 : ℝ),(385 / 3131 : ℝ),(385 / 3131 : ℝ),(385 / 3131 : ℝ),(385 / 3131 : ℝ),(1531 / 12524 : ℝ),(1531 / 12524 : ℝ),(1531 / 12524 : ℝ)]
theorem witness1_valid : (∀ i, 0 ≤ witness1 i) ∧ (∑ i, witness1 i) = 1 ∧ stationary 1 witness1 := by
  norm_num [stationary, transition, initial, tail, head, degree, witness1, Fin.sum_univ_succ, Fin.forall_fin_succ]
theorem value1 (y : E → ℝ) (h : stationary 1 y) : score y 3 = (4593 / 12524 : ℝ) := by
  have h0 := h (0 : E)
  have h1 := h (1 : E)
  have h2 := h (2 : E)
  have h3 := h (3 : E)
  have h4 := h (4 : E)
  have h5 := h (5 : E)
  have h6 := h (6 : E)
  have h7 := h (7 : E)
  norm_num [stationary, transition, initial, tail, head, degree, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num [score, tail, Fin.sum_univ_succ]
  linear_combination (7820 / 3131 : ℝ) * h0 + (5780 / 3131 : ℝ) * h1 + (7820 / 3131 : ℝ) * h2 + (5780 / 3131 : ℝ) * h3 + (7820 / 3131 : ℝ) * h4 + (9778 / 3131 : ℝ) * h5 + (8911 / 3131 : ℝ) * h6 + (8911 / 3131 : ℝ) * h7

def witness10 : E → ℝ := ![(2866267 / 18352244 : ℝ),(4454441 / 36704488 : ℝ),(2137027 / 18352244 : ℝ),(4454441 / 36704488 : ℝ),(2137027 / 18352244 : ℝ),(2562421 / 18352244 : ℝ),(4195061 / 36704488 : ℝ),(4195061 / 36704488 : ℝ)]
theorem witness10_valid : (∀ i, 0 ≤ witness10 i) ∧ (∑ i, witness10 i) = 1 ∧ stationary 10 witness10 := by
  norm_num [stationary, transition, initial, tail, head, degree, witness10, Fin.sum_univ_succ, Fin.forall_fin_succ]
theorem value10 (y : E → ℝ) (h : stationary 10 y) : score y 3 = (3378741 / 9176122 : ℝ) := by
  have h0 := h (0 : E)
  have h1 := h (1 : E)
  have h2 := h (2 : E)
  have h3 := h (3 : E)
  have h4 := h (4 : E)
  have h5 := h (5 : E)
  have h6 := h (6 : E)
  have h7 := h (7 : E)
  norm_num [stationary, transition, initial, tail, head, degree, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num [score, tail, Fin.sum_univ_succ]
  linear_combination (13345340 / 4588061 : ℝ) * h0 + (4236740 / 4588061 : ℝ) * h1 + (12461000 / 4588061 : ℝ) * h2 + (4236740 / 4588061 : ℝ) * h3 + (12461000 / 4588061 : ℝ) * h4 + (15931600 / 4588061 : ℝ) * h5 + (14544400 / 4588061 : ℝ) * h6 + (14544400 / 4588061 : ℝ) * h7

def witness100 : E → ℝ := ![(5917571 / 34758772 : ℝ),(8615233 / 69517544 : ℝ),(3754751 / 34758772 : ℝ),(8615233 / 69517544 : ℝ),(3754751 / 34758772 : ℝ),(5428373 / 34758772 : ℝ),(7288093 / 69517544 : ℝ),(7288093 / 69517544 : ℝ)]
theorem witness100_valid : (∀ i, 0 ≤ witness100 i) ∧ (∑ i, witness100 i) = 1 ∧ stationary 100 witness100 := by
  norm_num [stationary, transition, initial, tail, head, degree, witness100, Fin.sum_univ_succ, Fin.forall_fin_succ]
theorem value100 (y : E → ℝ) (h : stationary 100 y) : score y 3 = (6358233 / 17379386 : ℝ) := by
  have h0 := h (0 : E)
  have h1 := h (1 : E)
  have h2 := h (2 : E)
  have h3 := h (3 : E)
  have h4 := h (4 : E)
  have h5 := h (5 : E)
  have h6 := h (6 : E)
  have h7 := h (7 : E)
  norm_num [stationary, transition, initial, tail, head, degree, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num [score, tail, Fin.sum_univ_succ]
  linear_combination (26575420 / 8689693 : ℝ) * h0 + (1381420 / 8689693 : ℝ) * h1 + (26003200 / 8689693 : ℝ) * h2 + (1381420 / 8689693 : ℝ) * h3 + (26003200 / 8689693 : ℝ) * h4 + (31278800 / 8689693 : ℝ) * h5 + (30585200 / 8689693 : ℝ) * h6 + (30585200 / 8689693 : ℝ) * h7

-- A coordinate of any PageRank path on this graph cannot be monotone in either direction.
theorem no_monotone_path : ¬ ∃ p : ℝ → V → ℝ,
    (∀ μ, 0 < μ → isPageRank μ (p μ)) ∧
    (MonotoneOn (fun μ => p μ 3) (Set.Ioi 0) ∨
     AntitoneOn (fun μ => p μ 3) (Set.Ioi 0)) := by
  rintro ⟨p, hp, hm⟩
  obtain ⟨y1, _, _, hy1, he1⟩ := hp 1 (by norm_num)
  obtain ⟨y10, _, _, hy10, he10⟩ := hp 10 (by norm_num)
  obtain ⟨y100, _, _, hy100, he100⟩ := hp 100 (by norm_num)
  have v1 := value1 y1 hy1
  have v10 := value10 y10 hy10
  have v100 := value100 y100 hy100
  rcases hm with hm | hm
  · have z := hm (show (10 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (100 : ℝ) ∈ Set.Ioi 0 by norm_num) (by norm_num : (10 : ℝ) ≤ 100)
    change p 10 3 ≤ p 100 3 at z
    rw [he10, he100] at z
    linarith
  · have z := hm (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (10 : ℝ) ∈ Set.Ioi 0 by norm_num) (by norm_num : (1 : ℝ) ≤ 10)
    change p 10 3 ≤ p 1 3 at z
    rw [he1, he10] at z
    linarith

def denom (μ : ℝ) : ℝ := 12321 * μ^2 + 235098 * μ + 1004981
def pathEdge (μ : ℝ) : E → ℝ := ![
(8547 * μ^2 + 145746 * μ + 554107)/(4 * (12321 * μ^2 + 235098 * μ + 1004981)),
(37 * μ + 363) * (333 * μ + 2747)/(8 * (12321 * μ^2 + 235098 * μ + 1004981)),
(5217 * μ^2 + 111616 * μ + 499167)/(4 * (12321 * μ^2 + 235098 * μ + 1004981)),
(37 * μ + 363) * (333 * μ + 2747)/(8 * (12321 * μ^2 + 235098 * μ + 1004981)),
(5217 * μ^2 + 111616 * μ + 499167)/(4 * (12321 * μ^2 + 235098 * μ + 1004981)),
(7881 * μ^2 + 129978 * μ + 474541)/(4 * (12321 * μ^2 + 235098 * μ + 1004981)),
(10101 * μ^2 + 218918 * μ + 995781)/(8 * (12321 * μ^2 + 235098 * μ + 1004981)),
(10101 * μ^2 + 218918 * μ + 995781)/(8 * (12321 * μ^2 + 235098 * μ + 1004981))]
def path (μ : ℝ) : V → ℝ := score (pathEdge μ)
theorem pathEdge_valid {μ : ℝ} (hμ : 0 < μ) :
    (∀ i, 0 ≤ pathEdge μ i) ∧ (∑ i, pathEdge μ i) = 1 ∧ stationary μ (pathEdge μ) := by
  have hd : 0 < 12321 * μ^2 + 235098 * μ + 1004981 := by positivity
  have h1 : μ + 1 ≠ 0 := by positivity
  have h2 : μ + 2 ≠ 0 := by positivity
  constructor
  · intro i
    fin_cases i <;> norm_num [pathEdge] <;> positivity
  constructor
  · simp only [pathEdge, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    field_simp
    ring
  · intro i
    fin_cases i <;> norm_num [stationary, transition, initial, tail, head, degree, pathEdge, Fin.sum_univ_succ]
    all_goals field_simp
    all_goals ring

theorem path_isPageRank {μ : ℝ} (hμ : 0 < μ) : isPageRank μ (path μ) := by
  obtain ⟨ha,hb,hc⟩ := pathEdge_valid hμ
  exact ⟨pathEdge μ, ha, hb, hc, rfl⟩
theorem coordinate_nonmonotone :
    ¬ (MonotoneOn (fun μ => path μ 3) (Set.Ioi 0) ∨
       AntitoneOn (fun μ => path μ 3) (Set.Ioi 0)) := by
  intro h
  exact no_monotone_path ⟨path, fun _ hμ => path_isPageRank hμ, h⟩

end PageRank356988
#print axioms PageRank356988.no_monotone_path
