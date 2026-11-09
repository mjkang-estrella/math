import json,pathlib
L=pathlib.Path.cwd();rows=json.load(open('outputs/pagerank-exact.json'))
def rat(s):
 a=s.split('/');return '('+' / '.join(a)+' : ℝ)'
s='''import Mathlib.Basic.Real.Basic
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
'''
for r in rows:
 mu=r['mu'];val=r['projection'][3]
 s+=f'\ndef witness{mu} : E → ℝ := !['+','.join(rat(x)for x in r['stationary'])+']\n'
 s+=f'''theorem witness{mu}_valid : (∀ i, 0 ≤ witness{mu} i) ∧ (∑ i, witness{mu} i) = 1 ∧ stationary {mu} witness{mu} := by
  norm_num [stationary, transition, initial, tail, head, degree, witness{mu}, Fin.sum_univ_succ, Fin.forall_fin_succ]
'''
 s+=f'''theorem value{mu} (y : E → ℝ) (h : stationary {mu} y) : score y 3 = {rat(val)} := by
'''
 for i in range(8):s+=f'  have h{i} := h ({i} : E)\n'
 s+='  norm_num [stationary, transition, initial, tail, head, degree, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7\n'
 s+='  norm_num [score, tail, Fin.sum_univ_succ]\n'
 s+='  linear_combination '+ ' + '.join(f'{rat(d)} * h{i}'for i,d in enumerate(r['dual']))+'\n'
s+='''
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
end PageRank356988
#print axioms PageRank356988.no_monotone_path
'''
(L/'lean/PageRank.lean').write_text(s)
