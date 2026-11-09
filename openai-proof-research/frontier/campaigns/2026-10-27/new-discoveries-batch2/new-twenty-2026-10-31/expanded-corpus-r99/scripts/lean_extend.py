import pathlib,json,re
p=pathlib.Path('lean/PageRank.lean');s=p.read_text();f=json.load(open('outputs/pagerank-symbolic.json'))
def lean(x):return x.replace('**','^').replace('*',' * ').replace('t','μ')
new='''
def denom (μ : ℝ) : ℝ := 12321 * μ^2 + 235098 * μ + 1004981
def pathEdge (μ : ℝ) : E → ℝ := ![
'''+',\n'.join(lean(f[k])for k in ['a','b','c','b','c','d','e','e'])+''']
def path (μ : ℝ) : V → ℝ := score (pathEdge μ)
theorem pathEdge_valid {μ : ℝ} (hμ : 0 < μ) :
    (∀ i, 0 ≤ pathEdge μ i) ∧ (∑ i, pathEdge μ i) = 1 ∧ stationary μ (pathEdge μ) := by
  have hd : 0 < 12321 * μ^2 + 235098 * μ + 1004981 := by positivity
  have h1 : μ + 1 ≠ 0 := by positivity
  have h2 : μ + 2 ≠ 0 := by positivity
  constructor
  · intro i
    fin_cases i <;> simp only [pathEdge, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> positivity
  constructor
  · simp only [pathEdge, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one]
    field_simp
    <;> ring
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
'''
s=s.replace('end PageRank356988',new+'\nend PageRank356988');p.write_text(s)
