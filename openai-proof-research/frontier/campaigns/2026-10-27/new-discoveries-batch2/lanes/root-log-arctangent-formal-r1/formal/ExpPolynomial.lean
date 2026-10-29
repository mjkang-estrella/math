import MeanAnalyticDefs
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
/-- A quadratic polynomial times one genuine exponential. -/
@[ext] structure ExpQuadratic where
  rate : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
noncomputable def ExpQuadratic.eval (q : ExpQuadratic) (t : ℝ) : ℝ :=
  (q.a + q.b*t + q.c*t^2)*Real.exp (q.rate*t)
noncomputable def ExpQuadratic.step (q : ExpQuadratic) : ExpQuadratic :=
  ⟨q.rate, q.rate*q.a+q.b, q.rate*q.b+2*q.c, q.rate*q.c⟩
theorem ExpQuadratic.hasDerivAt (q : ExpQuadratic) (t : ℝ) :
    HasDerivAt q.eval (q.step.eval t) t := by
  have ht := hasDerivAt_id t
  convert ((((hasDerivAt_const t q.a).add (ht.const_mul q.b)).add
    ((ht.pow 2).const_mul q.c)).mul ((ht.const_mul q.rate).exp)) using 1
  · rfl
  · dsimp [ExpQuadratic.eval, ExpQuadratic.step, id]
    ring
noncomputable def evalExpList (qs : List ExpQuadratic) (t : ℝ) : ℝ :=
  (qs.map (fun q => q.eval t)).sum
theorem hasDerivAt_evalExpList (qs : List ExpQuadratic) (t : ℝ) :
    HasDerivAt (evalExpList qs) (evalExpList (qs.map ExpQuadratic.step) t) t := by
  induction qs with
  | nil => exact hasDerivAt_const t 0
  | cons q qs ih =>
    convert (q.hasDerivAt t).add ih using 1
    · funext x; simp [evalExpList]
    · simp [evalExpList]
theorem deriv_evalExpList (qs : List ExpQuadratic) :
    deriv (evalExpList qs) = evalExpList (qs.map ExpQuadratic.step) :=
  funext fun t => (hasDerivAt_evalExpList qs t).deriv
noncomputable def expListJet : ℕ → List ExpQuadratic → List ExpQuadratic
  | 0, qs => qs
  | n+1, qs => (expListJet n qs).map ExpQuadratic.step
theorem iteratedDeriv_evalExpList (qs : List ExpQuadratic) (n : ℕ) :
    iteratedDeriv n (evalExpList qs) = evalExpList (expListJet n qs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_evalExpList]
    rfl

noncomputable def ExpQuadratic.jet : ℕ → ExpQuadratic → ExpQuadratic
  | 0, q => q
  | n+1, q => (q.jet n).step
noncomputable def ExpQuadratic.jetFormula (q : ExpQuadratic) (n : ℕ) : ExpQuadratic :=
  ⟨q.rate,
   q.rate^(n+2)*q.a+(n+2)*q.rate^(n+1)*q.b+(n+2)*(n+1)*q.rate^n*q.c,
   q.rate^(n+2)*q.b+2*(n+2)*q.rate^(n+1)*q.c,
   q.rate^(n+2)*q.c⟩
theorem ExpQuadratic.jet_formula (q : ExpQuadratic) (n : ℕ) :
    q.jet (n+2) = q.jetFormula n := by
  induction n with
  | zero =>
    apply ExpQuadratic.ext <;>
      simp [jet, step, jetFormula] <;> ring
  | succ n ih =>
    change (q.jet (n+2)).step = q.jetFormula (n+1)
    rw [ih]
    apply ExpQuadratic.ext <;>
      simp [step, jetFormula, pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
theorem expListJet_map (qs : List ExpQuadratic) (n : ℕ) :
    expListJet n qs = qs.map (fun q => q.jet n) := by
  induction n with
  | zero => simp [expListJet, ExpQuadratic.jet]
  | succ n ih => simp only [expListJet, ih, List.map_map, ExpQuadratic.jet, Function.comp_def]

theorem ExpQuadratic.jet24 (q : ExpQuadratic) : q.jet 24 = q.jetFormula 22 :=
  q.jet_formula 22
noncomputable def pairExp (l u v : ℝ) : List ExpQuadratic :=
  [⟨l,u,v,2*u⟩,⟨-l,u,-v,2*u⟩]
theorem pairExp_derivative24 (l u v t : ℝ) :
    evalExpList (expListJet 24 (pairExp l u v)) t =
    2*(l^22*(u*l^2+24*v*l+1104*u)*Real.cosh (l*t) +
      t*(l^22*(v*l+94*u)+2*l^22*u)*l*Real.sinh (l*t) +
      t^2*(2*l^22*u)*l^2*Real.cosh (l*t)) := by
  rw [expListJet_map]
  simp only [pairExp, List.map_cons, List.map_nil, evalExpList, List.sum_cons,
    List.sum_nil, ExpQuadratic.jet24, ExpQuadratic.jetFormula, ExpQuadratic.eval]
  norm_num [Real.cosh_eq, Real.sinh_eq, neg_mul, pow_succ]
  ring
end LogArctangentMean


