# Stable exported interfaces

All names below are in namespace InversePeriodDoubling; exact expanded types
of every declaration are in the audit logs.

- D,U : PowerSeries (ZMod 2); d,u : Nat -> ZMod 2.
- D_subst_U : D.subst U = X; U_subst_D : U.subst D = X.
- U_unique(Q)(HasSubst Q)(D.subst Q=X) : Q=U.
- scalar_recurrence : ScalarRecurrence, whose body is the three literal recurrences.
- u_even(n) : u(2*n)=0; u_four_one(n)(1<=n) : u(4*n+1)=u(2*n-1).
- u_four_three(n) : u(4*n+3)=u n; u_zero/u_one.
- State, delta, output, run, value, state, auto; table1_numeric(w) :
  output(run S w)=u(value w). valueFrom_formula gives positional interpretation.
- a,b,g,c : Nat -> Nat, source-defined via Nat.nth and natural subtraction.
- enumeration_endpoint : EnumerationEndpoint. Includes both infinitudes,
  StrictMono b/a/c, gap alphabet and exact exceptional-position characterization.
- a_bounds(j) : j+1<=a j; around_one(j) gives both zero ranks around a j.
- suffixValues(q)(t), suffix_count_recurrence, suffix_bound, suffix_depth_three,
  suffix_semantics, suffix_source.

Residuals for item4: all-depth pairwise ordering/no duplicates; extrema and Fibonacci
counts table t>=3, first-threshold theorem at firstThreshold(t), exact gap alphabet
and record classification. No conditional assumption-to-output theorem is offered
as an unconditional solution. Future generic assembly must supply the regularity,
recognizability, pumping and base conversion theorems with proofs.
