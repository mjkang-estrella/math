# Borwein sine series

## Synopsis

The [Borwein sine series problem][gdm], posed in a 2004 textbook, asks whether

$$\sum\_{n=1}^{\infty} \frac{\left(\frac{2}{3} + \frac{1}{3}\sin n\right)^n}{n}$$

converges.
A complete proof of the convergence is given in the short note
[arXiv:2007.11017 (Boppana)](https://arxiv.org/abs/2007.11017).

We provided this problem to AxiomProver as a test case,
without referencing Boppana's paper,
but including an assumption on the [irrationality measure of pi][ZZ2020].
We found it was able to re-derive a similar proof and formalize it in Lean.

## Artifcats from AxiomProver

### Input files

See [`input/BorweinSineSeries`](../input/BorweinSineSeries).

- [`.environment`](../input/BorweinSineSeries/.environment): specifies the Lean version
- [`task.md`](../input/BorweinSineSeries/task.md): description of the task to be completed
- [`problem.lean`](../input/BorweinSineSeries/problem.lean): problem statement to be formalized

### Output files (run with Lean 4.28.0), with edits

**Note that these files have minor refactoring edits compared to raw output**;
see the full diff below.

- [`BorweinSineSeries/problem.lean`](../BorweinSineSeries/problem.lean): problem statement
- [`BorweinSineSeries/solution.lean`](../BorweinSineSeries/solution.lean): outputted solution file

### Comment on μ(π) and edits

When we provided the problem to AxiomProver,
we gave 7.6063 as the upper bound on μ(π).
However, this value is actually slightly lower than Salikhov's bound 7.606308…;
moreover, it has since been improved to 7.10321… in [arXiv:1912.06345][ZZ2020].

Hence, we edited `BorweinSineSeries` manually after generation
to use the new constant (and also to improve the style
by not hard-coding the constant everywhere):

```lean
/-- The value μ(π) ≈ 7.10321 (see arXiv:1912.06345) -/
noncomputable abbrev muPi : ℝ := 7.10321
```

The `diff` for these edits is provided below for context.

#### diff for `problem.lean`

```diff
@@ -1,8 +1,11 @@
 import Mathlib
 
-noncomputable def PiIrrBound : Prop :=
+/-- The value μ(π) ≈ 7.10321 (see arXiv:1912.06345) -/
+noncomputable abbrev muPi : ℝ := 7.10321
+
+def PiIrrBound : Prop :=
   ∃ (C : ℝ) (Q₀ : ℕ), 0 < C ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → Q₀ ≤ q →
-    C / (q : ℝ) ^ (7.6063 : ℝ) < |Real.pi - (p : ℝ) / (q : ℝ)|
+    C / (q : ℝ) ^ muPi < |Real.pi - (p : ℝ) / (q : ℝ)|
 
 theorem borwein_sine_series (hpi: PiIrrBound) :
     Summable fun n : ℕ+ ↦ ((2 / 3 + 1 / 3 * Real.sin (n : ℝ)) ^ (n : ℕ)) / (n : ℝ) := by
```

#### diff for `solution.lean`

```diff
@@ -2,9 +2,12 @@ import Mathlib
 
 open scoped Classical
 
-noncomputable def PiIrrBound : Prop :=
+/-- The value μ(π) ≈ 7.10321 (see arXiv:1912.06345) -/
+noncomputable abbrev muPi : ℝ := 7.10321
+
+def PiIrrBound : Prop :=
   ∃ (C : ℝ) (Q₀ : ℕ), 0 < C ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → Q₀ ≤ q →
-    C / (q : ℝ) ^ (7.6063 : ℝ) < |Real.pi - (p : ℝ) / (q : ℝ)|
+    C / (q : ℝ) ^ muPi < |Real.pi - (p : ℝ) / (q : ℝ)|
 
 noncomputable def a (n : ℝ) : ℝ := 2 / 3 + 1 / 3 * Real.sin n
 
@@ -198,29 +201,29 @@ private theorem pi_rational_approx_bound (n₁ n₂ k₁ k₂ : ℤ) (ε : ℝ)
 
 private lemma gap_bound_from_irrationality
     (C ε D : ℝ) (hC : 0 < C) (hε : 0 < ε) (hD : 0 < D)
-    (h : C / (2 * D) ^ (7.6063 : ℝ) < ε / D) :
-    (C / ((2 : ℝ) ^ (7.6063 : ℝ) * ε)) ^ ((1 : ℝ) / (7.6063 - 1)) ≤ D := by
-  rw [show (1 : ℝ) / (7.6063 - 1) = ((7.6063 : ℝ) - 1)⁻¹ from one_div _,
+    (h : C / (2 * D) ^ muPi < ε / D) :
+    (C / ((2 : ℝ) ^ muPi * ε)) ^ ((1 : ℝ) / (muPi - 1)) ≤ D := by
+  rw [show (1 : ℝ) / (muPi - 1) = (muPi - 1)⁻¹ from one_div _,
     Real.rpow_inv_le_iff_of_pos (by positivity) hD.le (by positivity)]
-  rw [show (2 * D) ^ (7.6063 : ℝ) = (2 : ℝ) ^ (7.6063 : ℝ) * D ^ (7.6063 : ℝ)
+  rw [show (2 * D) ^ muPi = (2 : ℝ) ^ muPi * D ^ muPi
     from Real.mul_rpow (by positivity) hD.le] at h
-  rw [show D ^ (7.6063 : ℝ) = D ^ ((7.6063 : ℝ) - 1) * D from by
-    conv_lhs => rw [show (7.6063 : ℝ) = (7.6063 : ℝ) - 1 + 1 from by ring]
+  rw [show D ^ muPi = D ^ (muPi - 1) * D from by
+    conv_lhs => rw [show muPi = muPi - 1 + 1 from by ring]
     rw [Real.rpow_add hD, Real.rpow_one]] at h
-  rw [show (2 : ℝ) ^ (7.6063 : ℝ) * (D ^ ((7.6063 : ℝ) - 1) * D) =
-    ((2 : ℝ) ^ (7.6063 : ℝ) * D ^ ((7.6063 : ℝ) - 1)) * D from by ring,
+  rw [show (2 : ℝ) ^ muPi * (D ^ (muPi - 1) * D) =
+    ((2 : ℝ) ^ muPi * D ^ (muPi - 1)) * D from by ring,
     div_lt_div_iff₀ (by positivity) hD] at h
-  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (7.6063 : ℝ) * ε)]
-  nlinarith [mul_comm (D ^ ((7.6063 : ℝ) - 1)) (2 ^ (7.6063 : ℝ) * ε),
-    lt_of_mul_lt_mul_right (show C * D < ε * (2 ^ (7.6063 : ℝ) * D ^ ((7.6063 : ℝ) - 1)) * D by nlinarith) hD.le]
+  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ muPi * ε)]
+  nlinarith [mul_comm (D ^ (muPi - 1)) (2 ^ muPi * ε),
+    lt_of_mul_lt_mul_right (show C * D < ε * (2 ^ muPi * D ^ (muPi - 1)) * D by nlinarith) hD.le]
 
 private lemma C_gap_epsilon_eq (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
-    (C / ((2 : ℝ) ^ (7.6063 : ℝ))) ^ ((1 : ℝ) / (7.6063 - 1)) *
-      ε ^ (-(1 : ℝ) / (7.6063 - 1)) =
-    (C / ((2 : ℝ) ^ (7.6063 : ℝ) * ε)) ^ ((1 : ℝ) / (7.6063 - 1)) := by
-  rw [show C / ((2 : ℝ) ^ (7.6063 : ℝ) * ε) = C / (2 : ℝ) ^ (7.6063 : ℝ) * ε⁻¹ from by field_simp,
+    (C / ((2 : ℝ) ^ muPi)) ^ ((1 : ℝ) / (muPi - 1)) *
+      ε ^ (-(1 : ℝ) / (muPi - 1)) =
+    (C / ((2 : ℝ) ^ muPi * ε)) ^ ((1 : ℝ) / (muPi - 1)) := by
+  rw [show C / ((2 : ℝ) ^ muPi * ε) = C / (2 : ℝ) ^ muPi * ε⁻¹ from by field_simp,
     Real.mul_rpow (by positivity) (by positivity),
-    show ε⁻¹ ^ ((1 : ℝ) / (7.6063 - 1)) = ε ^ (-(1 : ℝ) / (7.6063 - 1)) from by
+    show ε⁻¹ ^ ((1 : ℝ) / (muPi - 1)) = ε ^ (-(1 : ℝ) / (muPi - 1)) from by
       rw [show (ε⁻¹ : ℝ) = ε ^ (-(1 : ℝ)) from (Real.rpow_neg_one ε).symm,
         ← Real.rpow_mul hε.le]
       norm_num]
@@ -228,13 +231,13 @@ private lemma C_gap_epsilon_eq (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
 private lemma apply_PiIrrBound_to_approx
     (C : ℝ) (Q₀ : ℕ)
     (hPi : ∀ (p : ℤ) (q : ℕ), 0 < q → Q₀ ≤ q →
-      C / (q : ℝ) ^ (7.6063 : ℝ) < |Real.pi - (p : ℝ) / (q : ℝ)|)
+      C / (q : ℝ) ^ muPi < |Real.pi - (p : ℝ) / (q : ℝ)|)
     (n₁ n₂ k₁ k₂ : ℤ) (ε : ℝ)
     (hk : k₁ ≠ k₂)
     (hQ : Q₀ ≤ 2 * (k₂ - k₁).natAbs)
     (happrox : |Real.pi - (↑n₂ - ↑n₁) / (2 * (↑k₂ - ↑k₁))| <
       ε / ((k₂ - k₁).natAbs : ℝ)) :
-    C / (2 * ((k₂ - k₁).natAbs : ℝ)) ^ (7.6063 : ℝ) <
+    C / (2 * ((k₂ - k₁).natAbs : ℝ)) ^ muPi <
       ε / ((k₂ - k₁).natAbs : ℝ) := by
   have hk_diff : k₂ - k₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
   suffices ∃ p : ℤ, (↑p : ℝ) / (2 * ((k₂ - k₁).natAbs : ℝ)) =
@@ -269,9 +272,9 @@ lemma gap_principle_of_PiIrrBound (hpi : PiIrrBound) :
       Q₀ ≤ 2 * (k₂ - k₁).natAbs →
       |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε →
       |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε →
-      C_gap * ε ^ (-(1 : ℝ) / (7.6063 - 1)) ≤ |(k₂ - k₁ : ℤ)| := by
+      C_gap * ε ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)| := by
   obtain ⟨C, Q₀, hC, hPi⟩ := hpi
-  refine ⟨(C / ((2 : ℝ) ^ (7.6063 : ℝ))) ^ ((1 : ℝ) / (7.6063 - 1)), Q₀,
+  refine ⟨(C / ((2 : ℝ) ^ muPi)) ^ ((1 : ℝ) / (muPi - 1)), Q₀,
     Real.rpow_pos_of_pos (div_pos hC (by positivity)) _, ?_⟩
   intro n₁ n₂ k₁ k₂ ε hε _hε1 hk hQ h1 h2
   rw [C_gap_epsilon_eq C ε hC hε]
@@ -442,7 +445,7 @@ private lemma k_image_gap_constraint
       Q₀_gap ≤ 2 * (k₂ - k₁).natAbs →
       |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε →
       |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε →
-      C_gap * ε ^ (-(1 : ℝ) / (7.6063 - 1)) ≤ |(k₂ - k₁ : ℤ)|)
+      C_gap * ε ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)|)
     (j : ℕ) (hj : 5 ≤ j) (S : Finset ℕ)
     (hS_sub : S ⊆ Finset.Ico (2^j) (2^(j+1)))
     (hS_bad : ∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩)
@@ -450,7 +453,7 @@ private lemma k_image_gap_constraint
     (K : Finset ℤ) (hK_def : K = S.image (fun (n : ℕ) => k_of (↑n : ℝ))) :
     ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ ≠ k₂ →
       Q₀_gap ≤ 2 * (k₂ - k₁).natAbs →
-      C_gap * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (7.6063 - 1)) ≤ |(k₂ - k₁ : ℤ)| := by
+      C_gap * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)| := by
   intro k₁ hk₁ k₂ hk₂ hk_ne hQ
   rw [hK_def] at hk₁ hk₂
   simp only [Finset.mem_image] at hk₁ hk₂
@@ -513,15 +516,15 @@ private lemma bad_count_in_block_core
       Q₀_gap ≤ 2 * (k₂ - k₁).natAbs →
       |↑n₁ - (Real.pi / 2 + 2 * Real.pi * ↑k₁)| < ε →
       |↑n₂ - (Real.pi / 2 + 2 * Real.pi * ↑k₂)| < ε →
-      C_gap * ε ^ (-(1 : ℝ) / (7.6063 - 1)) ≤ |(k₂ - k₁ : ℤ)|)
+      C_gap * ε ^ (-(1 : ℝ) / (muPi - 1)) ≤ |(k₂ - k₁ : ℤ)|)
     (j : ℕ) (hj : 5 ≤ j) (S : Finset ℕ)
     (hS_sub : S ⊆ Finset.Ico (2^j) (2^(j+1)))
     (hS_bad : ∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩)
     (hS_pos : ∀ n ∈ S, 0 < n) :
       S.card ≤
-      ⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (7.6063 - 1)))) + 1)⌉₊ := by
+      ⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (muPi - 1)))) + 1)⌉₊ := by
   set K := S.image (fun (n : ℕ) => k_of (↑n : ℝ)) with hK_def
-  set Δ := C_gap * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (7.6063 - 1)) with hΔ_def
+  set Δ := C_gap * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (muPi - 1)) with hΔ_def
   have hcluster := integer_clustering_bound K ((2 : ℝ)^(j+1)) Q₀_gap Δ
     (by positivity) (mul_pos hC_gap
       (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _) _))
@@ -531,11 +534,11 @@ private lemma bad_count_in_block_core
       exact_mod_cast k_of_abs_le_of_mem_block j n (hS_sub hn_mem))
     (k_image_gap_constraint C_gap Q₀_gap hC_gap hgap j hj S hS_sub hS_bad hS_pos K hK_def)
   have hrpow_eq : ∀ (C : ℝ) (j : ℕ),
-      C * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (7.6063 - 1)) =
-      C * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (7.6063 - 1))) := fun C j => by
+      C * (((2 : ℝ)^j) ^ (-(1/4 : ℝ))) ^ (-(1 : ℝ) / (muPi - 1)) =
+      C * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (muPi - 1))) := fun C j => by
     congr 1
     rw [← Real.rpow_mul (by positivity)]
-    norm_num [show (7.6063 : ℝ) = (76063 : ℝ) / 10000 by norm_num]
+    norm_num [show muPi = (710321 : ℝ) / 100000 by norm_num]
   rw [hΔ_def, hrpow_eq, show 2 * (2 : ℝ)^(j+1) = (2 : ℝ)^(j+2) from by ring] at hcluster
   rw [(Finset.card_image_of_injOn (k_of_injOn_S j hj S hS_sub hS_bad hS_pos)).symm]
   calc K.card = ⌈(↑K.card : ℝ)⌉₊ := (Nat.ceil_natCast K.card).symm
@@ -543,9 +546,9 @@ private lemma bad_count_in_block_core
 
 private lemma bound_conversion (C_gap : ℝ) (Q₀_gap : ℕ) (hC_gap : 0 < C_gap) :
     ∃ (A : ℝ) (j₁ : ℕ), 0 < A ∧ ∀ j : ℕ, j₁ ≤ j →
-      (⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (7.6063 - 1)))) + 1)⌉₊ : ℝ) ≤
-      A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (7.6063 - 1))) := by
-  set γ := (1 : ℝ)/(4 * (7.6063 - 1))
+      (⌈(↑Q₀_gap + 1 : ℝ) * ((2 : ℝ)^(j+2) / (C_gap * ((2 : ℝ)^j) ^ ((1 : ℝ)/(4 * (muPi - 1)))) + 1)⌉₊ : ℝ) ≤
+      A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) := by
+  set γ := (1 : ℝ)/(4 * (muPi - 1))
   refine ⟨(↑Q₀_gap + 1) * (4 / C_gap) + ↑Q₀_gap + 2, 0, ?_, ?_⟩
   · positivity
   · intro j _
@@ -581,7 +584,7 @@ private lemma bad_count_in_block_assembled (hpi : PiIrrBound) :
       S ⊆ Finset.Ico (2^j) (2^(j+1)) →
       (∀ n ∈ S, ∀ (hn_pos : 0 < n), ¬good ⟨n, hn_pos⟩) →
       (∀ n ∈ S, 0 < n) →
-      (S.card : ℝ) ≤ A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (7.6063 - 1))) := by
+      (S.card : ℝ) ≤ A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) := by
   obtain ⟨C_gap, Q₀, hC_gap, hgap⟩ := gap_principle_of_PiIrrBound hpi
   obtain ⟨A, j₁, hA, hconv⟩ := bound_conversion C_gap Q₀ hC_gap
   refine ⟨A, max 5 j₁, hA, ?_⟩
@@ -597,7 +600,7 @@ private lemma bad_count_in_block (hpi : PiIrrBound) :
         match (inferInstance : Decidable (0 < n)) with
         | .isTrue h => ¬good ⟨n, h⟩
         | .isFalse _ => False)).card ≤
-      A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (7.6063 - 1))) := by
+      A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) := by
   obtain ⟨A, j₀, hA, hassembled⟩ := bad_count_in_block_assembled hpi
   refine ⟨A, j₀, hA, fun j hj => ?_⟩
   set S := (Finset.Ico (2^j) (2^(j+1))).filter (fun n =>
@@ -660,7 +663,7 @@ private lemma dyadic_block_bound (hpi : PiIrrBound) :
     ∀ j : ℕ, j₀ ≤ j →
       ∑ n ∈ (Finset.Ico (2^j) (2^(j+1))), badTerm n ≤ K * r ^ j := by
   obtain ⟨A, j₀, hA, hcount⟩ := bad_count_in_block hpi
-  refine ⟨A, (2 : ℝ) ^ (-(1 : ℝ)/(4 * (7.6063 - 1))), j₀,
+  refine ⟨A, (2 : ℝ) ^ (-(1 : ℝ)/(4 * (muPi - 1))), j₀,
     hA, le_of_lt (Real.rpow_pos_of_pos (by norm_num) _),
     Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num [div_eq_mul_inv]), ?_⟩
   intro j hj
@@ -670,11 +673,11 @@ private lemma dyadic_block_bound (hpi : PiIrrBound) :
           | .isTrue h => ¬good ⟨n, h⟩
           | .isFalse _ => False)).card * (1 / ((2 : ℝ)^j)) :=
         block_sum_le_card_div j
-    _ ≤ A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (7.6063 - 1))) * (1 / ((2 : ℝ)^j)) := by
+    _ ≤ A * ((2 : ℝ)^j) ^ (1 - (1 : ℝ)/(4 * (muPi - 1))) * (1 / ((2 : ℝ)^j)) := by
         apply mul_le_mul_of_nonneg_right
         · exact_mod_cast hcount j hj
         · positivity
-    _ = A * ((2 : ℝ) ^ (-(1 : ℝ)/(4 * (7.6063 - 1)))) ^ j := by
+    _ = A * ((2 : ℝ) ^ (-(1 : ℝ)/(4 * (muPi - 1)))) ^ j := by
         rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
           show (1 : ℝ) / (2 : ℝ) ^ j = ((2 : ℝ)⁻¹) ^ j from by rw [one_div, inv_pow],
           mul_assoc, ← mul_pow, ← Real.rpow_neg_one (2 : ℝ),
```

[gdm]: https://google-deepmind.github.io/formal-conjectures/theorem/?name=BorweinSineSeries.borwein_sine_series
[ZZ2020]: https://arxiv.org/abs/1912.06345
