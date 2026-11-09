import MathDB378395
set_option warningAsError true
open MathDB378395 MathDB378395.Main MathDB378395.Cert
example : col (0,0,4) ∈ F := (col_mem_F_iff _).mpr (by decide +kernel)
example : col (0,0,0) ∉ F := by
 intro h
 have z := (col_mem_F_iff _).mp h
 have h1 : onCol ellZ (0,0,0) = 1 := by decide +kernel
 omega
example : Module.finrank ℝ (Submodule.span ℝ F) = 43 := finrank_span_F
example : ¬ CollapsingConjecture := collapsing_conjecture_false
