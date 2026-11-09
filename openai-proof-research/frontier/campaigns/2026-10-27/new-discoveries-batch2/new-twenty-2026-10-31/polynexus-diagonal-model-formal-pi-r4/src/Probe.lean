import PolynexusSrc
#check @Matrix.mul_apply
example (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℕ) : Matrix (Fin n) (Fin n) ℕ := M * N
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℕ) : M * 1 = M := Matrix.mul_one M
#check @Finset.sum_eq_single_of_mem
