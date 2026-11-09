p='Bridge.lean';s=open(p).read();s=s.replace('  congr 1 <;> rw [monomial_sum_prod] <;> simp','''  congr 1
  · simpa using (monomial_sum_prod (rlmv pi)
      (fun i => Finsupp.single (Sum.inl i) 1) (fun _ => (1 : ℤ))).symm
  · simpa using (monomial_sum_prod (excv pi)
      (fun i => Finsupp.single (Sum.inr i) 1) (fun _ => (1 : ℤ))).symm''');open(p,'w').write(s)
