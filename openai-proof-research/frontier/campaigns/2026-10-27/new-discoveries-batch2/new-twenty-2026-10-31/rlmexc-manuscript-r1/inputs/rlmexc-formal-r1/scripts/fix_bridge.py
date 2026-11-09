p='Bridge.lean'
s=open(p).read().replace('namespace AK350721','namespace AK350721\nopen scoped Classical')
a=s.index('      simpa only [degreeSet_inl'); b=s.index('  · rintro',a)
s=s[:a]+'''      simp only [degreeSet_inl] at this
      split_ifs at this <;> simp_all
    · ext i
      have := congrArg (fun m => m (Sum.inr i)) h
      simp only [degreeSet_inr] at this
      split_ifs at this <;> simp_all
'''+s[b:]
s=s.replace('  simp only [term, degreeSet, monomial_add_single, monomial_add]\n  rw [show (1 : ℤ) = 1 * 1 from rfl, monomial_add]','  unfold term degreeSet\n  rw [show (1 : ℤ) = 1 * 1 from rfl, ← monomial_mul]')
s=s.replace('and_assoc, ', '')
open(p,'w').write(s)
