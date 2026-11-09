import ConcreteR2
open EdgePattern EdgePattern.Concrete
example : Independent graph ({0,1} : Finset V) := by
  exact (independent_iff _).mp (by decide)
