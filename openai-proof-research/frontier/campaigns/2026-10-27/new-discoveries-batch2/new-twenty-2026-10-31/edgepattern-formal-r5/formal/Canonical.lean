import Definitions
namespace EdgePattern.Canonical

-- Root-state dynamic-programming summaries. These are arithmetic definitions;
-- no classification or graph-semantic correctness theorem is claimed here.
structure State where
  size : ℕ
  count : ℕ
  weight : ℕ

def branch (k : Fin 3) : State :=
  if k = 0 then ⟨1,1,7⟩ else if k = 1 then ⟨1,2,16⟩ else ⟨2,1,18⟩

def combine (a b : State) : State :=
  ⟨a.size+b.size,a.count*b.count,a.weight*b.count+b.weight*a.count⟩

def excluded (a b : Fin 3) : State := combine (branch a) (branch b)
def included (a b : Fin 3) : State := ⟨1+a.val+b.val,1,9*(a.val+b.val)⟩

def best (a b : State) : State :=
  if a.size < b.size then b else if b.size < a.size then a
  else ⟨a.size,a.count+b.count,a.weight+b.weight⟩

def summary (a b c d : Fin 3) : State :=
  best (combine (excluded a b) (excluded c d))
    (best (combine (included a b) (excluded c d))
      (combine (excluded a b) (included c d)))

theorem all_81 : ∀ a b c d : Fin 3,
    0 < (summary a b c d).count ∧
    27 * (summary a b c d).count ≤ (summary a b c d).weight := by decide

end EdgePattern.Canonical
