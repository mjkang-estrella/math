module
public import URMatchingRemovedVertices
public import Mathlib.Combinatorics.SimpleGraph.Basic
@[expose] public section
namespace URMatching
open scoped Classical
def permutationAdj {N : ℕ} (σ : PermutationTuples N 100) : BipartiteVertex N → BipartiteVertex N → Prop
  | .inl x, .inr y => ∃ c, σ c x = y
  | .inr y, .inl x => ∃ c, σ c x = y
  | _, _ => False

def permutationGraph {N : ℕ} (σ : PermutationTuples N 100) : SimpleGraph (BipartiteVertex N) where
  Adj := permutationAdj σ
  symm := ⟨by intro u v; cases u <;> cases v <;> exact fun h => h⟩
  loopless := ⟨by intro u; cases u <;> exact fun h => h⟩

abbrev Survivor {N : ℕ} (h : ℕ) (σ : PermutationTuples N 100) :=
  {v : BipartiteVertex N // v ∉ removedVertices N h σ}

def inducedGraph {V : Type*} (G : SimpleGraph V) (P : Set V) : SimpleGraph P where
  Adj u v := G.Adj u.val v.val
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun u => G.loopless.irrefl u.val⟩

def survivorGraph {N : ℕ} (h : ℕ) (σ : PermutationTuples N 100) : SimpleGraph (Survivor h σ) :=
  inducedGraph (permutationGraph σ) {v | v ∉ removedVertices N h σ}
end URMatching
