# Lean source appendix for MathDB 336183

The modules below are listed in compile order.

### `YanceyTables.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Yancey

abbrev Vertex := Fin 34
abbrev Branch := Fin 4

def parent (u : Vertex) : Vertex :=
  (#[0, 0, 0, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26] : Array Vertex)[u.val]!

def depth (r : Vertex) (u : Vertex) : ℕ :=
  (#[
  #[0, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3, 3, 3, 4, 5, 3, 4, 5, 4, 4, 2, 6, 4, 6, 5, 3, 5, 7, 6, 6, 7, 7, 4],
  #[1, 0, 2, 3, 2, 1, 2, 3, 3, 4, 4, 4, 4, 4, 5, 6, 4, 5, 6, 5, 5, 1, 7, 5, 7, 6, 2, 6, 8, 7, 7, 8, 8, 3],
  #[1, 2, 0, 1, 2, 3, 4, 1, 3, 2, 2, 2, 4, 2, 3, 4, 4, 3, 4, 3, 3, 3, 5, 5, 5, 4, 4, 4, 6, 5, 5, 6, 6, 5],
  #[2, 3, 1, 0, 3, 4, 5, 2, 4, 3, 1, 3, 5, 3, 4, 5, 5, 2, 3, 4, 4, 4, 4, 6, 6, 3, 5, 5, 5, 6, 4, 7, 5, 6],
  #[1, 2, 2, 3, 0, 3, 4, 3, 1, 4, 4, 4, 2, 4, 5, 6, 2, 5, 6, 5, 5, 3, 7, 3, 7, 6, 4, 6, 8, 7, 7, 8, 8, 5],
  #[2, 1, 3, 4, 3, 0, 1, 4, 4, 5, 5, 5, 5, 5, 6, 7, 5, 6, 7, 6, 6, 2, 8, 6, 8, 7, 3, 7, 9, 8, 8, 9, 9, 4],
  #[3, 2, 4, 5, 4, 1, 0, 5, 5, 6, 6, 6, 6, 6, 7, 8, 6, 7, 8, 7, 7, 3, 9, 7, 9, 8, 4, 8, 10, 9, 9, 10, 10, 5],
  #[2, 3, 1, 2, 3, 4, 5, 0, 4, 1, 3, 1, 5, 1, 2, 3, 5, 4, 5, 2, 2, 4, 6, 6, 4, 5, 5, 3, 7, 4, 6, 5, 7, 6],
  #[2, 3, 3, 4, 1, 4, 5, 4, 0, 5, 5, 5, 1, 5, 6, 7, 1, 6, 7, 6, 6, 4, 8, 2, 8, 7, 5, 7, 9, 8, 8, 9, 9, 6],
  #[3, 4, 2, 3, 4, 5, 6, 1, 5, 0, 4, 2, 6, 2, 3, 4, 6, 5, 6, 1, 1, 5, 7, 7, 5, 6, 6, 2, 8, 5, 7, 6, 8, 7],
  #[3, 4, 2, 1, 4, 5, 6, 3, 5, 4, 0, 4, 6, 4, 5, 6, 6, 1, 2, 5, 5, 5, 3, 7, 7, 2, 6, 6, 4, 7, 3, 8, 4, 7],
  #[3, 4, 2, 3, 4, 5, 6, 1, 5, 2, 4, 0, 6, 2, 1, 2, 6, 5, 6, 3, 3, 5, 7, 7, 3, 6, 6, 4, 8, 3, 7, 4, 8, 7],
  #[3, 4, 4, 5, 2, 5, 6, 5, 1, 6, 6, 6, 0, 6, 7, 8, 2, 7, 8, 7, 7, 5, 9, 3, 9, 8, 6, 8, 10, 9, 9, 10, 10, 7],
  #[3, 4, 2, 3, 4, 5, 6, 1, 5, 2, 4, 2, 6, 0, 3, 4, 6, 5, 6, 3, 3, 5, 7, 7, 5, 6, 6, 4, 8, 5, 7, 6, 8, 7],
  #[4, 5, 3, 4, 5, 6, 7, 2, 6, 3, 5, 1, 7, 3, 0, 1, 7, 6, 7, 4, 4, 6, 8, 8, 2, 7, 7, 5, 9, 2, 8, 3, 9, 8],
  #[5, 6, 4, 5, 6, 7, 8, 3, 7, 4, 6, 2, 8, 4, 1, 0, 8, 7, 8, 5, 5, 7, 9, 9, 1, 8, 8, 6, 10, 1, 9, 2, 10, 9],
  #[3, 4, 4, 5, 2, 5, 6, 5, 1, 6, 6, 6, 2, 6, 7, 8, 0, 7, 8, 7, 7, 5, 9, 1, 9, 8, 6, 8, 10, 9, 9, 10, 10, 7],
  #[4, 5, 3, 2, 5, 6, 7, 4, 6, 5, 1, 5, 7, 5, 6, 7, 7, 0, 1, 6, 6, 6, 2, 8, 8, 1, 7, 7, 3, 8, 2, 9, 3, 8],
  #[5, 6, 4, 3, 6, 7, 8, 5, 7, 6, 2, 6, 8, 6, 7, 8, 8, 1, 0, 7, 7, 7, 1, 9, 9, 2, 8, 8, 2, 9, 3, 10, 4, 9],
  #[4, 5, 3, 4, 5, 6, 7, 2, 6, 1, 5, 3, 7, 3, 4, 5, 7, 6, 7, 0, 2, 6, 8, 8, 6, 7, 7, 3, 9, 6, 8, 7, 9, 8],
  #[4, 5, 3, 4, 5, 6, 7, 2, 6, 1, 5, 3, 7, 3, 4, 5, 7, 6, 7, 2, 0, 6, 8, 8, 6, 7, 7, 1, 9, 6, 8, 7, 9, 8],
  #[2, 1, 3, 4, 3, 2, 3, 4, 4, 5, 5, 5, 5, 5, 6, 7, 5, 6, 7, 6, 6, 0, 8, 6, 8, 7, 1, 7, 9, 8, 8, 9, 9, 2],
  #[6, 7, 5, 4, 7, 8, 9, 6, 8, 7, 3, 7, 9, 7, 8, 9, 9, 2, 1, 8, 8, 8, 0, 10, 10, 3, 9, 9, 1, 10, 4, 11, 5, 10],
  #[4, 5, 5, 6, 3, 6, 7, 6, 2, 7, 7, 7, 3, 7, 8, 9, 1, 8, 9, 8, 8, 6, 10, 0, 10, 9, 7, 9, 11, 10, 10, 11, 11, 8],
  #[6, 7, 5, 6, 7, 8, 9, 4, 8, 5, 7, 3, 9, 5, 2, 1, 9, 8, 9, 6, 6, 8, 10, 10, 0, 9, 9, 7, 11, 2, 10, 1, 11, 10],
  #[5, 6, 4, 3, 6, 7, 8, 5, 7, 6, 2, 6, 8, 6, 7, 8, 8, 1, 2, 7, 7, 7, 3, 9, 9, 0, 8, 8, 4, 9, 1, 10, 2, 9],
  #[3, 2, 4, 5, 4, 3, 4, 5, 5, 6, 6, 6, 6, 6, 7, 8, 6, 7, 8, 7, 7, 1, 9, 7, 9, 8, 0, 8, 10, 9, 9, 10, 10, 1],
  #[5, 6, 4, 5, 6, 7, 8, 3, 7, 2, 6, 4, 8, 4, 5, 6, 8, 7, 8, 3, 1, 7, 9, 9, 7, 8, 8, 0, 10, 7, 9, 8, 10, 9],
  #[7, 8, 6, 5, 8, 9, 10, 7, 9, 8, 4, 8, 10, 8, 9, 10, 10, 3, 2, 9, 9, 9, 1, 11, 11, 4, 10, 10, 0, 11, 5, 12, 6, 11],
  #[6, 7, 5, 6, 7, 8, 9, 4, 8, 5, 7, 3, 9, 5, 2, 1, 9, 8, 9, 6, 6, 8, 10, 10, 2, 9, 9, 7, 11, 0, 10, 3, 11, 10],
  #[6, 7, 5, 4, 7, 8, 9, 6, 8, 7, 3, 7, 9, 7, 8, 9, 9, 2, 3, 8, 8, 8, 4, 10, 10, 1, 9, 9, 5, 10, 0, 11, 1, 10],
  #[7, 8, 6, 7, 8, 9, 10, 5, 9, 6, 8, 4, 10, 6, 3, 2, 10, 9, 10, 7, 7, 9, 11, 11, 1, 10, 10, 8, 12, 3, 11, 0, 12, 11],
  #[7, 8, 6, 5, 8, 9, 10, 7, 9, 8, 4, 8, 10, 8, 9, 10, 10, 3, 4, 9, 9, 9, 5, 11, 11, 2, 10, 10, 6, 11, 1, 12, 0, 11],
  #[4, 3, 5, 6, 5, 4, 5, 6, 6, 7, 7, 7, 7, 7, 8, 9, 7, 8, 9, 8, 8, 2, 10, 8, 10, 9, 1, 9, 11, 10, 10, 11, 11, 0]
  ] : Array (Array ℕ))[r.val]![u.val]!

def previous (r : Vertex) (u : Vertex) : Vertex :=
  (#[
  #[0, 0, 0, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[1, 1, 0, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 2, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 3, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[4, 0, 0, 2, 4, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[1, 5, 0, 2, 0, 5, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[1, 5, 0, 2, 0, 6, 6, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 7, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[4, 0, 0, 2, 8, 1, 5, 2, 8, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 9, 4, 9, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 10, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 11, 4, 7, 3, 11, 8, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[4, 0, 0, 2, 8, 1, 5, 2, 12, 7, 3, 7, 12, 7, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 13, 4, 7, 3, 7, 8, 13, 11, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 11, 4, 7, 3, 14, 8, 7, 14, 14, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 11, 4, 7, 3, 14, 8, 7, 15, 15, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[4, 0, 0, 2, 8, 1, 5, 2, 16, 7, 3, 7, 8, 7, 11, 14, 16, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 17, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 18, 18, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 9, 4, 19, 3, 7, 8, 7, 11, 14, 8, 10, 17, 19, 9, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 9, 4, 20, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 20, 1, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[1, 21, 0, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 21, 18, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 18, 22, 9, 9, 1, 22, 16, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[4, 0, 0, 2, 8, 1, 5, 2, 16, 7, 3, 7, 8, 7, 11, 14, 23, 10, 17, 9, 9, 1, 18, 23, 15, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 11, 4, 7, 3, 14, 8, 7, 15, 24, 8, 10, 17, 9, 9, 1, 18, 16, 24, 17, 21, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 25, 17, 9, 9, 1, 18, 16, 15, 25, 21, 20, 22, 15, 25, 24, 30, 26],
  #[1, 21, 0, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 26, 18, 16, 15, 17, 26, 20, 22, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 9, 4, 20, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 27, 1, 18, 16, 15, 17, 21, 27, 22, 15, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 18, 22, 9, 9, 1, 28, 16, 15, 17, 21, 20, 28, 15, 25, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 11, 4, 7, 3, 14, 8, 7, 15, 29, 8, 10, 17, 9, 9, 1, 18, 16, 15, 17, 21, 20, 22, 29, 25, 24, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 25, 17, 9, 9, 1, 18, 16, 15, 30, 21, 20, 22, 15, 30, 24, 30, 26],
  #[2, 0, 7, 2, 0, 1, 5, 11, 4, 7, 3, 14, 8, 7, 15, 24, 8, 10, 17, 9, 9, 1, 18, 16, 31, 17, 21, 20, 22, 15, 25, 31, 30, 26],
  #[2, 0, 3, 10, 0, 1, 5, 2, 4, 7, 17, 7, 8, 7, 11, 14, 8, 25, 17, 9, 9, 1, 18, 16, 15, 30, 21, 20, 22, 15, 32, 24, 32, 26],
  #[1, 21, 0, 2, 0, 1, 5, 2, 4, 7, 3, 7, 8, 7, 11, 14, 8, 10, 17, 9, 9, 26, 18, 16, 15, 17, 33, 20, 22, 15, 25, 24, 30, 33]
  ] : Array (Array Vertex))[r.val]![u.val]!

def branch (r : Vertex) (u : Vertex) : Branch :=
  (#[
  #[0, 0, 1, 1, 2, 0, 0, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 2, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0],
  #[0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2],
  #[0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 2, 2, 2, 0, 1, 1, 2, 2, 0, 1, 0, 2, 1, 0, 2, 1, 2, 1, 2, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 2, 2, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 2, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 2, 0, 2, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ] : Array (Array Branch))[r.val]![u.val]!

def anchor (r : Vertex) (u : Branch) : Vertex :=
  (#[
  #[1, 2, 4, 0],
  #[0, 5, 21, 1],
  #[0, 3, 7, 2],
  #[2, 10, 3, 3],
  #[0, 8, 4, 4],
  #[1, 6, 5, 5],
  #[5, 6, 6, 6],
  #[2, 9, 11, 13],
  #[4, 12, 16, 8],
  #[7, 19, 20, 9],
  #[3, 17, 10, 10],
  #[7, 14, 11, 11],
  #[8, 12, 12, 12],
  #[7, 13, 13, 13],
  #[11, 15, 14, 14],
  #[14, 24, 29, 15],
  #[8, 23, 16, 16],
  #[10, 18, 25, 17],
  #[17, 22, 18, 18],
  #[9, 19, 19, 19],
  #[9, 27, 20, 20],
  #[1, 26, 21, 21],
  #[18, 28, 22, 22],
  #[16, 23, 23, 23],
  #[15, 31, 24, 24],
  #[17, 30, 25, 25],
  #[21, 33, 26, 26],
  #[20, 27, 27, 27],
  #[22, 28, 28, 28],
  #[15, 29, 29, 29],
  #[25, 32, 30, 30],
  #[24, 31, 31, 31],
  #[30, 32, 32, 32],
  #[26, 33, 33, 33]
  ] : Array (Array Vertex))[r.val]![u.val]!

def momentTable (r : Vertex) (u : Branch) : ℤ :=
  (#[
  #[15, 98, 13, 0],
  #[139, 3, 6, 0],
  #[40, 36, 40, 0],
  #[105, 27, 0, 0],
  #[142, 8, 0, 0],
  #[177, 1, 0, 0],
  #[210, 0, 0, 0],
  #[98, 8, 19, 1],
  #[172, 1, 3, 0],
  #[148, 1, 3, 0],
  #[131, 19, 0, 0],
  #[135, 13, 0, 0],
  #[208, 0, 0, 0],
  #[158, 0, 0, 0],
  #[164, 8, 0, 0],
  #[194, 3, 1, 0],
  #[205, 1, 0, 0],
  #[158, 6, 6, 0],
  #[195, 3, 0, 0],
  #[184, 0, 0, 0],
  #[181, 1, 0, 0],
  #[173, 3, 0, 0],
  #[227, 1, 0, 0],
  #[238, 0, 0, 0],
  #[227, 1, 0, 0],
  #[195, 3, 0, 0],
  #[205, 1, 0, 0],
  #[214, 0, 0, 0],
  #[260, 0, 0, 0],
  #[230, 0, 0, 0],
  #[227, 1, 0, 0],
  #[260, 0, 0, 0],
  #[260, 0, 0, 0],
  #[238, 0, 0, 0]
  ] : Array (Array ℤ))[r.val]![u.val]!

def squareTable (r : Vertex) : ℤ :=
  (#[582, 808, 476, 598, 816, 1126, 1512, 582, 1118, 836, 788, 792, 1500, 864, 1070, 1416, 1492, 1046, 1396, 1170, 1162, 1114, 1814, 1934, 1834, 1396, 1488, 1556, 2300, 1842, 1814, 2320, 2300, 1930] : Array ℤ)[r.val]!

end Yancey
```

### `YanceyTree.lean`

```lean
import YanceyTables
import Mathlib.Tactic.FinCases

namespace Yancey

open SimpleGraph

def edge (u v : Vertex) : Prop :=
  (u ≠ 0 ∧ parent u = v) ∨ (v ≠ 0 ∧ parent v = u)

instance (u v : Vertex) : Decidable (edge u v) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

theorem parent_decreases : ∀ u : Vertex, u ≠ 0 → parent u < u := by decide

def tree : SimpleGraph Vertex where
  Adj := edge
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨hne, he⟩ | ⟨hne, he⟩ <;>
      exact (ne_of_lt (parent_decreases u hne)) he⟩

instance : DecidableRel tree.Adj := fun u v => inferInstanceAs (Decidable (edge u v))

private theorem depth_zero : ∀ r : Vertex, depth r r = 0 := by decide

private theorem depth_bound : ∀ r u : Vertex, depth r u ≤ 33 := by
  intro r
  fin_cases r <;> decide

private theorem depth_parent : ∀ r u : Vertex, u ≠ 0 →
    depth r u ≤ depth r (parent u) + 1 ∧ depth r (parent u) ≤ depth r u + 1 := by
  intro r
  fin_cases r <;> decide

private theorem depth_step (r u v : Vertex) (h : edge u v) :
    depth r u ≤ depth r v + 1 := by
  rcases h with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
  · exact (depth_parent r u hu).1
  · exact (depth_parent r v hv).2

private theorem descent : ∀ r u : Vertex, u ≠ r →
    edge u (previous r u) ∧ depth r u = depth r (previous r u) + 1 := by
  intro r
  fin_cases r <;> decide

theorem branch_step : ∀ r u : Vertex, u ≠ r →
    if previous r u = r then anchor r (branch r u) = u
    else branch r (previous r u) = branch r u := by
  intro r
  fin_cases r <;> decide

theorem descending_edge (r u : Vertex) (h : u ≠ r) :
    tree.Adj u (previous r u) := (descent r u h).1

theorem descending_depth (r u : Vertex) (h : u ≠ r) :
    depth r u = depth r (previous r u) + 1 := (descent r u h).2

private theorem walk_of_depth (r u : Vertex) :
    ∃ w : tree.Walk u r, w.length = depth r u := by
  generalize hn : depth r u = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hu : u = r
    · subst u
      exact ⟨.nil, by simpa only [depth_zero, Walk.length_nil] using hn⟩
    · have hs := descending_depth r u hu
      obtain ⟨w, hw⟩ := ih (depth r (previous r u)) (by omega) (previous r u) rfl
      exact ⟨.cons (descending_edge r u hu) w, by simpa [hw] using hs.symm.trans hn⟩

theorem tree_connected : tree.Connected := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨wu, _⟩ := walk_of_depth 0 u
  obtain ⟨wv, _⟩ := walk_of_depth 0 v
  exact ⟨wu.append wv.reverse⟩

private theorem depth_le_walk (r : Vertex) {u v : Vertex} (w : tree.Walk u v) :
    depth r u ≤ depth r v + w.length := by
  induction w with
  | nil => simp
  | @cons u z v h _ ih =>
    have hs := depth_step r u z h
    simp only [Walk.length_cons]
    omega

/-- The complete table is certified against Mathlib's shortest-walk distance. -/
theorem dist_eq_depth (r u : Vertex) : tree.dist u r = depth r u := by
  obtain ⟨w, hw⟩ := walk_of_depth r u
  obtain ⟨p, hp⟩ := tree_connected.exists_walk_length_eq_dist u r
  have hl := depth_le_walk r p
  rw [depth_zero, zero_add, hp] at hl
  exact (hw ▸ dist_le w).antisymm hl

theorem tree_dist_bound (u r : Vertex) : tree.dist u r ≤ 33 := by
  rw [dist_eq_depth]
  exact depth_bound r u

private def degreeCount (u : Vertex) : ℕ :=
  (Finset.univ.filter fun v => edge u v).card

private theorem degreeCount_eq (u : Vertex) : tree.degree u = degreeCount u := by
  unfold degreeCount SimpleGraph.degree
  congr 1
  ext v
  simp only [tree.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

private theorem degree_total : ∑ u : Vertex, degreeCount u = 66 := by decide

theorem tree_isTree : tree.IsTree := by
  refine isTree_iff_connected_and_card.mpr ⟨tree_connected, ?_⟩
  have h := tree.sum_degrees_eq_twice_card_edges
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
  simp only [degreeCount_eq, degree_total] at h
  simp only [Fintype.card_fin]
  omega

end Yancey
```

### `YanceyStatement.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Yancey

open SimpleGraph

/-- The 1-Lipschitz condition for the unweighted graph distance. -/
def LipschitzOn {V : Type} (G : SimpleGraph V) (X : V → ℝ) : Prop :=
  ∀ u v, |X u - X v| ≤ (G.dist u v : ℝ)

/-- The edge form of the same constraint on connected graphs. -/
def EdgeLipschitz {V : Type} (G : SimpleGraph V) (X : V → ℝ) : Prop :=
  ∀ u v, G.Adj u v → |X u - X v| ≤ 1

theorem LipschitzOn.edge {V : Type} {G : SimpleGraph V} {X : V → ℝ}
    (h : LipschitzOn G X) : EdgeLipschitz G X := by
  intro u v he
  simpa only [dist_eq_one_iff_adj.mpr he, Nat.cast_one] using h u v

theorem EdgeLipschitz.metric {V : Type} {G : SimpleGraph V} {X : V → ℝ}
    (h : EdgeLipschitz G X) (hc : G.Connected) : LipschitzOn G X := by
  have walkBound {u v : V} (w : G.Walk u v) : |X u - X v| ≤ (w.length : ℝ) := by
    induction w with
    | nil => simp
    | @cons u z v he _ ih =>
      calc
        |X u - X v| ≤ |X u - X z| + |X z - X v| := abs_sub_le ..
        _ ≤ 1 + _ := add_le_add (h u z he) ih
        _ = _ := by simp [add_comm]
  intro u v
  obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist u v
  exact hw ▸ walkBound w

/-- Variance for the uniform probability on vertices, in the form E[X²] − E[X]². -/
noncomputable def variance {V : Type} [Fintype V] (X : V → ℝ) : ℝ :=
  (∑ v, X v ^ 2) / (Fintype.card V : ℝ) -
    ((∑ v, X v) / (Fintype.card V : ℝ)) ^ 2

/-- X is feasible and realizes the maximum of the uniform variance. -/
def VarianceOptimal {V : Type} [Fintype V] (G : SimpleGraph V) (X : V → ℝ) : Prop :=
  LipschitzOn G X ∧ ∀ Y, LipschitzOn G Y → variance Y ≤ variance X

def IsPathGraph {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.pathGraph (Fintype.card V))

def CentredAt {V : Type} (G : SimpleGraph V) (X : V → ℝ) (r : V) : Prop :=
  ∀ u, |X u - X r| = (G.dist u r : ℝ)

def YanceyConj14 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → ∀ X, VarianceOptimal T X →
      ∃ r, CentredAt T X r ∧ (¬ IsPathGraph T → 3 ≤ T.degree r)

end Yancey
```

### `YanceyVariance.lean`

```lean
import YanceyTree
import YanceyStatement
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real

namespace Yancey

open Set

def score {A : Type} [CommRing A] (X : Vertex → A) : A :=
  34 * (∑ u, X u ^ 2) - (∑ u, X u) ^ 2

theorem score_shift (X : Vertex → ℝ) (a : ℝ) :
    score (fun u => X u - a) = score X := by
  have hsum : (∑ u, (X u - a)) = (∑ u, X u) - 34 * a := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  have hsq : (∑ u, (X u - a) ^ 2) =
      (∑ u, X u ^ 2) - 2 * a * (∑ u, X u) + 34 * a ^ 2 := by
    simp_rw [sub_sq, mul_right_comm (2 : ℝ) _ a, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [nsmul_eq_mul]
  unfold score
  rw [hsum, hsq]
  ring

theorem variance_eq_score (X : Vertex → ℝ) : variance X = score X / 34 ^ 2 := by
  unfold variance score
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  ring

theorem variance_shift (X : Vertex → ℝ) (a : ℝ) :
    variance (fun u => X u - a) = variance X := by
  rw [variance_eq_score, score_shift, variance_eq_score]

theorem score_intCast (X : Vertex → ℤ) :
    score (fun u => (X u : ℝ)) = ((score X : ℤ) : ℝ) := by
  simp [score]

private def normalized : Set (Vertex → ℝ) :=
  { X | LipschitzOn tree X ∧ X 0 = 0 }

private theorem normalized_closed : IsClosed normalized := by
  have h : normalized =
      ({X : Vertex → ℝ | X 0 = 0}) ∩
        ⋂ u : Vertex, ⋂ v : Vertex, {X : Vertex → ℝ | |X u - X v| ≤ (tree.dist u v : ℝ)} := by
    ext X
    simp [normalized, LipschitzOn, and_comm]
  rw [h]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_iInter fun u => isClosed_iInter fun v =>
      isClosed_le ((continuous_apply u).sub (continuous_apply v)).abs continuous_const)

private theorem normalized_compact : IsCompact normalized := by
  apply (isCompact_pi_infinite (fun _ : Vertex => isCompact_Icc (α := ℝ)
    (a := -33) (b := 33))).of_isClosed_subset normalized_closed
  intro X hX
  have hX' : LipschitzOn tree X ∧ X 0 = 0 := hX
  intro u
  have h := hX'.1 u 0
  rw [hX'.2, sub_zero] at h
  have hD : (tree.dist u 0 : ℝ) ≤ 33 := by
    exact_mod_cast tree_dist_bound u 0
  exact abs_le.mp (h.trans hD)

private theorem variance_continuous : Continuous (variance (V := Vertex)) := by
  unfold variance
  exact ((continuous_finsetSum _ fun u _ => (continuous_apply u).pow 2).div_const _).sub
    (((continuous_finsetSum _ fun u _ => continuous_apply u).div_const _).pow 2)

theorem tree_has_optimum : ∃ X : Vertex → ℝ, VarianceOptimal tree X := by
  have hne : normalized.Nonempty := ⟨fun _ => 0, ⟨by simp [LipschitzOn], rfl⟩⟩
  obtain ⟨X, hX, hmax⟩ := normalized_compact.exists_isMaxOn hne variance_continuous.continuousOn
  have hX' : LipschitzOn tree X ∧ X 0 = 0 := hX
  refine ⟨X, hX'.1, ?_⟩
  intro Y hY
  have hnorm : (fun u => Y u - Y 0) ∈ normalized := by
    refine ⟨?_, sub_self _⟩
    intro u v
    convert hY u v using 2; ring
  have hle := hmax hnorm
  change variance (fun u => Y u - Y 0) ≤ variance X at hle
  simpa only [variance_shift] using hle

end Yancey
```

### `YanceyMoments.lean`

```lean
import YanceyTree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Yancey

def signed (b : Bool) (x : ℤ) : ℤ := if b then x else -x

def signedDepth (r : Vertex) (s : Branch → Bool) (u : Vertex) : ℤ :=
  signed (s (branch r u)) (depth r u)

def allSigns (a b c d : Bool) (k : Branch) : Bool :=
  (#[a, b, c, d] : Array Bool)[k.val]!

private theorem signed_mul (b : Bool) (x : ℤ) : signed b x = signed b 1 * x := by
  cases b <;> simp [signed]

private theorem signed_sq (b : Bool) (x : ℤ) : signed b x ^ 2 = x ^ 2 := by
  cases b <;> simp [signed]

private theorem squareTable_eq : ∀ r : Vertex,
    (∑ u : Vertex, (depth r u : ℤ) ^ 2) = squareTable r := by
  intro r
  fin_cases r <;> decide

private theorem momentTable_eq : ∀ (r : Vertex) (k : Branch),
    (∑ u : Vertex, if branch r u = k then (depth r u : ℤ) else 0) = momentTable r k := by
  intro r
  fin_cases r <;> decide

theorem signedDepth_sum_sq (r : Vertex) (s : Branch → Bool) :
    (∑ u, signedDepth r s u ^ 2) = squareTable r := by
  simpa only [signedDepth, signed_sq] using squareTable_eq r

theorem signedDepth_sum (r : Vertex) (s : Branch → Bool) :
    (∑ u, signedDepth r s u) = ∑ k, signed (s k) (momentTable r k) := by
  calc
    (∑ u, signedDepth r s u) =
        ∑ u : Vertex, ∑ k : Branch,
          if branch r u = k then signed (s k) (depth r u) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_eq_single (branch r u)]
      · simp [signedDepth]
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    _ = ∑ k, signed (s k) (momentTable r k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← momentTable_eq r k, signed_mul (s k), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : branch r u = k
      · simpa only [ite_eq_left h] using signed_mul (s k) (depth r u)
      · simp [h]

theorem moment_score_certificate : ∀ (r : Vertex) (a b c d : Bool),
    34 * squareTable r - (∑ k, signed (allSigns a b c d k) (momentTable r k)) ^ 2 ≤ 14888 := by
  intro r
  fin_cases r <;> decide

end Yancey
```

### `YanceyRefutation.lean`

```lean
import YanceyVariance
import YanceyMoments

namespace Yancey

def competitor (u : Vertex) : ℤ :=
  (#[0, 1, -1, -2, 1, 2, 3, -2, 2, -3, -3, -3, 3, -1, -4, -5, 3,
    -4, -5, -4, -4, 2, -6, 4, -6, -5, 3, -5, -7, -6, -6, -7, -7, 4] : Array ℤ)[u.val]!

private theorem competitor_parentInt : ∀ u : Vertex, u ≠ 0 →
    |competitor u - competitor (parent u)| ≤ 1 := by decide

private theorem competitor_edgeInt (u v : Vertex) (h : edge u v) :
    |competitor u - competitor v| ≤ 1 := by
  rcases h with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
  · exact competitor_parentInt u hu
  · rw [abs_sub_comm]
    exact competitor_parentInt v hv

theorem competitor_feasible : LipschitzOn tree (fun u => (competitor u : ℝ)) := by
  apply EdgeLipschitz.metric _ tree_connected
  intro u v he
  change |(competitor u : ℝ) - (competitor v : ℝ)| ≤ 1
  exact_mod_cast competitor_edgeInt u v he

private theorem competitor_scoreInt : score competitor = 14892 := by decide

theorem competitor_score : score (fun u => (competitor u : ℝ)) = 14892 := by
  rw [score_intCast, competitor_scoreInt]
  norm_num

private theorem signedDepth_bound (r : Vertex) (s : Branch → Bool) :
    score (signedDepth r s) ≤ (14888 : ℤ) := by
  have hs : allSigns (s 0) (s 1) (s 2) (s 3) = s := by
    funext k
    fin_cases k <;> rfl
  rw [score, signedDepth_sum_sq, signedDepth_sum, ← hs]
  exact moment_score_certificate r (s 0) (s 1) (s 2) (s 3)

private noncomputable def nonnegSign (x : ℝ) : Bool :=
  if 0 ≤ x then true else false

private theorem same_sign {x y : ℝ} (hx : 1 ≤ |x|) (hy : 1 ≤ |y|)
    (hxy : |x - y| ≤ 1) : nonnegSign x = nonnegSign y := by
  have hb := abs_le.mp hxy
  by_cases xp : 0 ≤ x <;> by_cases yp : 0 ≤ y
  · simp [nonnegSign, xp, yp]
  · rw [abs_of_nonneg xp] at hx
    rw [abs_of_neg (lt_of_not_ge yp)] at hy
    exfalso
    linarith
  · rw [abs_of_neg (lt_of_not_ge xp)] at hx
    rw [abs_of_nonneg yp] at hy
    exfalso
    linarith
  · simp [nonnegSign, xp, yp]

private theorem centred_representation {X : Vertex → ℝ} (hX : LipschitzOn tree X)
    {r : Vertex} (hr : CentredAt tree X r) :
    ∃ s : Branch → Bool, (fun u => X u - X r) = fun u => (signedDepth r s u : ℝ) := by
  let z := fun u => X u - X r
  let s := fun k => nonnegSign (z (anchor r k))
  have hAbs (u : Vertex) : |z u| = (depth r u : ℝ) := by
    simpa only [dist_eq_depth] using hr u
  have sign_eq (u : Vertex) (hu : u ≠ r) : nonnegSign (z u) = s (branch r u) := by
    generalize hn : depth r u = n
    induction n using Nat.strong_induction_on generalizing u with
    | h n ih =>
      have hb := branch_step r u hu
      by_cases hp : previous r u = r
      · rw [ite_eq_left hp] at hb
        change nonnegSign (z u) = nonnegSign (z (anchor r (branch r u)))
        rw [hb]
      · rw [ite_eq_right hp] at hb
        have hdu := descending_depth r u hu
        have hdp := descending_depth r (previous r u) hp
        have hU : 1 ≤ |z u| := by
          rw [hAbs]
          exact_mod_cast (show 1 ≤ depth r u by omega)
        have hP : 1 ≤ |z (previous r u)| := by
          rw [hAbs]
          exact_mod_cast (show 1 ≤ depth r (previous r u) by omega)
        have hE : |z u - z (previous r u)| ≤ 1 := by
          have he := hX.edge u (previous r u) (descending_edge r u hu)
          convert he using 2; dsimp [z]; ring
        calc
          nonnegSign (z u) = nonnegSign (z (previous r u)) := same_sign hU hP hE
          _ = s (branch r (previous r u)) :=
            ih _ (by omega) (previous r u) hp rfl
          _ = s (branch r u) := congrArg s hb
  refine ⟨s, funext fun u => ?_⟩
  change z u = (signedDepth r s u : ℝ)
  by_cases hu : u = r
  · subst u
    have hz : depth r r = 0 := by rw [← dist_eq_depth, SimpleGraph.dist_self]
    simp [z, signedDepth, signed, hz]
  · unfold signedDepth signed
    rw [← sign_eq u hu]
    have ha := hAbs u
    by_cases h : 0 ≤ z u
    · rw [abs_of_nonneg h] at ha
      simpa [nonnegSign, h] using ha
    · rw [abs_of_neg (lt_of_not_ge h)] at ha
      have he : z u = -(depth r u : ℝ) := by linarith
      simpa [nonnegSign, h] using he

theorem centred_score_le {X : Vertex → ℝ} (hX : LipschitzOn tree X)
    {r : Vertex} (hr : CentredAt tree X r) : score X ≤ 14888 := by
  obtain ⟨s, hs⟩ := centred_representation hX hr
  rw [← score_shift X (X r), hs, score_intCast]
  exact_mod_cast signedDepth_bound r s

theorem optimum_has_no_centre (X : Vertex → ℝ) (hX : VarianceOptimal tree X) :
    ∀ r : Vertex, ∃ u : Vertex, |X u - X r| ≠ (tree.dist u r : ℝ) := by
  intro r
  by_contra hn
  have hc : CentredAt tree X r := fun u => not_not.mp (fun h => hn ⟨u, h⟩)
  have hub := centred_score_le hX.1 hc
  have hlb := hX.2 _ competitor_feasible
  rw [variance_eq_score, variance_eq_score, competitor_score] at hlb
  linarith

/-- A nonvacuous counterexample to the first clause. -/
theorem counterexample :
    ∃ (T : SimpleGraph Vertex) (X : Vertex → ℝ),
      T.IsTree ∧ VarianceOptimal T X ∧
        ∀ r : Vertex, ∃ u : Vertex, |X u - X r| ≠ (T.dist u r : ℝ) := by
  obtain ⟨X, hX⟩ := tree_has_optimum
  exact ⟨tree, X, tree_isTree, hX, optimum_has_no_centre X hX⟩

/-- The negation of Yancey's Conjecture 1.4, including its degree clause. -/
theorem mathdb336183 : ¬ YanceyConj14 := by
  intro h
  obtain ⟨X, hX⟩ := tree_has_optimum
  obtain ⟨r, hr, _⟩ := h Vertex tree tree_isTree X hX
  obtain ⟨u, hu⟩ := optimum_has_no_centre X hX r
  exact hu (hr u)

#check mathdb336183
#check counterexample
#check optimum_has_no_centre
#check tree_has_optimum
#check tree_isTree
#check dist_eq_depth
#check centred_score_le
#check competitor_feasible
#check competitor_score
#print YanceyConj14
#print CentredAt
#print VarianceOptimal
#print LipschitzOn
#print EdgeLipschitz
#print variance
#print IsPathGraph
#print axioms mathdb336183
#print axioms counterexample
#print axioms optimum_has_no_centre
#print axioms tree_has_optimum
#print axioms tree_isTree
#print axioms dist_eq_depth
#print axioms centred_score_le
#print axioms competitor_feasible
#print axioms competitor_score

end Yancey
```
