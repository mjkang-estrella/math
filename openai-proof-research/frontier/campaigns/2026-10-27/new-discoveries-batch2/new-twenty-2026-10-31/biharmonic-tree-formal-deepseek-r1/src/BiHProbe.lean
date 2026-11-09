import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix

namespace BiH

variable {V : Type*} [Fintype V] [DecidableEq V]

#check SimpleGraph.isHermitian_lapMatrix
#check Matrix.IsHermitian.eigenvalues
#check Matrix.IsHermitian.rank_eq_card_non_zero_eigs
#check Matrix.IsHermitian.trace_eq_sum_eigenvalues
#check Matrix.IsHermitian.mulVec_eigenvectorBasis
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.det_eq_prod_eigenvalues
#check Matrix.IsHermitian.eigenvalues_eq_zero_iff
#check Fintype.card_subtype_compl
#check SimpleGraph.Preconnected.subsingleton_connectedComponent
#check SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
#check Matrix.rank_eq_finrank_range_toLin
#check LinearMap.finrank_range_add_finrank_ker
#check Matrix.rank_eq_finrank_span_cols
#check Matrix.range_toLin'
#check SimpleGraph.pathGraph
#check SimpleGraph.starGraph
#check SimpleGraph.IsTree
#check SimpleGraph.Iso
#check SimpleGraph.IsTree.card_edgeFinset
#check Module.finrank_pi
#check Fintype.card_eq_one_iff
#check Matrix.IsHermitian.eigenvectorBasis
#check OrthonormalBasis.sum_repr
#check Matrix.rank_eq_card_non_zero_eigs
#check Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg
#check SimpleGraph.posSemidef_lapMatrix
#check Matrix.trace_mul_cycle
#check Matrix.trace_diagonal
#check Unitary.conjStarAlgAut_apply
#check Matrix.IsHermitian.eigenvectorUnitary
#check Matrix.conjStarAlgAut_star_eigenvectorUnitary
#check Fintype.card_subtype
#check Fintype.card_congr

end BiH
