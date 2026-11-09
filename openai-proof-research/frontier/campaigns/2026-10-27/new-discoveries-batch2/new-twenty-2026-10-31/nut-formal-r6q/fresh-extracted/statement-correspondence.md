# Statement correspondence

| Declaration | Exact role | Scope and limits |
| --- | --- | --- |
| `Nut8.PerSupport` | `∀ code ∈ GraphClosure7_000.targets, ∀ C s, Structural C s → SupportCode C code → ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)` | Byte-identical root-fixed interface; 194 catalogue supports. |
| `Nut8.signedPatterns_complete` | A structural matrix with positive ordered parent edges belongs literally to `signedPatterns (unsignedQuotient C) p`. | All integer entries; shared semi-edge sign; one slot per unordered off-tree edge, including double edges; independent signs for magnitude-two loops. |
| `Nut8.signedCatalogue_complete` | Given the specified support permutation and ordered parent tree, some unit switching of `C.submatrix e e` belongs literally to `signedCatalogue code e p`. | Uses inherited universal unsigned augmentation completeness. No transport to r2 labels is assumed. |
| `Nut8.catalogue_signed_normalization` | Every catalogue support has permutation and parent data giving the preceding exact membership for every structural matrix on that support. | Uses the inherited checked tree records for all 194 supports. |
| `Nut8.NewCertificatesNNNN.certificateK` | A literal regenerated matrix has the stated nonzero determinant or zero principal adjugate entry. | Each scalar value is checked through inherited `sparseDet_eq_det` or `sparseDet_principal`; no numerical or unsigned spectral pretest. |
| `Nut8.FiniteSupportNNN.unsigned_enumeration` and `signed_enumerationK` | The unsigned catalogue and each signed-pattern image equal their displayed literal finite sets. | Checked in small batches; the permutation and parents are explicit checked data. |
| `Nut8.FiniteSupportNNN.verified` | Every matrix in that signed catalogue fails the determinant/full-principal-cofactor conjunction. | Derived from the individual scalar certificates. |
| `Nut8.per_support` | `Nut8.PerSupport` | Intended final endpoint. Validation status is recorded in results.json; source presence alone is not proof. |

The graph-theoretic endpoint is outside this lane. `Coverage8` and the composition
with the already proved finite endpoint are assigned to the parallel r5p lane.
This lane does not modify the root interface, establish novelty, self-accept a
result, or change campaign counts. Root adjudicates integration and acceptance.
