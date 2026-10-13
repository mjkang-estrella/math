# I200 reading, validation and failures

2026-10-12. Completed, unsealed. Verdict: **UNRESOLVED; NO SUBSTANTIAL NOMINATION**.

Read AGENTS.md and the pinned manifest in full, the controlling I200 brief in full, the supplied I198 brief/report/analytic record/parent disposition, and the in-place I198 literature record. Read the catalogue's family-095 entry and its three companion summaries only. Source operations and external reading limits are listed in the literature/authentication records.

Partial report, analytic, reading and literature records were written before developing the final arguments. All final assertions were validated by written derivations: expanding the inverse Hessian, canceling Taylor terms in the covariance formula, clearing the graph denominator using homogeneity, factoring the coefficient Gram matrix, and checking the generalized Schur range condition. No executable mathematical checks or numerical data were used.

## Failed routes and their exact limits

- **Reuse the rank-N patch:** impossible for every delta>0 and every old chart point. Q_delta has rank r; A has rank N.
- **Add a fixed positive floor to A:** feasible only after changing t. The cost is at least delta(r-N)||y_s||^2/h. A bounded patch cannot let h go to zero with delta fixed.
- **Repair t rationally:** valid as a feasible graph. Homogeneous denominator clearing produces an exact polynomial patch. Its moment defect is positive at order epsilon^2, so it does not prove nonliftability.
- **Take h,delta to zero after analytic selection:** not justified. Selection domains, derivatives, mixing constants and the chosen center depend on the fixed patch/lift; no uniform bound or extension to the singular parameter stratum was proved. A fixed-epsilon failure also does not contradict a sufficiently-small-epsilon statement with lift-dependent constants.
- **Infer liftability from positive definiteness or pointwise square roots:** the factor is nonlinear in y; it gives no joint affine LMI. Bilinear SOS remains false below a strictly positive threshold.
- **Infer nonliftability from failure of bilinear SOS:** invalid. The separate Choi-Lam companion shows why arbitrary lifts require a stronger obstruction. Its bounded-degree matching proof is specific and was not generalized here.
- **Use a piecewise matrix positivity certificate as an affine lift:** an additional exact representation argument is missing. Approximation errors are not controlled against unbounded X^dagger near the residual singular boundary.
- **Apply smooth-cone theorems globally:** impossible from their stated hypotheses. K_delta retains a nonzero boundary point with two distinct supporting hyperplanes for every delta>0.
- **Obtain a lift-size rate by compactness:** not attempted. The one compactness proof concerns Gram matrices for the fixed mr bilinear monomials and says nothing about arbitrary finite affine lifts.

## Retrieval and provenance limitations

The initial filename query was too broad and produced truncated filenames from old trees. Those names were not read as source evidence and no recursive audit followed. A combined source read exceeded the output limit; complete sections 04 and 05 were subsequently read in separate bounded passages. Section 03 remains a partial new reading, with its accepted seed/inverse-limit contracts distinguished from reread proof operations. A metadata jq query initially used `path` instead of `source_path` and returned an error; it was corrected. These were retrieval/metadata failures, not mathematical tests.

One external PDF, Netzer–Sanyal, was downloaded, fully text-read and retained. Its SHA-256 agrees with the earlier I198 byte hash. Other external papers were read in the web tool only to the stated passages; no full-read copy or byte hash is claimed for them. Secondary search hits were ignored as proof or priority evidence.

Only the four named I200 research files, the I200 literature note, and the full-read PDF copy were written. No subordinate agents, code/experiment files, numerical scans, tests, snapshots, seals, historical replays, staging, commits or publication. I199/I201, ancestors, indexes and I31 were not edited or audited. Eight findings remain accepted; no ninth finding is claimed; both acceptance gates remain with the parent.
