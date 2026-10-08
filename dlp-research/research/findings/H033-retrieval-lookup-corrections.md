# H033 retrieval lookup: external rejection not established

Status: Factory Fable report COMPLETED; raw retained in
H033-retrieval-lookup-fable-raw.md with exact task ID. Root identified errors;
native Sol independently checked them. Sol originated R1 and explicitly accepts
withdrawal of the original capacity rationale. No experiment or improved solver.

## What the bit ledger establishes

For c=m/w>=1, H=s+t and K=max(d+u+v,H), the unrounded descriptor-slot formula

    alpha*=(3v+H)/(4v+u+H+cK)

is correct BEFORE extra table overhead. It does not universally give alpha*<=1/2.
Counterexample: u=v=30, s=t=32, d=4, c=1.23 gives154/292.72>1/2. Widths u,v
are consistent, for example, with w=600000000 and m=738000000. This is an
arithmetic counterexample to the claimed gate, not an allocated table or run.
In the report's branch u=v=L,s=L+sigma,H<=d+2L, half load instead requires

    sigma+t <= 2(c−1)L+cd.

Its further claim that wide payloads can force alpha*>=.8 is also wrong:
as H dominates fixed widths, alpha* tends to1/(1+c). Indeed alpha*<=2/3 in
this simplified formula, since2K>=v+H implies
2(4v+u+H+cK)−3(3v+H)>=2u>=0. This is not a lookup-cost theorem.

An actual layout still needs integer slot counts, occupancy/sentinel encoding,
alignment, hashes, construction/query scratch and duplicate handling. Four-bit
degree counters require an overflow/failure rule. The source's floor(1.23w)+32
array size is not literally1.23w. None of these is waived by a ratio calculation.

## Unsupported timing, hashing and failure transfers

Three cell ACCESSES need not be three distinct cache misses. Expected probing
counts need their specified hash/query law; reusing a cell index, sorted minimum
or hash conditioned on a successful peel does not establish that law. Packing,
word widths, cache state, dependencies and tag costs are unresolved. The claimed
one-line linear probe and universal lookup dominance are rejected.

Sol accessed [Graf–Lemire](https://arxiv.org/html/1912.08258v3), §§3.1–3.2,
Algorithms1–4. Reported small-set construction success is not a uniform R1
failure bound for actual endpoint archives, counters or capped retries. Nor do
membership-filter operations automatically price seed retrieval. The raw eight-
extra-lines build estimate is not an established difference in complete work.

The proposed fixed-fingerprint rehash repair changes the key contract. It needs
collision detection/handling; persistent fingerprint collisions do not disappear
merely by changing vertex salts. Original seed replay and cap failures remain
paid unless a new protocol demonstrably removes them. Baseline signature
collisions also need handling. Same-hash pointwise containment cannot be combined
with a cheaper different-hash build without a new coupling argument.

## Conditional frozen-archive equations, not EC stopping laws

Accept the report's algebra ONLY in its stipulated ideal landing model: build B
steps, N possible classes, no-build-collision probability exp(−B²/(2N)); on that
event query success hazard is B/N and no query-query detection contributes.
Put x=B/sqrt(N) and deterministically w=theta B. The model gives

    E[T]=sqrt(N)[x+exp(−x²/2)/x],
    E[G]/w=exp(−x²/2)/x²,
    E[G | no build collision]/w=1/x².

Here G counts DP queries under the model's deterministic-rate convention. Actual
random endpoint counts, detection delay, null relations, overflow and coalescence
are not covered. The approximate27% penalty is a MODEL result, not observed EC
work. The raw large-reuse substitution uses the conditional ratio; it cannot
silently replace the unconditional one in the solver ledger.

For a coupled archive and query stream, the real acceptance gate is

    E sum_{j<=G}(lookup_B(X_j)−lookup_R(X_j))
      > E[extra build + retry + replay + other work].

A material eta-fraction gain additionally needs net credit exceeding eta E[W_B].
Constant prices and query/build ratios are shorthands only after their conditional
costs and counts are justified. Common hashing/walk work remains in the complete-
work denominator. If the schedules differ, their stopped walk work must differ
in the ledger too; it is not common by assertion.

## Disposition

The original single-batch hard-peak capacity claim remains falsified by the
accepted descriptor comparator. The residual lookup claim is UNSUPPORTED, not
universally disproved by this report. It currently supplies no favorable complete-
cost regime and warrants no benchmark. Directory occupancy and concrete scratch
qualifications from H033-retrieval-directory-screen.md remain in force. No
resident-only or multi-archive result is inferred. Verified improvement NONE.

Root and native `/root/h010_early_dependencies` independently checked the algebra
and scope. Reviewer used source access only; no edits, runs, imports or children.
Root integrates; no Lean/Audit change or hardware measurement.
