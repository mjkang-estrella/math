# Repartitioning and the incremental conjecture for set multipartite Ramsey numbers

Certificate paths below refer to the original packet `../set-multipartite-ramsey-337410-formal-paper-sol61-20261120-r1/`; this revision changes only the manuscript.

## Abstract

For \(s\ge2\), let \(M_s(n)=M_s(C_4;K_{1,n})\) be the set multipartite Ramsey number with \(c\) classes of \(s\) vertices. We prove the conjecture of Gonçalves, Monte Carmelo and Nakaoka that \(M_s(n+1)\le M_s(n)+1\) for all \(s,n\ge2\). The proof allows the partition of the surviving vertices to change after a deletion. A transposition suffices when \(s\ge3\). For \(s=2\), a weak friendship argument and a dense-complement matching repair the partition into pairs. The complete Lean certificate includes finiteness of the defining minimum and every relabelling used in the proof.

## 1. Source statement and literal definitions

The source is C. J. F. Gonçalves, E. L. Monte Carmelo and I. N. Nakaoka, *Projective planes and set multipartite Ramsey numbers for C₄ versus star*, [arXiv:1710.06383v1](https://arxiv.org/pdf/1710.06383v1), §§1.1–1.2 and Conjecture 2.3. The cached source text is in `evidence/1710.06383v1.txt`; its hash is recorded in `packet-verification.json`. The arXiv version was posted on 17 October 2017; the PDF itself bears the date 14 October 2018.

The source defines the host as a complete multipartite graph with c equal classes of size s. For fixed positive s, its set multipartite Ramsey number is the least positive c such that every subgraph of this host contains the first forbidden graph or its complement relative to the host contains the second. Section 1.2 specializes the first graph to the four-cycle and the second to the star with n leaves, writing this number as \(M_s\(n\)\). Its case s=1 is the ordinary graph Ramsey number.

Conjecture 2.3 asks whether

\[
 M_s(n+1)\le M_s(n)+1\qquad(s\ge2,\ n\ge2).
\]

This is MathDB 337410, *The incremental conjecture for set multipartite Ramsey numbers*. The local record was obtained with `python3 -I ../root-intake-r60/corpus_row.py 337410` from this lane, and is retained in `evidence/mathdb-337410.txt`. Its description calls the host “complete balanced s-partite”; the source instead explicitly has **c classes of size s**. We follow the source's convention, as required by the independent statement review. A graph may be taken to be spanning, since adding isolated vertices does not change the existence of a forbidden copy. All copies are subgraph copies, not necessarily induced.

Here are the corresponding certificate definitions, in namespace `MultipartiteRamsey`:

```lean
def Host (c s : ℕ) : SimpleGraph (Fin c × Fin s) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

def HasC4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b x y, a ≠ b ∧ x ≠ y ∧ G.Adj a x ∧ G.Adj a y ∧ G.Adj b x ∧ G.Adj b y

noncomputable def HasStarInRelCompl (c s n : ℕ)
    (G : SimpleGraph (Fin c × Fin s)) : Prop := by
  classical
  exact ∃ v, n ≤ (Finset.univ.filter (fun w => v.1 ≠ w.1 ∧ ¬ G.Adj v w)).card

def RamseyProp (s n c : ℕ) : Prop :=
  0 < c ∧ ∀ G : SimpleGraph (Fin c × Fin s),
    G ≤ Host c s → HasC4 G ∨ HasStarInRelCompl c s n G

noncomputable def M (s n : ℕ) : ℕ := by
  classical
  exact if h : ∃ c, RamseyProp s n c then Nat.find h else 0
```

The predicate `HasC4` exhibits two distinct vertices with two distinct common neighbors. Looplessness forces the four displayed vertices to be distinct. The star predicate counts neighbors in the complement **relative to the host**; edges within a class are excluded. A star with \(n\) leaves exists precisely when some vertex has at least \(n\) such neighbors. Positivity of the number of classes is part of `RamseyProp`.

The theorem `ramseyProp_exists` proves existence for every \(s,n\ge1\). Consequently `M_spec` proves attainment, `M_le` proves minimality, and `M_ge_two` proves \(M_s(n)\ge2\) throughout that domain. The zero fallback cannot be used in the final theorem. As a small-case check, `M_one` proves \(M_s(1)=2\) for \(s\ge2\).

## 2. Elementary graph lemmas

Write \(N\) for the order of a finite simple graph and (d(v)) for its degree. A graph is \(C_4\)-free if and only if any two distinct vertices have at most one common neighbor.

**Lemma 1 (two-step counting).** If \(G\) is \(C_4\)-free and every degree is at least \(d\), then

\[
 d(v)(d-1)\le N-1 \qquad(v\in V(G)).
\]

**Proof.** Count paths \(v,x,y\) with \(x\in N(v)\) and \(y\in N(x)\setminus\{v\}\). For different (x,x'), the endpoint sets are disjoint, since otherwise \(v,y\) have two common neighbors. Their union excludes \(v\). Each set has at least \(d-1\) elements. This proves the inequality. The certificate constructs the finite dependent type of these paths and an injection into \(V\setminus\{v\}\); see `twoStep_count` and `degree_count`. ∎

We also need the weaker count

\[
 d(a)+d(b)\le N+1\qquad(a\ne b),
\]

obtained by counting the union of their neighborhoods and using that the intersection has size at most one (`degree_pair_bound`).

**Lemma 2 (weak even-order friendship statement).** A **nonempty** \(C_4\)-free graph of even order with minimum degree at least three has two distinct vertices with no common neighbor.

**Proof.** Suppose every distinct pair has a common neighbor, necessarily unique. Nonadjacent vertices \(u,v\) have equal degree: map \(x\in N(u)\) to the unique common neighbor of \(x,v\). The inverse sends \(y\in N(v)\) to the unique common neighbor of \(y,u\). These maps are well-defined because \(u,v\) are nonadjacent, and uniqueness verifies the inverse identities.

There is no universal vertex \(z\). Otherwise the preceding degree-sum bound, with \(d(z)=N-1\), forces every other degree to be at most two. Such another vertex exists because \(d(z)\ge3\).

If vertices \(u,v\) had different degrees, they would be adjacent. Choose \(u'\ne u\) nonadjacent to \(u\), and \(v'\ne v\) nonadjacent to \(v\). Their degrees equal those of \(u,v\), respectively. Unequal degrees force every edge from \(\{u,u'\}\) to \(\{v,v'\}\), a \(C_4\). Thus the graph is regular, say of degree \(d\).

For a fixed \(v\), the sets \(N(x)\setminus\{v\}\), \(x\in N(v)\), partition \(V\setminus\{v\}\): uniqueness gives disjointness and existence gives coverage. Hence \(N-1=d(d-1)\), so \(N\) is odd, a contradiction. This is proved locally as `even_no_common`; no theorem from Mathlib's Archive is imported. The explicit nonemptiness hypothesis rules out the empty graph and holds in every application here. ∎

**Lemma 3 (dense matching).** A finite graph of even order \(m\) with minimum degree at least (m/2) has a perfect matching.

**Proof.** Begin with an arbitrary pairing of all vertices, possible because \(m\) is even, and maximize the number of vertices whose partner is adjacent to them. Let \(f\) denote the pairing involution. If a pair \(a,b=f(a)\) is not an edge, consider a neighbor \(x\) of \(a\), with partner \(y=f(x)\). If \(b,y\) were adjacent, replace the pairs \(a,b\) and \(x,y\) by \(a,x\) and \(b,y\). The four vertices are distinct. Both new pairs are edges, so all previously good vertices remain good and \(a,b\) become good, contradicting maximality.

It follows that \(f(N(a))\cap N(b)=\varnothing\). Their union excludes \(b\): \(b\notin N(b)\), and \(f(x)=b\) would imply \(x=a\notin N(a)\). Therefore \(d(a)+d(b)\le m-1\), contradicting the minimum-degree bound. All pairs must be edges. The Lean proof `dense_matching` realizes the replacement by conjugating \(f\) by the transposition of \(b,x\). ∎

**Lemma 4 (deletion and independent pairs).** A nonempty \(C_4\)-free graph of even order \(N\) and minimum degree \(\delta\ge4\) admits deletion of two vertices such that every survivor loses at most one neighbor and the survivors can be partitioned into independent pairs.

**Proof.** Lemma 2 gives distinct \(x,y\) with no common neighbor. Every survivor loses at most one neighbor on deleting them. By Lemma 1,

\[
 3d(v)\le N-1\quad\text{for every }v.
\]

Since some degree is at least four, \(N\ge13\), and evenness gives \(N\ge14\). Consequently

\[
 2d(v)\le N-4
\]

for every vertex: multiply the first inequality by two and use \(2N-2\le3N-12\). Set \(m=N-2\). In the ordinary complement of the induced survivor graph, every degree is at least

\[
 N-3-d(v)\ge (N-2)/2=m/2.
\]

Lemma 3 gives a perfect matching there. Each matched pair is independent in the original graph. In Lean, `pair_delete_matching` and `pair_delete_degree` prove the two assertions. `pairing_equiv` labels the pairs, using the smaller of the two vertices under a finite enumeration as representative; `independent_pair_equiv` proves the resulting classes independent. Finally `repair_pairs` embeds the literal smaller host `Fin c × Fin 2` into the original vertex set and proves the degree-loss bound there. ∎

## 3. Repair when the class size is at least three

**Lemma 5.** Let \(s\ge3\). Suppose a \(C_4\)-free graph is partitioned into \(c+1\) independent classes of size \(s\). There is a set \(S\) of \(s\) vertices such that no survivor is adjacent to every vertex of \(S\), and the survivors admit a partition into \(c\) independent classes of size \(s\).

**Proof.** Fix an original class \(A\). If no vertex is adjacent to all of \(A\), delete \(A\).

Otherwise let \(v\) be adjacent to every vertex of \(A\), and let \(B\) be its class. Each member of \(B\setminus\{v\}\) has at most one neighbor in \(A\), since two such neighbors would be common to that vertex and \(v\). As there are \(s-1\) such members, some \(a\in A\) misses all of \(B\setminus\{v\}\).

Delete \(S=(A\setminus\{a\})\cup\{v\}\), replace \(B\) by \(\(B\setminus\{v\}\)\cup\{a\}\), and keep the other classes. The replacement is independent and has size \(s\). If a survivor saw all of \(S\), it and \(v\) would have the \(s-1\ge2\) common neighbors in \(A\setminus\{a\}\), a contradiction. In particular, every survivor loses at most \(s-1\) neighbors. The deleted set is not required to be independent.

The formal construction `repair_large` is the identity permutation in the first case and the transposition of \(a,v\) in the second. The retained embedding is `\(j,t\) ↦ e (i.succAbove j,t)`. Theorems `restrict_host`, `restrict_noC4` and `restrict_degree` establish the new host condition, \(C_4\)-freeness and degree loss on the literal finite vertex types. ∎

## 4. Finiteness and the growth theorem

First we prove that the minimum in the definition is finite for every \(s,n\ge1\). Take \(c=2n+6\). If a graph on \(K_{c\times s}\) has no complement star with \(n\) leaves, its degree at each vertex is at least

\[
 D=(c-1)s-n+1.
\]

The host has degree ((c-1)s), and every relative-complement degree is at most \(n-1\). For two distinct vertices the preceding lower bound gives a degree sum at least \(2D\). But a \(C_4\)-free graph has degree sum at most \(cs+1\) at such a pair. Here

\[
 2D-(cs+1)=(2n+4)s-2n+1\ge5,
\]

a contradiction. There are at least two vertices since \(c\ge8\) and \(s\ge1\). Thus `RamseyProp s n (2*n+6)` holds (`ramseyProp_bound`). A single-class host has no edges in either color, so \(M_s(n)\ge2\). For \(s\ge2,n=1\), two classes suffice: avoiding a complement edge forces all host edges, which include a \(C_4\). This also proves the stated sanity check \(M_s(1)=2\).

We now prove the stronger assertion

\[
 P(s,n,c)\ \Longrightarrow\ P(s,n+1,c+1)\qquad(s,n\ge2),
\]

where \(P\) is the source Ramsey property at \(c\) classes. Such a property forces \(c\ge2\). Suppose that \(G\subseteq K_{(c+1)\times s}\) is \(C_4\)-free and that its relative complement has no \(K_{1,n+1}\). Then

\[
 d_G(v)\ge cs-n\qquad\text{for every }v.
\]

It suffices to construct a \(C_4\)-free graph \(H\) on \(cs\) vertices, partitioned into \(c\) independent classes of size \(s\), with

\[
 \delta(H)\ge(c-1)s-n+1. \tag{1}
\]

Its relative-complement degrees are at most \(n-1\), contrary to (P(s,n,c)).

For \(s\ge3\), Lemma 5 gives \(H\) with degree at least (cs-n-(s-1)), exactly \(1\).

For \(s=2\), put \(D=2c-n\). If \(D\ge4\), Lemma 4 produces an independent-pair partition after deletion, losing at most one neighbor per survivor. This gives \(\delta\(H\)\ge D-1\), which is \(1\).

If \(D\le3\), we can contradict (P(2,n,c)) directly. For \(c=2\), put a perfect matching between the two classes: both this matching and its relative complement have degree one, so neither a \(C_4\) nor a complement star with \(n\ge2\) leaves exists. For every \(c\ge3\), use the cycle of length \(2c\ge6\) and pair antipodal vertices into the \(c\) host classes. These pairs are independent. The cycle has degree two and contains no \(C_4\), while its relative complement has degree \(2c-4\le n-1\), because \(D\le3\). This is again a counterexample to (P(2,n,c)).

For clarity, the formal low-degree construction is a cycle on `ZMod (2*c)` with edges of difference \(1\) or \(-1\), paired by the involution \(v\mapsto v+c\). Its degree is proved to be two, its \(C_4\)-freeness is proved algebraically (a putative four-cycle forces two displayed vertices equal or \(4=0\)), and `independent_pair_equiv` transports the graph back to `Fin c × Fin 2`. The four-vertex matching is also proved explicitly. No finite graph database or generated certificate is used. This cycle argument consolidates the empty/matching/cycle low-degree split in the supplied ordinary proof.

We have proved `step`. Apply it with \(c=M_s(n)\), using the proved existence and attainment of that minimum. The least permissible number of classes for \(n+1\) is at most \(c+1\). Hence

\[
 \boxed{M_s(n+1)\le M_s(n)+1\quad(s,n\ge2).}
\]

The final declaration is exactly

```lean
theorem conj_2_3 (s n : ℕ) (hs : 2 ≤ s) (hn : 2 ≤ n) :
    M s (n+1) ≤ M s n + 1
```

## 5. Scope, significance and prior-art limits

The contribution proposed here is the permission to **repartition surviving vertices**, combining a local transposition for \(s\ge3\) with a separate global pair repair for \(s=2\). No novelty is claimed for the friendship consequence, dense matching fact, or neighborhood count in isolation. The argument is elementary and short; a specialist may judge its significance modest. It nevertheless removes the numerical condition in the source's Proposition 2.2 throughout the printed range, rather than producing a parameter instance or merely correcting the record's wording. Campaign acceptance and priority are not self-awarded by this formalization lane.

The final bounded prior-art refresh (20 November 2026) read arXiv v1, whose current abstract page lists only v1 and no journal reference; the related Zenodo poster; and Xiong's 2024 polarity-construction paper (DOI 10.12677/AAM.2024.132082). The source's Proposition 2.2 remains the closest result: it proves the increment-one bound under an extra numerical hypothesis. Neither the poster nor the 2024 paper proves the universal growth inequality. The local Principia, mio-qwq/math, omega and openai/math screens found no matching result, and fresh omega issue and PR searches for the source identifier and distinctive object words were empty. These are bounded searches, not a proof of priority.

Three earlier full texts remain unresolved priority risks. ScienceDirect's robots.txt expressly disallows ChatGPT-User, so the 2021 Procedia paper was not fetched there; a ResearchGate copy attempt returned HTTP 403. Its indexed abstract describes a coordinate parametrization of projective planes and polarity constructions improving lower bounds, without announcing the growth inequality. The 2020 Brazilian Journal of Development landing page returned HTTP 403 with a Cloudflare challenge, despite robots.txt allowing user-initiated reference access. Its actual abstract was not recovered: OpenAlex merges it with a Zenodo poster abstract, which must not be attributed to the journal paper. Gonçalves's 2019 doctoral thesis was not located in the accessible UEM institutional repository or linked graduate-program pages; neither its abstract nor its full text was read. Absence of a growth theorem from the available abstracts does not exclude a proof in these unread bodies.

## 6. Certificate and reproducibility

The certificate consists of 11 modules (1,405 lines) in `src/`, reproduced byte-for-byte in `LEAN-SOURCE-APPENDIX.md` in dependency order. Lean 4.34.1 and the Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned in `PINS.json`. Every module is compiled and checked by the standalone kernel checker through the mandated 32 GiB runner; receipts and the clean extracted rebuild are listed in `REPORT.md`.

The final endpoint's axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. The certificate has no unfinished proofs, added axioms, broad `import Mathlib`, native decision procedure, or externally generated graph data. The existence proof, weak friendship result, matching argument, and both kinds of partition transport are part of the kernel-checked dependency chain. The extracted rebuild does not replace root's independent kernel replay. The separate final mathematical and source review is recorded in `FINAL-REVIEW-337410.md` in the final-check lane.
