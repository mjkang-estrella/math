# Remarks on two conjectures of Li and Guo

Kerem Özdemir, 2026-10-26.

Claude (Anthropic) was used, under the direction of Kerem Özdemir, to search for the examples, to develop the arguments, to write the verification script and to draft this note. The characteristic polynomials were checked by that exact script and separately in floating point. The author takes full responsibility for the content.

**Summary.** Li and Guo [1] proposed an inequality between the Laplacian eigenvalues and the degree sequence of a graph (their Conjecture 1.1) and a weaker form for the sums of the largest Laplacian eigenvalues (Conjecture 1.2). We record two small defects in the printed statements. Conjecture 1.2, inequality (3) of their Remark 1 and their Corollary 2.19 fail for the 5-cycle, because the exception made in Conjecture 1.1 was not carried over. Conjecture 1.1 as printed covers disconnected graphs and fails for C5 + K1, C5 + K2 and 2C5; the reduction to connected graphs in their Lemma 2.1 applies the conjecture to every component, including excluded C_{4k+1} components. We give corrected statements. The connected case of Conjecture 1.1 remains open.

## 1. The statements

For a graph G on n vertices let mu_1 >= mu_2 >= ... >= mu_n = 0 be the eigenvalues of the Laplacian L(G) = D(G) - A(G), let S_k(G) = mu_1 + ... + mu_k, and let d_1 >= ... >= d_n be the degrees. Write

    R(G) = (1 - 1/d_1) * sum_{i=1..n} d_i (d_i - 1).

The following are transcribed from [1] (p. 4552 for the two conjectures, p. 4562 for the corollary).

- **Conjecture 1.1.** If G is not a cycle C_{4k+1} (k a positive integer), then sum over the i with mu_i >= 2 of (mu_i - 2)^2 <= R(G).
- **Conjecture 1.2** (introduced as the weaker conjecture obtained by the Cauchy-Schwarz inequality). For k = 1, 2, ..., n: S_k(G) <= 2k + sqrt(k R(G)).
- **Remark 1, inequality (3)** (conjectured): S_2(G) <= 4 + sqrt(2 R(G)).
- **Corollary 2.19.** If G is d-regular, then S_2(G) <= 4 + (d - 1) sqrt(2n).
- **Lemma 2.1.** If Conjecture 1.1 is true for connected graphs, then it is also true for disconnected graphs.

The sum in Conjecture 1.1 runs over indices, so repeated eigenvalues count with multiplicity; this is how [1] computes it for cycles (Theorem 2.14 and Remark 2), and it is the reading under which the cycles C_{4k+1} need to be excluded. The authors report a computer check of Conjecture 1.1 for connected graphs with at most 9 vertices, and they show (Remark 2) that every C_{4k+1} violates its inequality.

## 2. Conjecture 1.2, inequality (3) and Corollary 2.19 at C5

The Laplacian characteristic polynomial of C5 is x (x^2 - 5x + 5)^2, so its spectrum is ((5 + sqrt5)/2)^(2), ((5 - sqrt5)/2)^(2), 0. Here d_1 = 2, sum d_i (d_i - 1) = 10 and R(C5) = 5. At k = 2,

    S_2(C5) = 5 + sqrt5 = 7.2360...,   2k + sqrt(k R) = 4 + sqrt10 = 7.1622...

and S_2 > 4 + sqrt10 is equivalent to (1 + sqrt5)^2 > 10, that is, to sqrt5 > 2. So C5 violates Conjecture 1.2 at k = 2. The right side of inequality (3) is the same 4 + sqrt10, and since C5 is 2-regular with n = 5 the right side of Corollary 2.19 is 4 + (2 - 1) sqrt10 as well, so both fail at C5 too.

The cause is an omitted exception. Conjecture 1.2 follows from Conjecture 1.1: for each k,

    S_k - 2k <= sum over i <= k with mu_i >= 2 of (mu_i - 2) <= sqrt(k * sum over mu_i >= 2 of (mu_i - 2)^2),

so a graph can violate Conjecture 1.2 only if it violates the inequality of Conjecture 1.1, and C5 is one of the excluded cycles. Among cycles, a scan of C_n for 3 <= n <= 600 finds that Conjecture 1.2 fails only for (n, k) = (5, 2) and Corollary 2.19 only for n = 5, while the inequality of Conjecture 1.1 fails exactly for n = 1 (mod 4), in agreement with [1]. Among connected graphs with at most 10 vertices, C5 is the only one violating Conjecture 1.2 (Section 4).

**Repair.** Exclude C5, or the cycles C_{4k+1}, in Conjecture 1.2, in inequality (3) and in Corollary 2.19.

## 3. Conjecture 1.1 for disconnected graphs

Conjecture 1.1 is stated for every graph other than C_{4k+1}, connected or not, and Lemma 2.1 is there to reduce the disconnected case to the connected one. The proof of Lemma 2.1 applies the inequality to each component, which fails when a component is C_{4k+1}. Exact values (the Laplacian spectrum of a disjoint union is the union of the spectra):

| G | d_1 | R(G) | sum over mu_i >= 2 of (mu_i - 2)^2 | violated |
|---|---|---|---|---|
| C5 + K1 | 2 | 5 | 3 + sqrt5 = 5.236 | yes |
| C5 + K2 | 2 | 5 | 3 + sqrt5 = 5.236 | yes |
| 2 C5 | 2 | 10 | 6 + 2 sqrt5 = 10.472 | yes |
| C5 + K4 | 3 | 68/3 | 15 + sqrt5 = 17.236 | no |

Each "yes" reduces to sqrt5 > 2. K2 adds the eigenvalue 2, which contributes 0 to the left side, and degrees 1, which contribute 0 to the right side. 2C5 also violates Conjecture 1.2 at k = 4: (S_4 - 8)^2 = (2 + 2 sqrt5)^2 = 24 + 8 sqrt5 > 40 = 4 R, again equivalent to sqrt5 > 2. The last row shows that a C5 component is harmless when another component raises d_1. A second, minor gap in the proof of Lemma 2.1 is that it uses 1 - 1/d_1(H) for components H that are single vertices, where d_1(H) = 0.

**Corrected Lemma 2.1.** If the inequality of Conjecture 1.1 holds for every connected graph with at least one edge other than C_{4k+1}, then it holds for every graph with at least one edge that has no component isomorphic to some C_{4k+1}.

*Proof.* Let H_1, ..., H_t be the components of G. Isolated vertices contribute only the eigenvalue 0 and the term d(d - 1) = 0, so they can be dropped. For each remaining component, the hypothesis gives

    sum over mu_i(H_j) >= 2 of (mu_i(H_j) - 2)^2 <= (1 - 1/d_1(H_j)) sum_{v in H_j} d(v)(d(v) - 1) <= (1 - 1/d_1(G)) sum_{v in H_j} d(v)(d(v) - 1),

because d_1(H_j) <= d_1(G) and the sum is nonnegative. Adding over j gives the inequality for G, since the spectrum and the degree sequence of G are the unions over the components. QED

**Repair.** State Conjecture 1.1 for connected graphs other than C_{4k+1} (the case the authors tested), or for graphs with no component isomorphic to a C_{4k+1}; by the corrected lemma the two versions are equivalent.

## 4. Status of the connected case

These remarks leave the connected case of Conjecture 1.1 untouched. It is also listed as open task cb-0101 in the bespokelabsai/conjecture-bench collection (status as of 2026-07-23). We checked all 11,716,571 connected graphs on 10 vertices (and all connected graphs on fewer vertices) in floating point: apart from the excluded cycles, none violates Conjecture 1.1, and only C5 violates Conjecture 1.2. Random-start tabu search on connected graphs with 11-18 vertices and family-seeded tabu search on 11 vertices found no violation of the connected case.

## 5. Reproduction

`python3 verify.py` in this folder (Python standard library only, about one second; output in `verify.out`). For C5, C5 + K1, C5 + K2, 2C5 and C5 + K4 it computes the Laplacian characteristic polynomial exactly (integer Berkowitz recursion), checks it against the factorisation into x, x - 2, x - 4 and x^2 - 5x + 5, and decides every inequality above in exact arithmetic in Q(sqrt5). It then repeats the floating-point scan over cycles C_n, 3 <= n <= 600. The exhaustive check of connected graphs on at most 10 vertices was run separately with `src/batch4.py` in the repository that contains this note; `verify.py` does not repeat it.

## Reference

[1] W.-J. Li and J.-M. Guo, A new conjecture on Laplacian eigenvalues and degree sequence of a graph, Filomat 39:13 (2025) 4551-4564. doi:10.2298/FIL2513551L
