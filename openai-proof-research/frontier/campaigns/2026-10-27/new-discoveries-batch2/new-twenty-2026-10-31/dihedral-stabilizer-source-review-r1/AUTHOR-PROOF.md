# Exact ordinary refutation of MathDB 368999 — qualification HOLD

Credit 0. This is an ordinary hand proof, not an accepted discovery or a Lean certificate. No mathematical computation was executed. All computations below are symbolic deductions made in the research reasoning.

The literal record is preserved in literal/368999.jsonl and provenance.json. The source is Allocca–Trimmer, arXiv:2506.19216, Conjecture 2. Its v1 is dated 24 June 2025 and latest listed v2 is dated 20 September 2025. Both bodies were fetched. Section 2 defines W_l as elements representable by words of exactly l letters from S, F(r^i f^k)=i, and W'_l=F(W_l). Section 3 defines the additive translation stabilizer. The singleton {1} in the conjecture is group-identity notation: the additive identity is 0. The witness below has a nonidentity stabilizer and is proper regardless of that notation issue.

Use D_8 = <r,f | r^8=f^2=1, frf=r^-1>, with r of exact order 8. Take S={f,rf,r^4 f}. These are three distinct nonidentity reflections. Each squares to 1, so S is symmetric. Since (rf)f=r, S generates r and f, hence all of D_8. In particular, no condition that it is a genuine generating set is omitted.

Put A={0,1,4} in Z/8Z. For x,y in A,
(r^x f)(r^y f)=r^(x-y).
Every two-letter word is of this form, and every ordered pair x,y gives a two-letter word. Therefore W'_2=A-A, not merely a subset of A-A. The difference table is

| x minus y | 0 | 1 | 4 |
|---|---|---|---|
| 0 | 0 | 7 | 4 |
| 1 | 1 | 0 | 5 |
| 4 | 4 | 3 | 0 |

Consequently B=W'_2={0,1,3,4,5,7}. Translation by 4 exchanges the three pairs {0,4}, {1,5}, {3,7}, so B+4=B. Translation by 1 is not a symmetry, because 1 belongs to B but 1+1=2 does not. Thus the stabilizer contains the nonzero element 4 and is not all of C_8. More precisely, its complement is {2,6}. If B+c=B, then {2,6}+c={2,6}. The image of 2 forces c=0 or 4. Both do stabilize B, so Stab(B)={0,4}. This contradicts the exact either-trivial-or-full conclusion at l=2.

This does not challenge or use Theorem 4's word-set growth lower bound: here |W_2|=6 is compatible with min(2*2+1,8)=5. It does not use a prime-order-only statement: Conjecture 2 occurs in the section for all n. The source explicitly normalizes an arbitrary three-reflection generating set to {f,r^a f,r^b f}, and ours satisfies that normalization.

The mechanism is structural rather than a one-off unexplained table. For n=2m and m>=4, take A={0,1,m}. Then
A-A={0,m}+{0,1,-1}.
Indeed the differences are 0, +/-1, m, m-1, m+1. The three cosets of H={0,m} are distinct for m>=4, so this has six elements and is a proper nonempty subset of C_(2m). It is H-invariant. If its stabilizer were the full cyclic group, invariance and nonemptiness would force it to be the entire cyclic group, contradicting its size. The generators again include f and rf. This gives an ordinary family of counterexamples; it is one family with one possible credit, never multiple credits.

Qualification and chronology limits: latest arXiv v2 still has the conjecture. No journal reference for that paper is displayed on the fetched abstract page; this is not proof that no journal version exists. The 2015/2017 predecessor has actual three-reflection classification and word-length discussion; its Theorem 4 and proof/examples were read. A complete comparison with its final 2017 journal body is unfinished. Moulton–Steel's earlier butterfly-effect paper was downloaded and partially inspected, not fully source-cleared. Aseeri's November 2025 citing paper uses conjugates of generators and at-most-length balls; its definitions and proof portions were read. Its normal-conjugacy diameter theorem does not by itself compute this exact S-word set, but the thesis behind that article has not been read. Public registry routing screens are not a proof of absence. No independent adversarial review or final significance adjudication has occurred. Therefore this file remains qualification HOLD. No CANDIDATE.md, dormant Pi implementation plan, execution or acceptance is claimed.
