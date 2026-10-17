# Family 131: connected conditioning barriers (pre-freeze screen)

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0. This is a diagnostic screen, not a substantiality nomination, acceptance, or frozen theorem target. The source theorem at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true. The proposed extension was unrestricted connected fixed-degree sampling/mixing; no full proof of that extension has been obtained. The elementary barriers below do not disprove such an extension.

## Actual source interface

The pinned manuscript *Polynomial Mixing of the Switch Chain for Every Graphical Degree Sequence* concerns all simple labeled realizations Omega_d, not just connected ones. Its lazy four-vertex switch chain has t_mix(1/4) <= 2 n^8 and gap >= 1/(24 n^2 binom(n,4)). Its exact sampler terminates almost surely in expected polynomial bit complexity; this is not a worst-case running-time assertion.

Fix a vertex pair {i,j}, the outside graph, ij, and each outside vertex's number (0, 1, or 2) of neighbors in the pair. The singleton-neighbor labels form a set N; exactly q are assigned to i. On the unrestricted fiber every q-subset is permitted, with uniform conditional measure. The manuscript uses conditional averaging E_a, h_a=I-E_a and H=sum_a h_a. Its global identity H^2=sum_T H_T^2-(n-3)H+D_disjoint, triple bound H_T^2>=H_T and disjoint bound D_disjoint>=0 yield H^2>=H. Conditioning on connectedness changes the fibers and their measures. The source does not supply the resulting global inequality.

## Exact connected pair-fiber description

Assume a fiber has at least one connected realization and n>2. Every component of the fixed outside graph has at least one fixed attachment to {i,j}; otherwise no realization could be connected. If ij is present, or an outside vertex has two neighbors in the pair, then i and j are already connected in every realization. Every component attaches to this connected core, so every q-subset is allowed.

Otherwise all attachments are singleton labels. Let W_1,...,W_t partition N according to their outside components; every block is nonempty. A q-subset S gives a connected graph if and only if some W_l is mixed: 0<|S intersect W_l|<|W_l|. Indeed a mixed component joins i to j, and every other component attaches to one or both. If no block is mixed, the i-side and j-side are separated. Thus precisely the unions of whole blocks are deleted from the uniform slice.

This family need not be matroid bases. Take N={a,b,c,d,e,f}, blocks {a,b},{c,d},{e},{f} and q=3. Both B_1={a,c,d} and B_2={c,e,f} are permitted. For x=a in B_1 minus B_2, either possible replacement y in B_2 minus B_1 (e or f) gives a union of whole blocks, hence a forbidden set. The basis exchange axiom fails. This is an actual graph fiber: outside edges ab and cd, isolated e,f, and exactly one attachment per outside vertex to i or j, with both i,j of degree 3. Its degree vector is (3,3,2,2,2,2,1,1). Four of its twenty q-subsets are forbidden. No numerical evidence is needed for this example.

There is a useful limit on this obstruction. If the fiber has a connected realization in the second case, some block contains two labels x,y, and 1<=q<=|N|-1. A uniform q-subset separates those two labels with probability

  2q(|N|-q)/(|N|(|N|-1)) >= 2/|N|.

Such separation guarantees connectivity. Thus this observation is not a claim of exponentially poor acceptance inside an individual pair fiber, nor a proof of slow local mixing. It prevents an automatic invocation of the uniform-slice or matroid-base interface; the global conditioned operator estimate still needs proof.

## Exponentially rare connected realizations: an elementary count

For integer m>=16 take m labeled vertices of degree 3 and m+2 of degree 1. Write n=2m+2, M=4m+2 for the number of labeled half-edges and E=2m+1=n-1. Every connected realization is a tree. The Prüfer encoding, with each degree-3 label occurring twice and each leaf zero times, gives the positive exact count

  T_m=(2m)!/2^m.

There are Q_m=(4m+1)!! perfect pairings of the M half-edges. Every simple graph with these degrees corresponds to exactly 6^m pairings. We give a crude polynomial lower bound on the proportion of simple pairings, without invoking an asymptotic enumeration theorem.

For a pairing P let B(P) be the number of loops plus the number of unordered pairs of distinct parallel edges. Uniform pairing gives

  E[number of loops] = 3m/(4m+1) < 3/4,
  E[number of parallel pairs] = 9m(m-1)/((4m+1)(4m-1)) < 9/16.

The first identity sums over pairs of half-edges at one vertex. For the second, choose two half-edges at each of two degree-3 vertices and one of the two cross matchings. Consequently E B<2. Markov's inequality implies that more than half of all pairings have B<=4.

Any such pairing can be repaired to a simple pairing in at most four two-edge switches. All multigraph degrees remain at most 3, with loops counted twice. At a loop at v let F={v} union N(v), so |F|<=4. At a parallel edge vu let F={v,u} union N(v) union N(u), so |F|<=8. At most 3|F|<=24 edges meet F. At most 2B<=8 edges are bad (loops or members of nontrivial parallel bundles): a bundle of multiplicity r>=2 contributes r<=2 binom(r,2) edges to this bound. Since E>=33, there is an ordinary nonparallel edge xy with both endpoints outside F.

For a loop vv replace vv,xy by vx,vy. For a parallel edge vu replace one copy of vu and xy by vx,uy. These replacements are operations on the four actual labeled half-edges. The chosen endpoints ensure that no new loop or parallel edge is created. At least one defect disappears, so B decreases by at least one. Repeat, with a fixed deterministic rule for all choices, to obtain a simple pairing in at most four steps.

At any pairing a reverse step is specified by two current edges and a repairing of their four half-edges, with at most 3M^2 choices. Hence the number of preimages of a final simple pairing under this repair map is at most

  sum_{j=0}^4 (3M^2)^j <= 5(3M^2)^4.

This counts reverse paths and therefore bounds distinct preimages whether or not some reverse paths are inadmissible. Since at least Q_m/2 initial pairings had B<=4, the number of simple pairings is at least Q_m/[10(3M^2)^4]. It follows that

  |Omega_d| >= Q_m/[10(3M^2)^4 6^m].

The connected fraction p_m thus satisfies

  p_m <= 10(3M^2)^4 (2m)! 3^m/Q_m
      = 10(3M^2)^4 3^m 2^(2m+1)/[(2m+1) binom(4m+2,2m+1)]
      <= 15(3M^2)^4 (3/4)^m.

The final inequality uses the central binomial coefficient's bound by the average of its row, binom(4m+2,2m+1)>=2^(4m+2)/(4m+3), and (4m+3)/(2(2m+1))<=3/2. Constants are intentionally loose; the conclusion is exponential rarity as m tends to infinity.

Therefore independent exact-uniform unrestricted samples followed by rejection until connected require expected at least (4/3)^m/[15(3M^2)^4] samples. Moreover, ANY map from all realizations onto or into connected realizations has a fiber of size at least |Omega_d|/T_m, by the pigeonhole principle. A uniform polynomial maximum-fiber retraction from all states to connected states is impossible for these degree vectors. This second conclusion is independent of how such a map might repair components.

Neither conclusion rules out direct connected-state chains, non-rejection exact samplers, weighted comparisons without this fiber bound, or tree-specific Prüfer sampling. Neither challenges the stipulated upstream theorem.

## Actual primary operation comparison

Feder, Guetz, Mihail and Saberi, *A Local Switch Markov Chain on Given Degree Graphs with Application in Connectivity of Peer-to-Peer Networks*, local private PDF from https://theory.stanford.edu/~tomas/switch.pdf, Section 3.1/Lemma 1, states a retraction for min_i d_i>=2 with fiber bound 2n and distance bound 17 for adjacent unrestricted states. The inspected proof chooses a cycle edge in each component, removes these edges and chains the components cyclically. It then uses edge rotations and component reorderings (case bounds 9,17,14,12), with recovery from cuts along the joined cycle. This is a concrete paid operation in the minimum-degree regime. A tree component lacks the selected cycle edge. Our counting argument proves that simply extending the polynomial-fiber contract to arbitrary degree vectors with leaves cannot succeed. We have not audited every assertion of the older paper or used its claimed bounds as a lemma in our argument.

Cooper, Dyer, Greenhill and Handley, *The flip Markov chain for connected regular graphs*, arXiv:1701.03856v2 (13 June 2018), Theorem 1.1 covers even degree Delta>=4, n>=8 and n>=Delta+1, with the stated polynomial bound 480 Delta^35 n^15(Delta n log(Delta n)+log(epsilon^-1)). Its introduction explicitly describes a two-stage direct canonical-path comparison via connected switches. This establishes relevant prior work in a restricted degree regime, not the contemplated unrestricted connected extension. Only its abstract and introduction through the theorem and outline were read; its full Section 4 proof was not read. The introduction's correction of reference [6] concerns the authors' PODC 2009 extended abstract, not a demonstrated correction of the Feder et al. paper; no contrary attribution is made here.

## Disposition and unpaid operation

No target was frozen. No full connected mixing theorem is claimed. The finite fiber characterization, exchange failure and rarity count are elementary diagnostic deductions, not presented as new-to-literature substantial results. The remaining credible mathematical task would be a genuinely new global conditioned estimate or comparison which handles tree components without a polynomial all-state fiber bound. Neither the source's unrestricted inequalities nor the inspected primary cycle-joining construction pays that task. There is no narrower replacement nomination. Per parent instruction, new screening pauses after this packet is sealed, for a separately assigned independent full proof review.
