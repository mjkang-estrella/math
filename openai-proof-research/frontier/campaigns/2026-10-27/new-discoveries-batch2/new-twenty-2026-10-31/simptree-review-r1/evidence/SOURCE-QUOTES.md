# v1 — 2508.17854v1.txt

```text
1:                                                Characterisations and Structural Properties of Pure n-Simplicial
2:                                                                             Trees
3:                                                                    Gaurav Kottari∗, Niteesh Sahni†, Qazi J. Azhad‡
4:                                                            Department of Mathematics, Shiv Nadar Institution of Eminence,
5:                                                                    Tehsil Dadri, Gautam Buddha Nagar, 201314,
6: 
7: 
8: 
9: 
10: arXiv:2508.17854v1 [math.CO] 25 Aug 2025
11:                                                                                Uttar Pradesh, India
```

```text
118: 2.1   Simplicial Complexes
119: A simplicial complex K is a collection of non-empty subsets of a finite vertex set V , satisfying
120: the condition that every singleton subset is included in K, and that every non-empty subset of
121: an element of K is also an element of K. The elements of a simplicial complex are referred to as
122: simplices, and the dimension of a simplex is defined as one less than the number of its vertices;
123: in particular, a k-simplex is a simplex of dimension k and hence consists of exactly k + 1 vertices.
124: Accordingly, the dimension of a simplicial complex is the maximum dimension among its simplices.
125: We denote by K k the set of all k-dimensional simplices in a complex K, and by αk (K) the number
126: of such simplices. Given two simplices σ and τ in a simplicial complex K, τ is a face of σ if every
127: vertex of τ is also a vertex of σ. A simplicial complex K is called a pure n-simplicial complex
128: if every simplex in K is a face of at least one n-simplex of K. In particular, a pure 1-simplicial
129: complex K with vertex set V can be viewed as a simple, undirected graph G(W, E) with no isolated
130: vertices, where W = V and E = K 1 . A subset L ⊆ K of simplices is termed a subcomplex of K if
131: it satisfies the following condition: for every simplex σ in L, if τ is a face of σ in K, then τ must
132: also be an element of L. These definitions are standard and can be found in foundational texts on
133: combinatorial algebraic topology [3, 7].
134: 
135: 2.2   Dewdney’s Framework
136: Definition 2.1. Let S be a subset of a simplicial complex K. The closure of S in K is the smallest
137: subcomplex S of K such that S ⊆ S, that is,
138:                           S = {τ ∈ K : τ is a face of σ for some σ ∈ S}.
139: Definition 2.2. The attachment of an n-simplex ηi in a pure n-simplicial complex K is the sub-
140: complex denoted by A(ηi , K) and is defined as
141:               A(ηi , K) := {σ ⊂ ηi : σ ⊂ ηj for some n-simplex ηj , such that ηj ̸= ηi }.
142: Definition 2.3. A simplicial complex K with p + 1 vertices is called m-complete if the dimension
143: of K is m, and every subset of the vertex set of K with m + 1 elements is a simplex in K. In
144: particular, if m = p, then K is called a complete simplicial complex.
145: Definition 2.4. A pure n-simplicial complex K is said to have an m-ordering for some 0 ≤ m ≤
146: n − 1 if there exists a distinct sequence of n-simplices η1 , . . . , ηt , where t = αn (K), such that
147: A(ηi , Ki ) is an m-dimensional simplicial complex for each 2 ≤ i ≤ t, where Ki = {η1 , . . . , ηi }.
148: Furthermore, K is said to have an m-complete ordering if A(ηi , Ki ) forms a complete simplicial
149: complex with m + 1 vertices for each 2 ≤ i ≤ t.
150:    Note: Here we have adopted simplified notions and notations for the concepts originally defined
151: by Dewdney [1]. For example, an m-complete ordering corresponds to a Km+1  m -ordering, and an
152:                                 m
153: m-ordering corresponds to the S≥1 -ordering in Dewdney’s work. This avoids notational complexity
154: while preserving the original meaning.
155: 
156:                                                   3
157: Definition 2.5. A pure n-simplicial complex K is called an (m, n)-tree if K has an m-complete
158: ordering.
159:    To further characterise (m, n)-trees, Dewdney [1] introduced the notions of (m, n)-walks, (m, n)-
160: paths, (m, n)-connectedness and (m, n)-circuits, which we now recall.
161: Definition 2.6. In a pure n-dimensional simplicial complex K, an (m, n)-walk sequence between
162: two m-simplices σi and σj , for some 0 ≤ m ≤ n − 1, is an alternating sequence of m-simplices and
163: n-simplices, given by
164:                                 σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj ,
165: such that for each 1 ≤ k ≤ r, the simplices σk and σk+1 are distinct and both are faces of ηk . The
166: integer r is called the length of the (m, n)-walk sequence.
167: Definition 2.7. An (m, n)-walk sequence σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj between two m-
168: simplices σi and σj in a pure n-dimensional simplicial complex K is called an (m, n)-path sequence
169: if all simplices in the sequence are distinct.
170: Definition 2.8. A pure n-simplicial complex K is (m, n)-connected if there exists an (m, n)-path
171: sequence between every pair of m-simplices in K.
172: Definition 2.9. An (m, n)-walk sequence σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj in a pure n-simplicial
173: complex K is called an (m, n)-circuit sequence if it satisfies the following conditions:
174:     1. σi = σj .
175: 
176:     2. For all 1 ≤ p ̸= q ≤ r, we have σp ̸= σq and ηp ̸= ηq .
177: 
178: 
179: 3     Connectivity
180: Building upon the notion of an (m, n)-path sequence introduced by Dewdney [1], we now define a
181: more restrictive structure called a reduced (m, n)-path sequence.
```

```text
241: m-simplices τp+1 , . . . , τx such that τk is a face of σk for all p + 1 ≤ k ≤ x, we obtain a reduced
242: (m, n)-path sequence:
243:                                           τi , ηp , τp+1 , . . . , τx , ηx , τj ,
244: between τi and τj in K.
245: 
246:    From Proposition 3.3, we observe that if a pure n-dimensional simplicial complex K is (n−1, n)-
247: connected, then it is (m, n)-connected for all 1 ≤ m ≤ n−1. Henceforth, we refer to such a complex
```

```text
360: pure n-simplicial complexes.
361: 
362: Definition 4.1. An (m, n)-circuit sequence σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σi in a pure n-
363: simplicial complex K is called an (m, n)-simplicial cycle sequence if the following conditions hold:
364: 
365:     1. r ≥ 3.
366: 
367:     2. For each 2 ≤ k ≤ r − 1, σi is not a face of ηk .
368: 
369:     3. For each 2 ≤ z ≤ r, σz is a face of an (n − 1)-simplex σz′ of K, such that σz′ is a face of ηz−1
370:        and ηz , and σx′ ̸= σy′ for all 2 ≤ x ̸= y ≤ r.
371: 
372: The subcomplex C = {η1 , ..., ηr } of K is called simplicial cycle.
373: 
374:     In Fig. 1, the (1, 2)-circuit sequence
```

```text
449: 
450: Proof. Let
451:                                   σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σi
452: be an (n − 1, n)-simplicial cycle sequence. Since σi is not a face of η2 , there exists a vertex vi of σi
453: such that vi is not a vertex of η2 .
454:     Let 0 ≤ m ≤ n − 2. Let τi be an m-face of σi such that vi is a vertex of τi . Thus, τi is not a
455: face of η2 . Therefore, by Theorem 4.2, K contains a (m, n)-simplicial cycle sequence.
456: 
457: 
458:    From Corollary 4.8, we have the following remark.
459: 
460: Remark 4.9. If a pure n-simplicial complex with n ≥ 2 does not contain any (m, n)-simplicial
461: cycle sequence for some 0 ≤ m ≤ n − 2, then it does not contain an (n − 1, n)-simplicial cycle
462: sequence.
463: 
464: Lemma 4.10. In an acyclic pure n-simplicial complex, if there exist dependent reduced path se-
465: quences between two m-simplices, then:
```

```text
515: structural properties are studied.
516: 
517: Definition 5.1. A pure n-simplicial complex K is a simplicial tree if it is connected and acyclic.
518: 
519:    In Fig. 2(a), the simplicial complex is a simplicial tree composed of four 2-simplices, nine 1-
520: simplices, and six 0-simplices, whereas in Fig. 2(b), the simplicial complex is a simplicial tree with
521: three 2-simplices, seven 1-simplices, and five 0-simplices.
522: 
523: 
524: 
525: 
526:                      (a)                                                             (b)
527: 
528:                                Figure 2: Examples of simplicial trees
529: 
530: 
531: Theorem 5.2. A connected pure n-simplicial complex is a simplicial tree if and only if it satisfies
532: the following conditions:
```

```text
685:    2. For any 0 ≤ m ≤ n − 2, there does not exist any (m, n)-simplicial cycle sequence.
686: Then K is a simplicial tree.
687:     In Fig. 3, the simplicial complex
688: 
689:             K = {{1, 2, 3}, {2, 3, 4}, {3, 4, 5}, {1, 4, 5}, {1, 2, 6}, {1, 3, 7}, {1, 4, 9}, {1, 5, 8}}
690: 
691: is connected and satisfies conditions (1) and (2) of Theorem 5.2. Here, the (0, 2)-walk sequence
692: {1}, {1, 2, 3}, {2}, {2, 3, 4}, {3}, {3, 4, 5}, {5}, {1, 4, 5}, {1} forms a (0, 2)-simplicial cycle in K. Hence,
693: K is not a simplicial tree.
694:     Therefore, if condition (3) of Theorem 5.2 is dropped, then the converse of Theorem 5.2 fails.
695: 
696: 
697: 
698: 
699:                              Figure 3: Connected pure n-simplicial complex
700: 
701: 
702: Theorem 5.4. A pure n-simplicial complex K is a simplicial tree if and only if K has an (n − 1)-
703: complete ordering.
704: Proof. Let K be a simplicial tree with αn (K) = t. Since K is connected, there exists a sequence
705: η1 , . . . , ηl of n-simplices in K, where 2 ≤ l ≤ t, such that A(ηj , Kj ) forms a complete simplicial
706: 
707:                                                         14
```

```text
870:                               
871:                                  , for some 1 ≤ k ≤ n.
872: 
873: Proof. Let K be a connected, pure n-simplicial complex such that
874:                                                           
875:                                                  n        n
876:                                αk (K) = (p − n)     +          ,
877:                                                  k      k+1
878: 
879: for some 1 ≤ k ≤ n.
880: 
881: 
882:                                                           17
883:    If 1 ≤ k ≤ n − 1, then by Lemma 5.9, K is a simplicial tree. Now, consider the case k = n. By
884: Lemma 5.10, we have
885:                                   αn−1 (K) ≤ n(p − n) + 1.
886: Furthermore, by Lemma 5.9, we obtain
887: 
888:                                       αn−1 (K) ≥ (p − n)n + 1.
889: 
890: Combining these inequalities, we conclude that
891: 
892:                                       αn−1 (K) = (p − n)n + 1.
893: 
894: Therefore, by Lemma 5.9, K is a simplicial tree.
895: 
896: 
897:    From Theorem 5.11, we observe that the range of k for the case m = n − 1 in Theorem 1.1 has
898: been improved.
899:    In Fig. 4(a), a pure 2-simplicial complex is shown, consisting of six vertices and nine 1-simplices
900: with no (1, 2)-circuit sequences. Since the simplicial complex is disconnected, it does not form a
901: simplicial tree, thereby disproving both Conjecture 1.2 and Conjecture 1.3.
902: 
903: 
904: 
905: 
906:                      (a)                                                     (b)
907: 
908:                                               Figure 4
909: 
910:    Given a pure n-simplicial complex K with no (m, n)-simplicial cycle sequences for some 0 ≤
911: m ≤ n − 1, we now examine the conditions on αk (K) under which K can be concluded to be a
912: simplicial tree.
913: 
914: Theorem 5.12. A pure n-simplicial complex K with p vertices is a simplicial tree if and only if it
915: satisfies the following three properties:
916: 
917:   1. K has no (m, n)-simplicial cycle sequences for some 0 ≤ m ≤ n − 1.
918: 
919:   2. αn−1 (K) = (p − n)n + 1.
920: 
921:                                                  18
922:     3. αn (K) = p − n.
923: Proof. Let K be a pure n-simplicial complex satisfying properties (1), (2), and (3). From Re-
924: mark 4.9, K has no (n − 1, n)-simplicial cycle sequences. Let L1 , . . . , Lt denote the components of
925: K for some t ≥ 1, such that K = ti=1 Li . For each 1 ≤ i ≤ t, since Li is connected and contains
926:                                    S
927: no (n − 1)-simplicial cycle sequences, Lemma 5.10 implies
928: 
929:                                            αn−1 (Li ) = nαn (Li ) + 1.                             (i)
930: 
931:        Summing (i) over i = 1, . . . , t, we get
932:                                              t
933:                                              X
934:                                 αn−1 (K) =         (nαn (Li ) + 1) = n(p − n) + t.                (ii)
935:                                              i=1
936: 
937:    Comparing (ii) with αn−1 (K) = (p − n)n + 1, it follows that t = 1. Thus, K is connected. By
938: Theorem 5.11, K is a simplicial tree.
939: 
940: 
941:        The above Theorem 5.12 is a generalisation of Theorem 5.13 provided by Beineke and Pippert
942: [6].
943: Theorem 5.13. A pure 2-simplicial complex K with p vertices is a simplicial tree if and only if it
944: satisfies the following three properties:
945:     1. K has no (1, 2)-simplicial cycle sequences.
946: 
947:     2. α1 (K) = 2p − 3.
948: 
949:     3. α2 (K) = p − 2.
950:     In Fig. 4(b), a pure 2-simplicial complex is disconnected, consisting of six vertices and four
951: 2-simplices, with no simplicial cycle. Therefore, if condition (2) of Theorem 5.12 is dropped, the
952: converse of the theorem does not hold.
953: 
954: 
```

```text
964: 
965:        • An acyclic graph with p vertices and p − 1 edges is a tree.
966:     We observed that if the condition (2) is omitted from Theorem 5.12, then the converse is invalid,
967: as illustrated in Fig. 4(b). However, a natural question arises: can condition (2) of Theorem 5.12
968: be relaxed by replacing it with the knowledge of αk (K) for some 1 ≤ k ≤ n − 1? Our current
969: framework does not provide a proof for this, nor have we been able to construct a counterexample.
970: This leads us to the following conjecture.
971: 
972:                                                          19
973: Conjecture 6.1. A pure n-simplicial complex K with p vertices is a simplicial tree if and only if
974: it satisfies the following three properties:
975: 
976:    1. K has no (m, n)-simplicial cycle sequences for some 0 ≤ m ≤ n − 1.
977: 
978:    2. αk (K) = (p − n) nk + k+1
979:                               n
980:                                
981:                                   , for some 1 ≤ k ≤ n − 1.
982: 
983:    3. αn (K) = p − n.
984: 
```

# v2 — 2508.17854v2.txt

```text
1:                                                             Structural Characterisations of (n − 1, n)-Trees
2: 
3:                                                                    Gaurav Kottari∗, Niteesh Sahni†, Qazi J. Azhad‡
4:                                                            Department of Mathematics, Shiv Nadar Institution of Eminence,
5:                                                                    Tehsil Dadri, Gautam Buddha Nagar, 201314,
6:                                                                                Uttar Pradesh, India
7: 
8: 
9: 
10: 
11: arXiv:2508.17854v2 [math.CO] 22 Feb 2026
12:                                                                                               Abstract
```

```text
147: simplices, and the dimension of a simplex is defined as one less than the number of its vertices;
148: in particular, a k-simplex is a simplex of dimension k and hence consists of exactly k + 1 vertices.
149: Accordingly, the dimension of a simplicial complex is the maximum dimension among its simplices.
150: We denote by K k the set of all k-dimensional simplices in a complex K, and by αk (K) the number
151: of such simplices. Given two simplices σ and τ in a simplicial complex K, τ is a face of σ if every
152: vertex of τ is also a vertex of σ. A simplicial complex K is called a pure n-simplicial complex
153: if every simplex in K is a face of at least one n-simplex of K. In particular, a pure 1-simplicial
154: complex K with vertex set V can be viewed as a simple, undirected graph G(W, E) with no isolated
155: vertices, where W = V and E = K 1 . A subset L ⊆ K of simplices is termed a subcomplex of K if
156: it satisfies the following condition: for every simplex σ in L, if τ is a face of σ in K, then τ must
157: also be an element of L. These definitions are standard and can be found in foundational texts on
158: combinatorial algebraic topology [3, 7].
159: 
160: 2.2    Dewdney’s framework
161: Dewdney’s (m, n)-tree framework [1] provides one of the earliest higher-dimensional analogues
162: of graph-theoretic trees. The theory is based on an inductive construction of pure n-simplicial
163: 
164: 
165:                                                   3
166: complexes via ordered addition of n-simplices, together with connectivity notions defined through
167: alternating sequences of simplices. Throughout this subsection, we assume 0 ≤ m ≤ n − 1 unless
168: otherwise stated.
169: 
170: Definition 2.1. Let S be a subset of a simplicial complex K. The closure of S in K is the smallest
171: subcomplex S of K such that S ⊆ S, that is,
172: 
173:                             S = {τ ∈ K : τ is a face of σ for some σ ∈ S}.
174: 
175: Definition 2.2. The attachment of an n-simplex ηi in a pure n-simplicial complex K is the sub-
176: complex denoted by A(ηi , K) and is defined as
177: 
178:                       A(ηi , K) = {σ ⊂ ηi | ∃ ηj ∈ K n \ {ηi } such that σ ⊂ ηj } .
179: 
180:      In other words, A(ηi , K) consists of all faces of ηi that are shared with some other n-simplex of
181: K.
182: 
183: Definition 2.3. A simplicial complex K with p + 1 vertices is called m-complete if the dimension
184: of K is m, and every subset of the vertex set of K with m + 1 elements is a simplex in K. In
185: particular, if m = p, then K is called a complete simplicial complex.
186: 
187: Definition 2.4. A pure n-simplicial complex K is said to have an m-ordering if there exists a se-
188: quence of distinct n-simplices η1 , . . . , ηt , where t = αn (K), such that A(ηi , Ki ) is an m-dimensional
189: simplicial complex for all 2 ≤ i ≤ t, where Ki = {η1 , . . . , ηi }. Furthermore, K is said to have an
190: m-complete ordering if A(ηi , Ki ) forms a complete simplicial complex with m + 1 vertices for all
191: 2 ≤ i ≤ t.
192: 
193:    Note: We adopt a simplified version of the notation and terminology introduced by Dewd-
194: ney [1]. In particular, an m-complete ordering corresponds to Dewdney’s Km+1  m -ordering, and
195:                                    m
196: an m-ordering corresponds to his S≥1 -ordering. This reformulation reduces notational complexity
197: while preserving the original combinatorial content.
198:    Using the above notions, Dewdney defined (m, n)-trees as follows.
199: 
200: Definition 2.5. A pure n-simplicial complex K is called an (m, n)-tree if K has an m-complete
201: ordering.
202: 
203:    To further characterise (m, n)-trees, Dewdney [1] introduced the notions of (m, n)-walks, (m, n)-
204: paths, (m, n)-connectedness, and (m, n)-circuits, which we now recall.
205: 
206: Definition 2.6. In a pure n-dimensional simplicial complex K, an (m, n)-walk sequence between
207: two m-simplices σi and σj is an alternating sequence of m-simplices and n-simplices, given by
208: 
209:                                   σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj ,
210: 
211: such that for all 1 ≤ k ≤ r, the simplices σk and σk+1 are distinct and both are faces of ηk . The
212: integer r is called the length of the (m, n)-walk sequence.
213: 
214: Definition 2.7. An (m, n)-walk sequence
215: 
216:                                   σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj
217: 
218: is called an (m, n)-path sequence if all simplices in the sequence are distinct.
219: 
220: 
221:                                                          4
222: Definition 2.8. A pure n-simplicial complex K is (m, n)-connected if there exists an (m, n)-path
223: sequence between every pair of m-simplices in K.
224: 
225: Definition 2.9. An (m, n)-walk sequence
226: 
227:                                      σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj
228: 
229: is called an (m, n)-circuit sequence if it satisfies the following conditions:
230: 
231:     1. σi = σj .
232: 
233:     2. For all p, q with 1 ≤ p, q ≤ r and p ̸= q, we have σp ̸= σq and ηp ̸= ηq .
234: 
235: 
```

```text
556: Definition 3.8. An (m, n)-circuit sequence σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σi in a pure n-
557: simplicial complex K is called an (m, n)-simplicial cycle sequence if the following conditions hold:
558: 
559: 
560:                                                     11
561:    1. r ≥ 3.
562: 
563:    2. For some 2 ≤ k ≤ r − 1, σi is not a face of ηk .
564: 
565:    3. For all 2 ≤ z ≤ r, σz is a face of an (n − 1)-simplex σz′ of K such that σz′ is a face of both
566:       ηz−1 and ηz .
567: 
568: The subcomplex C = {η1 , ..., ηr } of K is called simplicial cycle.
569:    The complex K is called cyclic if it admits an (m, n)-simplicial cycle sequence for some 0 ≤
570: m ≤ n − 1, and acyclic otherwise.
571: 
572:     We now give a characterisation of cyclic pure n-simplicial complexes in terms of the combina-
```

```text
641:     We begin by generalising the result: A graph is a tree if and only if it is connected and acyclic.
642: Theorem 4.1. A pure n-simplicial complex K is an (n − 1, n)-tree if and only if it is connected
643: and acyclic.
644: Proof. Let K be an (n − 1, n)-tree with αn (K) = t. Then there exists a sequence of distinct n-
645: simplices η1 , . . . , ηt such that, for all 2 ≤ i ≤ t, A(ηi , Ki ) is a complete simplicial complex with n
646: vertices, where Ki = {η1 , . . . , ηi }. By Theorem 3.3, K is connected.
```

```text
1014: 
1015: Therefore, by Lemma 4.6, K is an (n − 1, n)-tree.
1016: 
1017:     We next present an example showing that the conditions proposed in Conjectures 1.2 and 1.3 are
1018: not sufficient to characterise (m, n)-trees. In Figure 3, a pure 2-simplicial complex K is shown with
1019: α0 (K) = 6 vertices and α1 (K) = 9 edges. The complex has no (1, 2)-circuit sequences and satisfies
1020: the enumerative identity appearing in Conjectures 1.2 and 1.3. However, K is disconnected and
1021: hence is not an (1, 2)-tree. This provides a counterexample to the ‘if’ direction of both conjectures.
1022: 
1023: 
1024: 
1025: 
1026: Figure 3: A pure 2-simplicial complex with no (1, 2)-circuit sequences that is disconnected, and
1027: hence not an (1, 2)-tree.
1028: 
1029:     We now present a modified version of Dewdney’s conjecture for the case m = n − 1. The
1030: modification consists of strengthening the circuit-freeness assumption and replacing the original
1031: enumerative identity by explicit counting conditions on (n − 1)- and n-simplices. The resulting
1032: formulation restores the classical correspondence between acyclicity, counting, and tree structure
1033: in the (n − 1, n)-setting.
1034: 
1035: Theorem 4.9. A pure n-simplicial complex K with p vertices is an (n − 1, n)-tree if and only if it
1036: satisfies the following three properties:
1037: 
1038:   1. K has no (m, n)-circuit sequences for some 0 ≤ m ≤ n − 1.
1039: 
1040:                                                  20
1041: Figure 4: Disconnected pure n-simplicial complex with six vertices, four 2-simplices, and contains
1042: no (1, 2)-circuit sequence
1043: 
1044: 
1045:   2. αn−1 (K) = (p − n)n + 1.
1046: 
1047:   3. αn (K) = p − n.
1048: Proof. Let K be a pure n-simplicial complex satisfying properties (1), (2), and (3). Since for any
1049: 0 ≤ m ≤ n − 2, an (m, n)-circuit sequence can be constructed from an (n − 1, n)-circuit sequence,
1050: it follows that K has no (n − 1, n)-circuit sequences.
1051:     Let L1 , . . . , Lr denote the components of K for some r ≥ 1, so that K = ri=1 Li . For all
1052:                                                                                   S
1053: 1 ≤ i ≤ r, since Li is connected and contains no (n − 1, n)-circuit sequences, Lemma 4.7 implies
1054: 
1055:                                        αn−1 (Li ) = nαn (Li ) + 1.                                 (i)
1056: 
1057:    Summing (i) over i = 1, . . . , r, we obtain
1058:                               r
1059:                               X                       r
1060:                                                       X
1061:                                                  
1062:                  αn−1 (K) =         nαn (Li ) + 1 = n   αn (Li ) + r = n(p − n) + r.              (ii)
1063:                               i=1                       i=1
1064: 
1065:     Comparing (ii) with the identity αn−1 (K) = (p − n)n + 1, we conclude that r = 1. Hence, K
1066: is connected. By Theorem 4.8, K is an (n − 1, n)-tree.
1067: 
1068:     To see that condition (2) in Theorem 4.9 is necessary and cannot be omitted, consider the
1069: example in Figure 4. In this figure, a pure 2-simplicial complex is disconnected, consisting of six
1070: vertices and four 2-simplices, with no (1, 2)-circuit sequence. This shows that without condition
1071: (2), the complex satisfies conditions (1) and (3) of Theorem 4.9 but fails to be an (1, 2)-tree due to
1072: being disconnected.
1073:     However, a natural question arises: can condition (2) of Theorem 4.9 be relaxed by replacing it
1074: with the knowledge of αk (K) for some 1 ≤ k ≤ n − 1? Our current framework does not provide a
1075: proof for this, nor have we been able to construct a counterexample. This leads us to the following
1076: conjecture.
1077: 
1078:                                                    21
1079: Conjecture 4.10. A pure n-simplicial complex K with p vertices is an (n − 1, n)-tree if and only
1080: if it satisfies the following three properties:
1081: 
1082:   1. K has no (m, n)-circuit sequences for some 0 ≤ m ≤ n − 1.
1083: 
1084:   2. αk (K) = (p − n) nk + k+1
1085:                              n
1086:                               
1087:                                  , for some 1 ≤ k ≤ n − 1.
1088: 
1089:   3. αn (K) = p − n.
1090: 
1091: 
```

# v3 — 2508.17854.txt

```text
1:                                                               Structural Characterisations of (n − 1, n)-Trees
2: 
3:                                                                              Gaurav Kottari∗, Niteesh Sahni†
4:                                                              Department of Mathematics, Shiv Nadar Institution of Eminence,
5:                                                                      Tehsil Dadri, Gautam Buddha Nagar, 201314,
6:                                                                                  Uttar Pradesh, India
7: 
8: 
9: 
10:                                                                                                  Abstract
11:                                                         We study higher-dimensional analogues of graph-theoretic trees within the class of pure n-
12: 
13: 
14: 
15: 
16: arXiv:2508.17854v3 [math.CO] 1 Aug 2026
17:                                                     simplicial complexes. Focusing on the case m = n − 1 in Dewdney’s (m, n)-tree framework, we
18:                                                     introduce refined notions of path and circuit sequences that overcome the structural limitations
```

```text
139: in particular, a k-simplex is a simplex of dimension k and hence consists of exactly k + 1 vertices.
140: Accordingly, the dimension of a simplicial complex is the maximum dimension among its simplices.
141: We denote by K k the set of all k-dimensional simplices in a complex K, and by αk (K) the number
142: of such simplices. Given two simplices σ and τ in a simplicial complex K, τ is a face of σ if every
143: vertex of τ is also a vertex of σ. A simplicial complex K is called a pure n-simplicial complex
144: if every simplex in K is a face of at least one n-simplex of K. In particular, a pure 1-simplicial
145: complex K with vertex set V can be viewed as a simple, undirected graph G(W, E) with no isolated
146: vertices, where W = V and E = K 1 . A subset L ⊆ K of simplices is termed a subcomplex of K if
147: it satisfies the following condition: for every simplex σ in L, if τ is a face of σ in K, then τ must
148: also be an element of L. These definitions are standard and can be found in foundational texts on
149: combinatorial algebraic topology [7, 10].
150: 
151: 2.2    Dewdney’s framework
152: Dewdney’s (m, n)-tree framework [4] provides one of the earliest higher-dimensional analogues
153: of graph-theoretic trees. The theory is based on an inductive construction of pure n-simplicial
154: complexes via ordered addition of n-simplices, together with connectivity notions defined through
155: alternating sequences of simplices. Throughout this subsection, we assume 0 ≤ m ≤ n − 1 unless
156: otherwise stated.
157: 
158: 
159: 
160: 
161:                                                   3
162: Definition 2.1. Let S be a subset of a simplicial complex K. The closure of S in K is the smallest
163: subcomplex S of K such that S ⊆ S, that is,
164: 
165:                             S = {τ ∈ K : τ is a face of σ for some σ ∈ S}.
166: 
167: Definition 2.2. The attachment of an n-simplex ηi in a pure n-simplicial complex K is the sub-
168: complex denoted by A(ηi , K) and is defined as
169: 
170:                       A(ηi , K) = {σ ⊂ ηi | ∃ ηj ∈ K n \ {ηi } such that σ ⊂ ηj } .
171: 
172:      In other words, A(ηi , K) consists of all faces of ηi that are shared with some other n-simplex of
173: K.
174: 
175: Definition 2.3. A simplicial complex K with p + 1 vertices is called m-complete if the dimension
176: of K is m, and every subset of the vertex set of K with m + 1 elements is a simplex in K. In
177: particular, if m = p, then K is called a complete simplicial complex.
178: 
179: Note: In this work, we adopt a simplified version of the notation and terminology introduced
180: by Dewdney [4]. In particular, what we call an m-complete ordering corresponds to Dewdney’s
181:   m -ordering, and an m-ordering corresponds to his S m -ordering. This reformulation reduces
182: Km+1                                                    ≥1
183: notational complexity while preserving the original combinatorial content. With this terminology
184: in place, we now define these notions formally.
185: 
186: Definition 2.4. A pure n-simplicial complex K is said to have an m-ordering if there exists a se-
187: quence of distinct n-simplices η1 , . . . , ηt , where t = αn (K), such that A(ηi , Ki ) is an m-dimensional
188: simplicial complex for all 2 ≤ i ≤ t, where Ki = {η1 , . . . , ηi }. Furthermore, K is said to have an
189: m-complete ordering if A(ηi , Ki ) forms a complete simplicial complex with m + 1 vertices for all
190: 2 ≤ i ≤ t.
191: 
192:      Using the above notions, Dewdney defined (m, n)-trees as follows.
193: 
194: Definition 2.5. A pure n-simplicial complex K is called an (m, n)-tree if K has an m-complete
195: ordering.
196: 
197:    To further characterise (m, n)-trees, Dewdney [4] introduced the notions of (m, n)-walks, (m, n)-
198: paths, (m, n)-connectedness, and (m, n)-circuits, which we now recall.
199: 
200: Definition 2.6. In a pure n-dimensional simplicial complex K, an (m, n)-walk sequence between
201: two m-simplices σi and σj is an alternating sequence of m-simplices and n-simplices, given by
202: 
203:                                   σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj ,
204: 
205: such that for all 1 ≤ k ≤ r, the simplices σk and σk+1 are distinct and both are faces of ηk . The
206: integer r is called the length of the (m, n)-walk sequence.
207: 
208: Definition 2.7. An (m, n)-walk sequence
209: 
210:                                   σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj
211: 
212: is called an (m, n)-path sequence if all simplices in the sequence are distinct.
213: 
214: Definition 2.8. A pure n-simplicial complex K is (m, n)-connected if there exists an (m, n)-path
215: sequence between every pair of m-simplices in K.
216: 
217:                                                          4
218: Definition 2.9. An (m, n)-walk sequence
219: 
220:                                   σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σj
221: 
222: is called an (m, n)-circuit sequence if it satisfies the following conditions:
223: 
224:     1. σi = σj .
225: 
226:     2. For all p, q with 1 ≤ p, q ≤ r and p ̸= q, we have σp ̸= σq and ηp ̸= ηq .
227: 
228: 
229: 3     Paths, cycles, and connectivity in pure simplicial complexes
```

```text
278:     From Proposition 3.1, it follows that if a pure n-simplicial complex K is (n − 1, n)-connected,
279: then for all 0 ≤ m ≤ n − 1 there exists an (m, n)-path sequence between any pair of m-simplices
280: of K. Consequently, K is (m, n)-connected for all 0 ≤ m ≤ n − 1. We therefore refer to such a
281: complex as connected. If K is not (n − 1, n)-connected, we refer to it as disconnected.
282:     We now examine the basic structural consequences for connected pure n-simplicial complexes.
283: In particular, this notion of connectivity induces a decomposition of a pure n-simplicial complex
284: into components. This provides a foundation for the structural developments that follow.
285:     We now formalise this by defining components associated with connected pure n-simplicial
286: complexes.
287: 
288: Definition 3.2. A pure n-subcomplex L of a pure n-simplicial complex K is called a component of
289: K if L is connected and for every ηi ∈ K n \ Ln , the subcomplex L ∪ {ηi } is disconnected.
```

```text
618: Definition 3.9. An (m, n)-circuit sequence σi = σ1 , η1 , σ2 , . . . , σr , ηr , σr+1 = σi in a pure n-
619: simplicial complex K is called an (m, n)-Dewdney cycle sequence if the following conditions hold:
620:   1. r ≥ 3.
621: 
622:   2. For some 2 ≤ k ≤ r − 1, σi is not a face of ηk .
623: 
624:   3. For all 2 ≤ z ≤ r, σz is a face of an (n − 1)-simplex σz′ of K such that σz′ is a face of both
625:      ηz−1 and ηz .
626: The subcomplex C = {η1 , ..., ηr } of K is called Dewdney cycle.
627:    The complex K is called cyclic if it admits an (m, n)-Dewdney cycle sequence for some 0 ≤ m ≤
628: n − 1, and acyclic otherwise.
```

```text
729:     We begin by generalising the result: A graph is a tree if and only if it is connected and acyclic.
730: 
731:                                                          15
732: Theorem 4.1. A pure n-simplicial complex K is an (n − 1, n)-tree if and only if it is connected
733: and acyclic.
734: 
735: Proof. Let K be an (n − 1, n)-tree with αn (K) = t. Then there exists a sequence of distinct n-
736: simplices η1 , . . . , ηt such that, for all 2 ≤ i ≤ t, A(ηi , Ki ) is a complete simplicial complex with n
```

```text
1095: m = 1, the conditions in Conjectures 1.2 and 1.3 coincide, as the index k can only take the value
1096: 1. Hence, the following example disproves the “if” direction of both conjectures.
1097:     Consider the pure 2-simplicial complex
1098: 
1099:                                  K = {{1, 2, 3}, {2, 5, 6}, {3, 4, 5}},
1100: 
1101: where the vertex set is V (K) = {1, 2, 3, 4, 5, 6} (see Figure 4). Then α0 (K) = 6 and α1 (K) = 9.
1102: The complex has no (1, 2)-circuit sequences and satisfies the enumerative identity in Conjectures 1.2
1103: and 1.3. However, K is disconnected and hence is not an (1, 2)-tree. This provides a counterexample
1104: to the “if” direction of both conjectures.
1105:     Before stating a modified version of Dewdney’s conjecture, we establish a simple relationship
1106: between circuit sequences of different dimensions. The following lemma shows that the existence of
1107: an (n − 1, n)-circuit sequence forces the existence of an (m, n)-circuit sequence for every 0 ≤ m ≤
1108: n − 2.
1109: 
1110: Lemma 4.9. If a pure n-simplicial complex K contains an (n − 1, n)-circuit sequence, then for
1111: every 0 ≤ m ≤ n − 2, it also contains an (m, n)-circuit sequence.
1112: 
1113: Proof. Let
1114:                               σi = σ1 , η1 , σ2 , η2 , . . . , σr , ηr , σr+1 = σi
1115: be an (n − 1, n)-circuit sequence, and let 0 ≤ m ≤ n − 2.
1116:     Choose an arbitrary m-face τ1 of σ1 . Since σ2 is distinct from σ1 , there exists an m-face τ2 of
1117: σ2 such that τ2 ̸= τ1 . If τ1 is a face of η2 , then
1118: 
1119:                                               τ1 , η1 , τ2 , η2 , τ1
1120: 
1121: is an (m, n)-circuit sequence, and we are done.
1122: 
1123:                                                        22
1124: Figure 4: A pure 2-simplicial complex K = {{1, 2, 3}, {2, 5, 6}, {3, 4, 5}} illustrating a counterex-
1125: ample to Conjectures 1.2 and 1.3.
1126: 
1127:     Assume therefore that τ1 is not a face of η2 . Choose an m-face τ3 of σ3 with τ3 ̸= τ2 . If τ1 is a
1128: face of η3 , then
1129:                                        τ1 , η1 , τ2 , η2 , τ3 , η3 , τ1
1130: is an (m, n)-circuit sequence.
1131:     Suppose now that τ1 is not a face of η3 . Choose an m-face τ4 of σ4 with τ4 ̸= τ3 . If τ4 = τ2 ,
```

```text
1154: Figure 5: Disconnected pure 2-simplicial complex K = {{1, 2, 4}, {1, 2, 3}, {2, 3, 5}, {4, 5, 6}} with
1155: six vertices, four 2-simplices, and contains no (1, 2)-circuit sequence.
1156: 
1157: 
1158: Theorem 4.10. A pure n-simplicial complex K with p vertices is an (n − 1, n)-tree if and only if
1159: it satisfies the following three properties:
1160: 
1161:   1. K has no (m, n)-circuit sequences for some 0 ≤ m ≤ n − 1.
1162: 
1163:   2. αn−1 (K) = (p − n)n + 1.
1164: 
1165:   3. αn (K) = p − n.
1166: 
1167: Proof. Let K be a pure n-simplicial complex satisfying properties (1), (2), and (3). It follows from
1168: Lemma 4.9 that K contains no (n − 1, n)-circuit sequences.
1169:    Let L1 , . . . , Lr denote the components of K for some r ≥ 1, so that K = ri=1 Li . For all
1170:                                                                                   S
1171: 1 ≤ i ≤ r, since Li is connected and contains no (n − 1, n)-circuit sequences, Lemma 4.7 implies
1172: 
1173:                                        αn−1 (Li ) = nαn (Li ) + 1.                                 (i)
1174: 
1175:    Summing (i) over i = 1, . . . , r, we obtain
1176:                               r
1177:                               X                       r
1178:                                                       X
1179:                                                  
1180:                  αn−1 (K) =         nαn (Li ) + 1 = n   αn (Li ) + r = n(p − n) + r.              (ii)
1181:                               i=1                        i=1
1182: 
1183:     Comparing (ii) with the identity αn−1 (K) = (p − n)n + 1, we conclude that r = 1. Hence, K
1184: is connected. By Theorem 4.8, K is an (n − 1, n)-tree.
1185: 
1186:    To see that condition (2) in Theorem 4.10 is necessary and cannot be omitted, consider the
1187: example in Figure 5. In this figure, a pure 2-simplicial complex
1188: 
1189:                               K = {{1, 2, 4}, {1, 2, 3}, {2, 3, 5}, {4, 5, 6}}
1190: 
1191: 
1192:                                                     24
1193: is disconnected, consisting of six vertices and four 2-simplices, with no (1, 2)-circuit sequence. This
1194: shows that without condition (2), the complex satisfies conditions (1) and (3) of Theorem 4.10 but
1195: fails to be an (1, 2)-tree due to being disconnected.
1196:     However, a natural question arises: can condition (2) in Theorem 4.10 be relaxed by replacing
1197: it with the knowledge of αk (K) for some 1 ≤ k ≤ n − 1?
1198:     For n = 2, the above question is true, as it follows from Theorem 4.10, where knowledge of
1199: α1 (K) suffices. This naturally leads to the following question of whether the same holds for n ≥ 3.
1200: 
1201: Question 4.11. Let K be a pure n-simplicial complex with p vertices. Suppose that for some
1202: 1 ≤ k ≤ n − 1,                             
1203:                                    n        n
1204:                   αk (K) = (p − n)   +            and αn (K) = p − n,
1205:                                    k     k+1
1206: and that K has no (m, n)-circuit sequences for some 0 ≤ m ≤ n − 1.
1207:    Does it follow that K is an (n − 1, n)-tree?
1208: 
1209:    Our current framework does not provide a proof for this, nor have we been able to construct a
1210: counterexample, and we leave it as an open question for future work.
1211: 
1212: 
```


# Supplement v1

```text
411:    Now, cyclic and acyclic pure n-simplicial complexes are defined analogously to the graph-
412: theoretic definitions of cyclic and acyclic graphs, respectively.
413: 
414: Definition 4.3. A pure n-simplicial complex is acyclic if it contains no simplicial cycles; otherwise,
415: it is cyclic.
416: 
417: Definition 4.4. An m-simplex of a pure n-simplicial complex K is called a joint m-simplex if it
418: is a face of at least two distinct n-simplices.
```

# Supplement v2

```text
141: for the refinements and extensions developed in this work.
142: 
143: 2.1    Simplicial complexes
144: A simplicial complex K is a collection of non-empty subsets of a finite vertex set V , satisfying
145: the condition that every singleton subset is included in K, and that every non-empty subset of
146: an element of K is also an element of K. The elements of a simplicial complex are referred to as
147: simplices, and the dimension of a simplex is defined as one less than the number of its vertices;
148: in particular, a k-simplex is a simplex of dimension k and hence consists of exactly k + 1 vertices.
149: Accordingly, the dimension of a simplicial complex is the maximum dimension among its simplices.
150: We denote by K k the set of all k-dimensional simplices in a complex K, and by αk (K) the number
151: of such simplices. Given two simplices σ and τ in a simplicial complex K, τ is a face of σ if every
152: vertex of τ is also a vertex of σ. A simplicial complex K is called a pure n-simplicial complex
153: if every simplex in K is a face of at least one n-simplex of K. In particular, a pure 1-simplicial
154: complex K with vertex set V can be viewed as a simple, undirected graph G(W, E) with no isolated
155: vertices, where W = V and E = K 1 . A subset L ⊆ K of simplices is termed a subcomplex of K if
156: it satisfies the following condition: for every simplex σ in L, if τ is a face of σ in K, then τ must
157: also be an element of L. These definitions are standard and can be found in foundational texts on
158: combinatorial algebraic topology [3, 7].
```
```text
238: Having introduced (n − 1, n)-connectivity in Section 2.2, we now examine its basic structural con-
239: sequences for pure n-simplicial complexes. In particular, this notion of connectivity induces a
240: decomposition of a pure n-simplicial complex into components. This provides a stable foundation
241: for the structural developments that follow.
242:     We now formalise this by defining components associated with (n − 1, n)-connectivity.
243: 
244: Definition 3.1. A pure n-subcomplex L of a pure n-simplicial complex K is called a component
```

# Supplement v3

```text
135: A simplicial complex K is a collection of non-empty subsets of a finite vertex set V , satisfying
136: the condition that every singleton subset is included in K, and that every non-empty subset of
137: an element of K is also an element of K. The elements of a simplicial complex are referred to as
138: simplices, and the dimension of a simplex is defined as one less than the number of its vertices;
139: in particular, a k-simplex is a simplex of dimension k and hence consists of exactly k + 1 vertices.
140: Accordingly, the dimension of a simplicial complex is the maximum dimension among its simplices.
141: We denote by K k the set of all k-dimensional simplices in a complex K, and by αk (K) the number
142: of such simplices. Given two simplices σ and τ in a simplicial complex K, τ is a face of σ if every
143: vertex of τ is also a vertex of σ. A simplicial complex K is called a pure n-simplicial complex
144: if every simplex in K is a face of at least one n-simplex of K. In particular, a pure 1-simplicial
145: complex K with vertex set V can be viewed as a simple, undirected graph G(W, E) with no isolated
146: vertices, where W = V and E = K 1 . A subset L ⊆ K of simplices is termed a subcomplex of K if
147: it satisfies the following condition: for every simplex σ in L, if τ is a face of σ in K, then τ must
148: also be an element of L. These definitions are standard and can be found in foundational texts on
149: combinatorial algebraic topology [7, 10].
```
```text
274: omitting the intermediate portion, as in the case τp+3 = τp+1 above.
275:    Proceeding in this manner along the finite (n−1, n)-path sequence from σi′ to σj ′ , we eventually
276: obtain an (m, n)-path sequence between τi and τj .
277: 
278:     From Proposition 3.1, it follows that if a pure n-simplicial complex K is (n − 1, n)-connected,
279: then for all 0 ≤ m ≤ n − 1 there exists an (m, n)-path sequence between any pair of m-simplices
280: of K. Consequently, K is (m, n)-connected for all 0 ≤ m ≤ n − 1. We therefore refer to such a
281: complex as connected. If K is not (n − 1, n)-connected, we refer to it as disconnected.
282:     We now examine the basic structural consequences for connected pure n-simplicial complexes.
283: In particular, this notion of connectivity induces a decomposition of a pure n-simplicial complex
284: into components. This provides a foundation for the structural developments that follow.
285:     We now formalise this by defining components associated with connected pure n-simplicial
286: complexes.
287: 
288: Definition 3.2. A pure n-subcomplex L of a pure n-simplicial complex K is called a component of
```
