
## 375646 TxGraffiti's annihilation-number bound for connected graphs
1: 
2: 
3: 
4: An annihilation-number Caro-Wei bound:a TxGraffiti conjecture and an independence-number bracket
5: 
6: 
7: 
8:  
9: 
10:   // Restore the saved color scheme preference, or
11:   // enact the browser preference if "automatic", 
12:   // without expecting DOM load to have completed.
13:   //
175: 
176: 
177: An annihilation-number Caro-Wei bound:
178: a TxGraffiti conjecture and an independence-number bracket
179: 
180: 
181: 
182: Chakshu Gupta
183: 
184: Affiliation: College of Computing, Georgia Institute of Technology
185: 
186: Email: cgupta65@gatech.edu
187: 
192: 
193: Automated conjecturing programs scan collections of graphs for inequalities
194: between invariants that no stored graph violates, then offer the survivors for
195: proof or refutation. TxGraffiti, one such program, conjectured that every
196: nontrivial connected graph  G  satisfies
197:  \alpha(G)\geq\bigl(a(G)+R(G)\bigr)/\Delta(G) , where  \alpha  is the
198: independence number,  a  the annihilation number,  R  the residue, and
199:  \Delta  the maximum degree. Established only for two special families of
200: graphs, the conjecture has otherwise remained open. The note proves the
201: degree-sequence inequality  a\leq\tfrac{\Delta+1}{2}W , where  W  is the
202: Caro-Wei sum; the same inequality is known for the independence number in
203: place of  a . Combined with the classical lower bounds  \alpha\geq R  and
204:  \alpha\geq W , it proves the conjecture for every connected graph of maximum
205: degree at least three, and a direct argument settles maximum degree two; the
206: conjecture fails only for the single edge, of maximum degree one. The
207: inequality also brackets the independence number between the polynomial-time
208: quantities  R  and  a , within a factor  (\Delta+1)/2 . The
209: conjecture’s bound is sharp, with equality attained, for instance, by the
210: complete graph on four vertices.
211:   
212: 
213: 
214: 
215: 1 Introduction
216: 
217: 
218: 
219: 
220: The Graffiti system [Faj88] makes conjectures by searching
221: a database of graphs for an inequality between invariants that no stored graph
222: violates, then offering the surviving relation as a conjecture. Its successor
223: TxGraffiti is the source of the following.
224: 
225: 
226: 
227: Conjecture 1 ([DBP25]).
228: 
229: 
230: 
231: If  G  is a nontrivial connected graph, then
232:  \alpha(G)\geq\bigl(a(G)+R(G)\bigr)/\Delta(G) , and this bound is sharp.
233: 
234: 
235: 
236: 
249: 
250: The annihilation number is an upper bound on  \alpha  [Pep09], while
251: the residue [FMS91] and the Caro-Wei sum  W  [Car79, Wei81]
252: are lower bounds;  W  sums  1/(d+1)  over all vertices. The conjecture is open in
253: general, established only for regular bipartite and cubic König-Egerváry
254: graphs [DBP25]. Existing bounds estimate  \alpha 
255: itself: the Degree Sequence Index Strategy bounds it from above
256: by annihilation-type quantities [CP14], and the Caro-Wei sum
257: estimates it within the best-possible factor  (\Delta+1)/2 , that is,
258:  \alpha\leq\tfrac{\Delta+1}{2}W  [BHR18]. Proving the conjecture,
259: however, requires a bound on the annihilation number itself, which prior
260: estimates of  \alpha  do not supply.
261: 
262: 
263: 
264: 
265: Theorem 1 provides such a bound:  a\leq\tfrac{\Delta+1}{2}W ,
266: obtained by applying the argument of [BHR18] to the annihilation head
267: in place of a maximum independent set. Combined with the classical lower bounds,
268: it proves the conjecture for every connected graph of maximum degree at least
269: two (Theorem 2); the single edge, of maximum degree one, is the sole
270: exception, where the conjecture fails. The conjectured bound  (a+R)/\Delta  is
271: sharp, attained for instance at the complete graph  K_{4} 
272: (Corollary 1), though for  \Delta\geq 3 , it is dominated by
273:  R  (Corollary 2). The same inequality also brackets
274: the independence number between the polynomial-time quantities  R  and
275:  a , which differ by at most a factor  (\Delta+1)/2  (Corollary 3).
276: 
277: 
278: 
279: 
405: 
406: 
407: 
408: Theorem 2 (Resolution of Conjecture 1).
409: 
410: 
411: 
412: Every connected graph  G  with  \Delta(G)\geq 2  satisfies
413: 
414: 
415: 
416: 
417:  \Delta(G)\,\alpha(G)\ \geq\ a(G)+R(G). 
590: 
591: 
592: 
593: Previously the conjecture  \alpha\geq(a+R)/\Delta  had been verified only for
594: regular bipartite graphs and cubic König-Egerváry graphs. This note
595: resolves it for every connected graph of maximum degree at least two; the
596: single edge, with  \Delta=1 , is the unique counter-example. The argument
597: reduces to the inequality  a\leq\tfrac{\Delta+1}{2}W , capping the ratio
598: between the annihilation number and the Caro-Wei sum at  (\Delta+1)/2 ; the
599: constant is best possible, attained on regular sequences of even order.
600: Combined with the classical lower bounds  \alpha\geq W  and  \alpha\geq R ,
601: this inequality forces the conjecture.
602: 
603: 
604: 
605: 
606: The conjectured bound  (a+R)/\Delta  is itself dominated by  R  for
607:  \Delta\geq 3 , so the conjecture names a relation among classical
608: degree-sequence quantities of  \alpha  rather than tightening any of them.
609: The bracket  R\leq\alpha\leq a  localizes  \alpha  in polynomial
610: time within a factor  (\Delta+1)/2 , refining the Caro-Wei bracket. Equality
611: in the conjecture forces  \alpha=R  and  (\Delta-1)\alpha=a ; the
612: complete graph  K_{4}  attains both, as do paths and cycles with  R=\alpha .
613: A structural description of all equality graphs is left open.
614: 
615: 
616: 
617: 
618: References
619: 
620: 
680: Siemion Fajtlowicz.
681: 
682: 
683: On conjectures of Graffiti.
684: 
685: 
686: Discrete Math., 72(1-3):113–118, 1988.
687: 
688: 
689:       
690: 
691: [FMS91]
692: 

## 375666 Dasgupta–Kárólyi–Serra–Szegedy conjecture for distinct products in finite abelian groups
214: 
215: 
216: 
217: Let  G=\{a_{1},\ldots,a_{n}\}  be an abelian group, and let  b_{1},\ldots,b_{n}\in G . In 1952, M. Hall, Jr. [6] proved that there exists a permutation  \sigma\in S_{n}  such that  a_{1}b_{\sigma(1)},\ldots,a_{k}b_{\sigma(k)}  are pairwise distinct if and only if  b_{1}\cdots b_{n}=e , where  e  denotes the identity element of  G . Snevily [8] proposed an interesting conjecture that if  A=\{a_{1},\ldots,a_{k}\}  and  B=\{b_{1},\ldots,b_{k}\}  are subsets of an abelian group  G  of odd order then  a_{1}b_{\sigma(1)},\ldots,a_{k}b_{\sigma(k)}  are pairwise distinct for some permutation  \sigma\in S_{k} . Snevily’s conjecture was confirmed by Alon [1] when  G  is a cyclic group of prime order. Later, Dasgupta, Károlyi, Serra and Szegedy [3] confirmed Snevily’s conjecture when  G  is a cyclic group of odd order. Gao and Wang [5] verified Snevily’s conjecture under the condition that  k<\sqrt{p(G)} , where  p(G)  denotes the smallest prime factor of  |G| . Snevily’s conjecture was finally solved by Arsovski [2]. For the development of Snevily’s conjecture in combination with restricted sumsets, one may refer to [9].
218: 
219: 
220: 
221: 
222: When  G  is a cyclic group of prime order, Alon [1] actually proved a stronger result, in which  b_{1},\ldots,b_{k}  are not necessarily distinct.
223: 
224: 
225: 
226: Theorem 1.1 (Alon [1]).
247: 
248: 
249: 
250: Motivated by Theorems 1.1 and 1.2, the following conjecture was proposed in [3].
251: 
252: 
253: 
254: Conjecture 1.1 (Dasgupta-Károlyi-Serra-Szegedy).
255: 
256: 
257: 
258: Let  G  be a finite abelian group with  |G|>1 . Let  p  be the smallest prime of  |G| . Let  k<p . Let  a_{1},\ldots,a_{k}\in G  be pairwise distinct and let  b_{1},\ldots,b_{k}\in G . Then  a_{1}b_{\sigma(1)},\ldots,a_{k}b_{\sigma(k)}  are pairwise distinct for some permutation  \sigma\in S_{k} .
259: 
260: 
261: 
262: 
263: 
264: In 2011, Feng, Sun and Xiang [4] introduced the method of exterior algebra to study Conjecture 1.1 and related problems. They proved the following (see [4, Corollary 1.7]).
265: 
266: 
267: 
268: Theorem 1.3 (Feng-Sun-Xiang [4]).
269: 
270: 
271: 
272: Conjecture 1.1 is true when  G  is an abelian  p -group.
273: 
274: 
275: 
276: 
277: 
278: Indeed, Feng, Sun and Xiang obtained a stronger conclusion which asserts that Conjecture 1.1 is true when the
279: smallest prime divisor of  |G|  is greater than  k  and any other prime divisor of  G  (if there is
280: any) is greater than  k! . Feng, Sun and Xiang made use of the character theory of abelian groups, which is not applicable to non-abelian groups.
281: 
282: 
283: 
284: 
285: The purpose of this paper is to further develop the method of exterior algebra into this topic, and as an application we extend Theorem 1.3 to finite (non-abelian)  p -groups. The main result in this paper is the following.
286: 
287: 
705: [2]
706: 
707: B. Arsovski,
708: A proof of Snevily’s conjecture,
709: Israel J. Math., 182, 505–508, 2011.
710: 
711: 
712:       
713: 
714: [3]
715: 
716: S. Dasgupta, G. Károlyi, O. Serra and B. Szegedy,
717: Transversals of additive Latin squares,
723: [4]
724: 
725: T. Feng, Z.W. Sun and Q. Xiang,
726: Exterior algebra and two conjectures on finite abelian groups,
727: Israel J. Math., 182, 425–437, 2011.
728: 
729: 
730:       
731: 
732: [5]
733: 
734: W. D. Gao and D. J. Wang,
735: Additive Latin transversals,
768: [9]
769: 
770: Z.W. Sun,
771: On Snevily’s conjecture and restricted sumsets,
772: Journal of Combinatorial Theory, Series A, 103, 291–304, 2003.
773: 
774: 
775:     
776: 
777: 
778: 
779: 
780: 

## 375727 Girao, Kittipassorn, and Narayanan's long-cycle conjecture
229: 
230: 
231: 
232: The problem of finding long cycles distinct from a given Hamiltonian cycle has been studied extensively for more than 80 years; see, for example, [1, 10] for surveys. The famous longstanding Sheehan’s conjecture [17] states that, for each  k\geq 3 , every  k -regular Hamiltonian graph has at least two distinct Hamiltonian cycles. An early result in this direction is Smith’s theorem, which states that every  3 -regular Hamiltonian graph contains an even number of Hamiltonian cycles through any prescribed edge. Tutte [22] gave the first published proof of this theorem in 1946. Later, in 1978, Thomason [18] extended the Smith’s theorem to all  k -regular Hamiltonian graphs with odd  k  by means of a non-constructive argument, commonly referred to as the “lollipop” argument. Twenty years later, Thomassen [19, 20, 21] proved Sheehan’s conjecture for all  k\geq 300  by combining the arguments of Thomason [18] with the Lovász local lemma [5]. In 2006, Haxell, Seamone, and Verstraëte [11] verified Sheehan’s conjecture for all  k\geq 23 . Thus, in view of Thomason’s result for odd  k , the only remaining cases are even values  4\leq k\leq 22 . Moreover, Petersen’s  2 -factor decomposition theorem [15] shows that it would suffice to establish the conjecture for  k=4 , since this would imply the conjecture for all even  k\geq 4 . For more results related to Sheehan’s conjecture, see [8, 9, 12, 13, 16, 24].
233: 
234: 
235: 
236: 
237: It is natural to ask whether the weaker condition  \delta(G)\geq 3  already forces a Hamiltonian graph to contain a second Hamiltonian cycle.
238: Unfortunately, Entringer and Swart [4] constructed a Hamiltonian graph in which every vertex has degree  3  or  4 , but the graph has a unique Hamiltonian cycle.
239: Further counterexamples can be found in [6, 8].
240: It is worth noting that all these counterexamples still contain a long cycle distinct from the Hamiltonian cycle. Recently, Girão, Kittipassorn, and Narayanan [7] posed the following conjecture.
241: 
242: 
243: 
244: Conjecture 1 (Girão, Kittipassorn, and Narayanan [7]).
245: 
246: 
247: 
248: Let  G  be a simple graph with  n  vertices and  \delta(G)\geq 3  containing a Hamiltonian cycle. Then there exists a constant  c>0  such that  G  contains another cycle of length at least  n-c .
249: 
250: 
251: 
252: 
253: 
254: Girão, Kittipassorn, and Narayanan [7] proved a polynomial-error version of this conjecture: there exists a constant  c>0  such that  G  contains another cycle of length at least  n-cn^{4/5} .
255: In this paper, we improve their bound as follows.
256: 
257: 
258: 
259: Theorem 1.
260: 
261: 
262: 
263: Let  G  be a simple graph with  n  vertices and  \delta(G)\geq 3  containing a Hamiltonian cycle. Then there exists a constant  c  such that  G  contains another cycle of length at least  n-cn^{2/3} .
267: 
268: 
269: At the end of this section, we introduce another interesting and challenging problem concerning the distribution of cycle lengths in Hamiltonian graphs.
270: At the 1999 conference “Paul Erdős and His Mathematics”, Jacobson and Lehel conjectured that, for every  k\geq 3 , every  k -regular Hamiltonian graph on  n  vertices contains cycles of at least  \Omega(n)  distinct lengths; in other words, the number of distinct cycle lengths should be linear in  n . The 3-regular graph with  n/6+O(1)  different cycle lengths can be seen in [2].
271: In 2016, Verstraëte [23] proposed the following stronger conjecture: every Hamiltonian graph  G  on  n  vertices with  \delta(G)\geq 3  contains cycles of at least  \Omega(n)  distinct lengths.
272: A major result toward these two conjectures was obtained by Bucić, Gishboliner, and Sudakov [2], who proved that every Hamiltonian graph  G  on  n  vertices with  \delta(G)\geq 3  contains cycles of at least  n^{1-o(1)}  distinct lengths.
273: They also asked whether, under the same assumptions,  G  must contain a cycle of length  n-c  for some constant  c>0 , and suggested that this problem may be useful for approaching the above two conjectures.
274: For more results and problems concerning the distribution of cycle lengths in Hamiltonian graphs, see [2, 14].
275: 
276: 
277: 
278: 
279: 2 Preliminaries
280: 
281: 
282: 
293: 
294: 
295: 
296: The following useful theorem is based on parity-based arguments and has been applied in the study of Sheehan’s conjecture; see, for example, [11, 19, 20, 21].
297: 
298: 
299: 
300: Theorem 2 (Thomassen [20]).
301: 
302: 
303: 
304: Let  H  be a graph with a Hamiltonian cycle  C  ( H  may contain some parallel edges).
305: If there exists a set  X\subseteq V(H)  such that  X  is independent in  C  and is a dominating set in the subgraph  H-E(C) ,
707: 
708: 
709: Remark.
710: Since we use a constructive method based on a poset result in Case 1 and a nonconstructive method in Case 2, the bound is best possible by using our methods. hence, new methods should be used to approach Conjecture 1.
711: 
712: 
713: 
714: 
715: Acknowledgements
716: 
717: 
718: 
719: 
729:       
730: 
731: [1]
732:  J.A. Bondy, Beautiful conjectures in graph theory, European Journal of Combinatorics, 37(2014), 4–23.
733: 
734: 
735:       
736: 
737: [2]
738:  M. Bucić, L. Gishboliner, and B. Sudakov, Cycles of many lengths in Hamiltonian graphs, Forum of mathematics,
739: sigma, Vol 10, Cambridge University Press, Cambridge, 2022, pp. e70.
740: 
741: 
829:       
830: 
831: [16]
832:  M. Šajna and A. Wagner, On Sheehan’s conjecture for graphs with symmetry, Journal of Graph Theory, 80(2015), 43–57.
833: 
834: 
835:       
836: 
837: [17]
838:  J. Sheehan, The multiplicity of Hamiltonian circuits in a graph, in Recent Advances in
839: Graph Theory (Proc. Second Czechoslovak Sympos., Prague, 1974), Academia, Prague,
840: 1975, 477–480.
841: 

## 375753 Faudree–Gyárfás–Schelp–Tuza strong clique index conjecture
161: 
162: 2 Proof of Theorem 
163: 
164: 3 Counterexamples to some conjectures on  h_{3}(\Delta) 
165: 
166: 
167: 3.1 Small counterexamples
168: 
169: 3.2 Infinite family of counterexamples
170: 
171: 
172: References
173: 
203: Abstract
204:     
205: 
206: For a graph  G  with line graph  L(G) ,  \chi(L(G)^{2})  and  \omega(L(G)^{2})  are called the strong chromatic index and strong clique index of  G , respectively. A well-known conjecture of Erdős and Nešetřil (1985) posits that  \chi(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2} . Related to that,
207: Faudree, Gyárfás, Schelp and Tuza (1990) conjectured that  \omega(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2} . We show that  \omega(L(G)^{2})\leq\frac{2607}{1987}\Delta(G)^{2}<\frac{21}{16}\Delta(G)^{2}  improving the upper bound  \frac{4}{3}\Delta(G)^{2}  of Faron and Postle. Indeed, we make progress towards a stronger conjecture of Faron and Postle in terms of Ore-degree.
208:     
209: 
210: For positive integers  \Delta  and  t , let  h_{t}(\Delta)  denote the smallest integer such that any graph  G  with size at least  h_{t}(\Delta)  and maximum degree  \Delta(G)\leq\Delta , contains two edges with distance at least  t . An old problem of Erdős and Nešetřil (1986) concerns estimating the quantity  h_{t}(\Delta)  and can be thought of as the edge-version of the degree-diameter problem. Chung, Gyárfás, Tuza and Trotter established the sharp inequality  h_{2}(\Delta)\leq\frac{5}{4}\Delta^{2}+1 . We disprove two conjectures of Cambie, Cames van Batenburg, Joannis de Verclos and Kang concerning the next open case  h_{3}(\Delta) .
211:   
212: 
213: 
214: 
215: 
216: Keywords: Strong clique index, Square of a line graph, Strong chromatic index, Degree-diameter problem, Projective plane
217: 
218: 
219: 
236: 
237: 
238: 
239: There is a vast literature on colorings of graph powers, particularly graph squares. We refer the reader to the excellent survey by Cranston [9]. A well-known conjecture in this area concerns the chromatic number of squares of line graphs, a.k.a. the strong chromatic index of  G . In the 1980s, Erdős and Nešetřil (see [16, 14]) proposed the following conjecture relating strong chromatic index and maximum degree of graphs.
240: 
241: 
242: 
243: Conjecture 1.1 (Erdős–Nešetřil [16, 14]).
244: 
245: 
246: 
247: For any graph  G ,
248: 
249: 
250: 
251: 
252:  \chi(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2}. 
257: 
258: 
259: 
260: Apparently, inspired by the difficulty of this conjecture, the following weaker conjecture was made by Faudree, Gyárfás, Schelp, and Tuza [15] concerning the strong clique index.
261: 
262: 
263: 
264: Conjecture 1.2 (Faudree–Gyárfás–Schelp–Tuza [15]).
265: 
266: 
267: 
268: For any graph  G ,
269: 
270: 
271: 
272: 
273:  \omega(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2}. 
278: 
279: 
280: 
281: Both of the above conjectures are tight for the blowup  C_{5}^{(t)}  of cycle  C_{5} , i.e., the graph obtained from  C_{5}  by replacing each vertex with an independent set of size  t  and replacing edges with complete bipartite graphs. One can check that  \Delta(C_{5}^{(t)})=2t  and  L(C_{5}^{(t)})^{2}  is a complete graph of order  5t^{2}=\frac{5}{4}\Delta(C_{5}^{(t)})^{2} .
282: 
283: 
284: 
285: 
286: Śleszyńska-Nowak [18] proved the general upper bound  \frac{3}{2}\Delta(G)^{2}  for  \omega(L(G)^{2})  which significantly improves on the trivial upper bound  2\Delta(G)^{2} . Soon after, Faron and Postle [13] established the following bound, which is the best-known general upper bound to date.
287: 
288: 
289: 
290: Theorem 1.3 ([13]).
304: 
305: 
306: 
307: For further partial progress on Conjecture 1.2, we refer the reader to [10, 11, 7, 6] and the survey [9].
308: 
309: 
310: 
311: 
312: We quickly summarize the approach of Faron and Postle [13]. They suggested that it is more helpful to work with the Ore-degree instead of the maximum degree. Recall that if  H  is a non-empty subgraph of  G , the Ore-degree of  H  in  G  is defined to be
313: 
314: 
315: 
316: 
318: 
319: 
320: 
321: Let  \sigma_{G}(H)=0  if  H  is an empty graph. They crucially identified the following stronger conjecture, which implies Conjecture 1.2.
322: 
323: 
324: 
325: Conjecture 1.4 ([13]).
326: 
327: 
328: 
329: Let  H  be a bipartite subgraph of  G  such that  E(H)  forms a clique in  L(G)^{2} . Then
330: 
331: 
332: 
333: 
334:  |E(H)|\leq\frac{1}{4}\ \sigma_{G}(H)^{2}. 
369: 
370: 
371: 
372: Clearly, if Conjecture 1.4 holds with  \beta=\frac{1}{4} , then the assumption in Theorem 1.5 holds with  \beta=\frac{1}{4}  for the subgraph  H  of  G  whose edges induce the largest clique in  L(G)^{2} , which in turn implies Conjecture 1.2. Faron and Postle observed that Conjecture 1.4 holds for  \beta=\frac{1}{3}  inductively using Theorem 1.5, thus establishing Theorem 1.3.
373: 
374: 
375: 
376: 
377: We make non-trivial progress towards Conjecture 1.4 and show the following.
378: 
379: 
380: 
381: Theorem 1.6.
382: 
383: 
384: 
385: Let  G  be a graph and let  H  be a bipartite subgraph of  G . If
386:  E(H)  is a clique in  L(G)^{2} , then
417: 
418: 
419: 
420: To compare these results with Theorem 1.5 and Conjecture 1.4, observe that  \frac{620}{1987}<\frac{5}{16}  and  \frac{2607}{1987}<\frac{21}{16} . There is room for minor optimization in our proofs, which we avoid to keep the presentation short and clean. We believe new ideas are needed to bring down the coefficient below  1.3  in Corollary 1.7. We prove Theorem 1.6 and Corollary 1.7 in Section 2.
421: 
422: 
423: 
424: 
425: 1.2 Degree-diameter problem for the edges
426: 
427: 
428: 
429: 
451: 
452: 
453: 
454: If  t=1 , then it is clear that  h_{1}(\Delta)=\Delta+1 . For  t=2 , Erdős and Nešetřil [12] and Bermond, Bond, Paoli and Peyrat [2] independently conjectured that  h_{2}(\Delta)\leq\frac{5}{4}\Delta^{2}+1 . This was later established by Chung, Gyárfás, Tuza and Trotter [8]. The open blow-ups of  C_{5}  give tight examples. Cambie, Cames van Batenburg, Joannis de Verclos and Kang [4], proved the following general upper bound for  \omega(L(G)^{t}) , which by (1.1) gives the best known upper bound on  h_{t}(\Delta)  for  t\geq 3 .
455: 
456: 
457: 
458: Theorem 1.8 ([4]).
459: 
460: 
461: 
462: For any graph  G , we have
463: 
472: 
473: 
474: 
475: In [4], the authors further proposed the following conjectures.
476: 
477: 
478: 
479: Conjecture 1.9 ([4]).
480: 
481: 
482: 
483:  h_{3}(\Delta)\leq\Delta^{3}-\Delta^{2}+\Delta+2 .
484: 
485: 
486: 
487: 
488: Conjecture 1.10 ([4]).
489: 
490: 
491: 
492: For  t\geq 3  and every
493:  \varepsilon>0 ,
494: 
495: 
496: 
497: 
505: 
506: 
507: 
508: In [4], Conjecture 1.9 was verified for  \Delta=3 . Here, we disprove both of these conjectures. We first show that the  4 -regular Odd graph  O_{4}  and the  15 -regular truncated Witt graph  W  are counterexamples to Conjecture 1.9. Then, using projective planes  \PG(2,q) , we construct an infinite family of graphs  G[H,q]  (see Lemma 3.3). Taking  H  to be  O_{4}  or  W  and letting  q\to\infty  disproves Conjecture 1.10 when  t=3  and Conjecture 1.9 for all sufficiently large  \Delta . Indeed, we show the following.
509: 
510: 
511: 
512: Theorem 1.11.
513: 
514: 
515: 
516: We have
517: 
535: 
536: 
537: 
538: We prove Theorem 1.11 in Section 3. We remark here that Conjecture 1.10 remains undecided for  t\geq 4 . We propose the following problem for  t=3 .
539: 
540: 
541: 
542: Problem 1.12.
543: 
544: 
545: 
546: May it be that for all sufficiently large  \Delta , we have  h_{3}(\Delta)\leq\frac{253}{225}\Delta^{3}  ?
547: 
996: 
997: 
998: 
999: 3 Counterexamples to some conjectures on  h_{3}(\Delta) 
1000: 
1001: 
1002: 
1003: 3.1 Small counterexamples
1004: 
1005: 
1006: 
1007: 
1008: Let  O_{4}  be the Odd graph11
1070: 
1071: 
1072: 
1073: Thus, Conjecture 1.9 is false for  \Delta=4 .
1074: 
1075: 
1076: 
1077: 
1078: Now, consider the Steiner system  S(5,8,24) , i.e., this is the Steiner system with a point set  \Omega  of  24  elements, a collection  \mathcal{O}  of  8 -subsets of  \Omega  called octads such that any  5 -subset of  \Omega  is contained in exactly one octad in  \mathcal{O} . The (large) Witt graph22
1079:               2
1080:               
1081:               
1082:               
1202: 
1203: 
1204: 
1205: Therefore,  W  is a counterexample to Conjecture 1.9 for  \Delta=15 .
1206: 
1207: 
1208: 
1209: 
1210: 3.2 Infinite family of counterexamples
1211: 
1212: 
1213: 
1214: 
1595: Cited by: §1.2,
1596: §1.2,
1597: §1.2,
1598: Conjecture 1.10,
1599: Theorem 1.8,
1600: Conjecture 1.9.
1601: 
1602: 
1603: [5]
1604: P. J. Cameron (1992)
1605: 
1606: Projective and polar spaces.
1607: 
1608: QMW Maths Notes, Vol. 13,  Queen Mary and Westfield College, School of Mathematical
1609: Sciences, London.
1730: Cited by: §1.1,
1731: §1.1,
1732: Theorem 1.3,
1733: Conjecture 1.4,
1734: Theorem 1.5.
1735: 
1736: 
1737: [14]
1738: R. J. Faudree, A. Gyárfás, R. H. Schelp, and Zs. Tuza (1989)
1739: 
1740: Induced matchings in bipartite graphs.
1741: 
1742: Discrete Math. 78 (1-2), pp. 83–87.
1746: MathReview (László Pyber)
1747: 
1748: Cited by: §1.1,
1749: Conjecture 1.1.
1750: 
1751: 
1752: [15]
1753: R. J. Faudree, R. H. Schelp, A. Gyárfás, and Zs. Tuza (1990)
1754: 
1755: The strong chromatic index of graphs.
1756: 
1757: Vol. 29, pp. 205–211.
1758: 
1762: MathReview Entry
1763: 
1764: Cited by: §1.1,
1765: Conjecture 1.2.
1766: 
1767: 
1768: [16]
1769: G. Halász and V. T. Sós (Eds.) (1989)
1770: 
1771: Irregularities of partitions.
1772: 
1773: Algorithms and Combinatorics: Study and Research Texts, Vol. 8,  Springer-Verlag, Berlin.
1774: 
1779: MathReview Entry
1780: 
1781: Cited by: §1.1,
1782: Conjecture 1.1.
1783: 
1784: 
1785: [17]
1786: M. Miller and J. Širáň (2005)
1787: 
1788: Moore graphs and beyond: a survey of the degree/diameter problem.
1789: 
1790: Electron. J. Combin. DS14, pp. 61.
1791: 

## 375755 Cambie–Cames van Batenburg–Joannis de Verclos–Kang conjecture for $h_3(\Delta)$
161: 
162: 2 Proof of Theorem 
163: 
164: 3 Counterexamples to some conjectures on  h_{3}(\Delta) 
165: 
166: 
167: 3.1 Small counterexamples
168: 
169: 3.2 Infinite family of counterexamples
170: 
171: 
172: References
173: 
203: Abstract
204:     
205: 
206: For a graph  G  with line graph  L(G) ,  \chi(L(G)^{2})  and  \omega(L(G)^{2})  are called the strong chromatic index and strong clique index of  G , respectively. A well-known conjecture of Erdős and Nešetřil (1985) posits that  \chi(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2} . Related to that,
207: Faudree, Gyárfás, Schelp and Tuza (1990) conjectured that  \omega(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2} . We show that  \omega(L(G)^{2})\leq\frac{2607}{1987}\Delta(G)^{2}<\frac{21}{16}\Delta(G)^{2}  improving the upper bound  \frac{4}{3}\Delta(G)^{2}  of Faron and Postle. Indeed, we make progress towards a stronger conjecture of Faron and Postle in terms of Ore-degree.
208:     
209: 
210: For positive integers  \Delta  and  t , let  h_{t}(\Delta)  denote the smallest integer such that any graph  G  with size at least  h_{t}(\Delta)  and maximum degree  \Delta(G)\leq\Delta , contains two edges with distance at least  t . An old problem of Erdős and Nešetřil (1986) concerns estimating the quantity  h_{t}(\Delta)  and can be thought of as the edge-version of the degree-diameter problem. Chung, Gyárfás, Tuza and Trotter established the sharp inequality  h_{2}(\Delta)\leq\frac{5}{4}\Delta^{2}+1 . We disprove two conjectures of Cambie, Cames van Batenburg, Joannis de Verclos and Kang concerning the next open case  h_{3}(\Delta) .
211:   
212: 
213: 
214: 
215: 
216: Keywords: Strong clique index, Square of a line graph, Strong chromatic index, Degree-diameter problem, Projective plane
217: 
218: 
219: 
236: 
237: 
238: 
239: There is a vast literature on colorings of graph powers, particularly graph squares. We refer the reader to the excellent survey by Cranston [9]. A well-known conjecture in this area concerns the chromatic number of squares of line graphs, a.k.a. the strong chromatic index of  G . In the 1980s, Erdős and Nešetřil (see [16, 14]) proposed the following conjecture relating strong chromatic index and maximum degree of graphs.
240: 
241: 
242: 
243: Conjecture 1.1 (Erdős–Nešetřil [16, 14]).
244: 
245: 
246: 
247: For any graph  G ,
248: 
249: 
250: 
251: 
252:  \chi(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2}. 
257: 
258: 
259: 
260: Apparently, inspired by the difficulty of this conjecture, the following weaker conjecture was made by Faudree, Gyárfás, Schelp, and Tuza [15] concerning the strong clique index.
261: 
262: 
263: 
264: Conjecture 1.2 (Faudree–Gyárfás–Schelp–Tuza [15]).
265: 
266: 
267: 
268: For any graph  G ,
269: 
270: 
271: 
272: 
273:  \omega(L(G)^{2})\leq\frac{5}{4}\Delta(G)^{2}. 
278: 
279: 
280: 
281: Both of the above conjectures are tight for the blowup  C_{5}^{(t)}  of cycle  C_{5} , i.e., the graph obtained from  C_{5}  by replacing each vertex with an independent set of size  t  and replacing edges with complete bipartite graphs. One can check that  \Delta(C_{5}^{(t)})=2t  and  L(C_{5}^{(t)})^{2}  is a complete graph of order  5t^{2}=\frac{5}{4}\Delta(C_{5}^{(t)})^{2} .
282: 
283: 
284: 
285: 
286: Śleszyńska-Nowak [18] proved the general upper bound  \frac{3}{2}\Delta(G)^{2}  for  \omega(L(G)^{2})  which significantly improves on the trivial upper bound  2\Delta(G)^{2} . Soon after, Faron and Postle [13] established the following bound, which is the best-known general upper bound to date.
287: 
288: 
289: 
290: Theorem 1.3 ([13]).
304: 
305: 
306: 
307: For further partial progress on Conjecture 1.2, we refer the reader to [10, 11, 7, 6] and the survey [9].
308: 
309: 
310: 
311: 
312: We quickly summarize the approach of Faron and Postle [13]. They suggested that it is more helpful to work with the Ore-degree instead of the maximum degree. Recall that if  H  is a non-empty subgraph of  G , the Ore-degree of  H  in  G  is defined to be
313: 
314: 
315: 
316: 
318: 
319: 
320: 
321: Let  \sigma_{G}(H)=0  if  H  is an empty graph. They crucially identified the following stronger conjecture, which implies Conjecture 1.2.
322: 
323: 
324: 
325: Conjecture 1.4 ([13]).
326: 
327: 
328: 
329: Let  H  be a bipartite subgraph of  G  such that  E(H)  forms a clique in  L(G)^{2} . Then
330: 
331: 
332: 
333: 
334:  |E(H)|\leq\frac{1}{4}\ \sigma_{G}(H)^{2}. 
369: 
370: 
371: 
372: Clearly, if Conjecture 1.4 holds with  \beta=\frac{1}{4} , then the assumption in Theorem 1.5 holds with  \beta=\frac{1}{4}  for the subgraph  H  of  G  whose edges induce the largest clique in  L(G)^{2} , which in turn implies Conjecture 1.2. Faron and Postle observed that Conjecture 1.4 holds for  \beta=\frac{1}{3}  inductively using Theorem 1.5, thus establishing Theorem 1.3.
373: 
374: 
375: 
376: 
377: We make non-trivial progress towards Conjecture 1.4 and show the following.
378: 
379: 
380: 
381: Theorem 1.6.
382: 
383: 
384: 
385: Let  G  be a graph and let  H  be a bipartite subgraph of  G . If
386:  E(H)  is a clique in  L(G)^{2} , then
417: 
418: 
419: 
420: To compare these results with Theorem 1.5 and Conjecture 1.4, observe that  \frac{620}{1987}<\frac{5}{16}  and  \frac{2607}{1987}<\frac{21}{16} . There is room for minor optimization in our proofs, which we avoid to keep the presentation short and clean. We believe new ideas are needed to bring down the coefficient below  1.3  in Corollary 1.7. We prove Theorem 1.6 and Corollary 1.7 in Section 2.
421: 
422: 
423: 
424: 
425: 1.2 Degree-diameter problem for the edges
426: 
427: 
428: 
429: 
451: 
452: 
453: 
454: If  t=1 , then it is clear that  h_{1}(\Delta)=\Delta+1 . For  t=2 , Erdős and Nešetřil [12] and Bermond, Bond, Paoli and Peyrat [2] independently conjectured that  h_{2}(\Delta)\leq\frac{5}{4}\Delta^{2}+1 . This was later established by Chung, Gyárfás, Tuza and Trotter [8]. The open blow-ups of  C_{5}  give tight examples. Cambie, Cames van Batenburg, Joannis de Verclos and Kang [4], proved the following general upper bound for  \omega(L(G)^{t}) , which by (1.1) gives the best known upper bound on  h_{t}(\Delta)  for  t\geq 3 .
455: 
456: 
457: 
458: Theorem 1.8 ([4]).
459: 
460: 
461: 
462: For any graph  G , we have
463: 
472: 
473: 
474: 
475: In [4], the authors further proposed the following conjectures.
476: 
477: 
478: 
479: Conjecture 1.9 ([4]).
480: 
481: 
482: 
483:  h_{3}(\Delta)\leq\Delta^{3}-\Delta^{2}+\Delta+2 .
484: 
485: 
486: 
487: 
488: Conjecture 1.10 ([4]).
489: 
490: 
491: 
492: For  t\geq 3  and every
493:  \varepsilon>0 ,
494: 
495: 
496: 
497: 
505: 
506: 
507: 
508: In [4], Conjecture 1.9 was verified for  \Delta=3 . Here, we disprove both of these conjectures. We first show that the  4 -regular Odd graph  O_{4}  and the  15 -regular truncated Witt graph  W  are counterexamples to Conjecture 1.9. Then, using projective planes  \PG(2,q) , we construct an infinite family of graphs  G[H,q]  (see Lemma 3.3). Taking  H  to be  O_{4}  or  W  and letting  q\to\infty  disproves Conjecture 1.10 when  t=3  and Conjecture 1.9 for all sufficiently large  \Delta . Indeed, we show the following.
509: 
510: 
511: 
512: Theorem 1.11.
513: 
514: 
515: 
516: We have
517: 
535: 
536: 
537: 
538: We prove Theorem 1.11 in Section 3. We remark here that Conjecture 1.10 remains undecided for  t\geq 4 . We propose the following problem for  t=3 .
539: 
540: 
541: 
542: Problem 1.12.
543: 
544: 
545: 
546: May it be that for all sufficiently large  \Delta , we have  h_{3}(\Delta)\leq\frac{253}{225}\Delta^{3}  ?
547: 
996: 
997: 
998: 
999: 3 Counterexamples to some conjectures on  h_{3}(\Delta) 
1000: 
1001: 
1002: 
1003: 3.1 Small counterexamples
1004: 
1005: 
1006: 
1007: 
1008: Let  O_{4}  be the Odd graph11
1070: 
1071: 
1072: 
1073: Thus, Conjecture 1.9 is false for  \Delta=4 .
1074: 
1075: 
1076: 
1077: 
1078: Now, consider the Steiner system  S(5,8,24) , i.e., this is the Steiner system with a point set  \Omega  of  24  elements, a collection  \mathcal{O}  of  8 -subsets of  \Omega  called octads such that any  5 -subset of  \Omega  is contained in exactly one octad in  \mathcal{O} . The (large) Witt graph22
1079:               2
1080:               
1081:               
1082:               
1202: 
1203: 
1204: 
1205: Therefore,  W  is a counterexample to Conjecture 1.9 for  \Delta=15 .
1206: 
1207: 
1208: 
1209: 
1210: 3.2 Infinite family of counterexamples
1211: 
1212: 
1213: 
1214: 
1595: Cited by: §1.2,
1596: §1.2,
1597: §1.2,
1598: Conjecture 1.10,
1599: Theorem 1.8,
1600: Conjecture 1.9.
1601: 
1602: 
1603: [5]
1604: P. J. Cameron (1992)
1605: 
1606: Projective and polar spaces.
1607: 
1608: QMW Maths Notes, Vol. 13,  Queen Mary and Westfield College, School of Mathematical
1609: Sciences, London.
1730: Cited by: §1.1,
1731: §1.1,
1732: Theorem 1.3,
1733: Conjecture 1.4,
1734: Theorem 1.5.
1735: 
1736: 
1737: [14]
1738: R. J. Faudree, A. Gyárfás, R. H. Schelp, and Zs. Tuza (1989)
1739: 
1740: Induced matchings in bipartite graphs.
1741: 
1742: Discrete Math. 78 (1-2), pp. 83–87.
1746: MathReview (László Pyber)
1747: 
1748: Cited by: §1.1,
1749: Conjecture 1.1.
1750: 
1751: 
1752: [15]
1753: R. J. Faudree, R. H. Schelp, A. Gyárfás, and Zs. Tuza (1990)
1754: 
1755: The strong chromatic index of graphs.
1756: 
1757: Vol. 29, pp. 205–211.
1758: 
1762: MathReview Entry
1763: 
1764: Cited by: §1.1,
1765: Conjecture 1.2.
1766: 
1767: 
1768: [16]
1769: G. Halász and V. T. Sós (Eds.) (1989)
1770: 
1771: Irregularities of partitions.
1772: 
1773: Algorithms and Combinatorics: Study and Research Texts, Vol. 8,  Springer-Verlag, Berlin.
1774: 
1779: MathReview Entry
1780: 
1781: Cited by: §1.1,
1782: Conjecture 1.1.
1783: 
1784: 
1785: [17]
1786: M. Miller and J. Širáň (2005)
1787: 
1788: Moore graphs and beyond: a survey of the degree/diameter problem.
1789: 
1790: Electron. J. Combin. DS14, pp. 61.
1791: 

## 375817 The $q,t$-dihedral sieving conjecture for cluster parking functions
251: Abstract
252:     
253: 
254: In a previous work, we defined the complex of cluster parking functions. On one side, they encode the type-refined enumeration of faces of the cluster complex, and on the other side, they have a reduced homology which is isomorphic to (ungraded) diagonal coinvariants. The goal of this work is to take into account the underlying dihedral symmetry. We thus have a product of a dihedral group and a symmetric group (there is a precise conjecture in the case of other finite Coxeter groups, but we focus on symmetric groups because of technicalities about diagonal coinvariants beyond this case). Under the action of the product group, the reduced homology of cluster parking functions is conjecturally isomorphic to diagonal coinvariants up to tensoring by a sign character of the dihedral group. This isomorphism can be reformulated as a dihedral sieving phenomenon. The main technical contribution is the definition of the dihedral automorphism group of cluster parking functions, and we discuss various features of the reduced homology character and its conjectural connection with diagonal coinvariants.
255:   
256: 
257: 
258: 
259: 1 Introduction
260: 
261: 
262: 
263: 1.1 Parabolic types and dihedral symmetry in the generalized cluster complex
446: 
447: 
448: 
449: Conjecture 1.3 ( \Lambda\Sigma=\Delta ).
450: 
451: 
452: 
453: We have  \Lambda\Sigma=\Delta , where:
454: 
455: 
456: • 
457: 
458: 
488: 
489: 
490: 
491: Conjecture 1.4 ( q,t -dihedral sieving).
492: 
493: 
494: 
495: For any  \mathbf{F}  in  \dih_{n+2}  and  \sigma\in\mathfrak{S}_{n} , we have:
496: 
497: 
498: 
499: 
500:  (\Lambda\Sigma)(\mathbf{F},\sigma)=\varDelta(\sigma)\Big|_{\begin{subarray}{c}q=\lambda_{1}\\
508: 
509: 
510: 
511: This can be considered as a (homological) dihedral sieving phenomenon for cluster parking functions. The various facets of this conjecture (including the general case beyond type  A ) will be discussed in Section 8. Understanding this character identity leads to very different considerations, depending on wether  \mathbf{F}  is a rotation or a reflection:
512: 
513: 
514: • 
515: 
516: 
517: 
518: When we restrict the action to the rotation subgroup  \rot_{n+2}\subset\dih_{n+2} , the evaluation of  \Delta  gives explicit values (this follows from the fact that  \varDelta  dramatically simplifies at  t=q^{-1} ).
519: We get a variant of parking spaces considered by Armstrong, Reiner, and Rhoades [1], with a cyclic group of order  n+2  rather than  n . We call them cluster parking spaces. It is not too difficult to generalize the conjecture to all finite Coxeter groups, and it has been proved in types  A  and  B  (see Pouillart [22]).
520: 
521: 
522: • 
523: 
524: 
525: 
526: The case of reflections of  \dih_{n+2}  is connected with [6], where we initiate the idea of plugging  t=-1  in the context of  q,t -combinatorics by building on the identity  \varDelta(e)\big|_{q=-t=1}=E_{n}  ( e\in\mathfrak{S}_{n}  is the unit and  E_{n}  is the  n th Euler number. In general,  (\Lambda\Sigma)(\mathbf{S},1_{W})  is the Springer number of  W , which is  E_{n}  when  W=\mathfrak{S}_{n} ). This is the part of the conjecture that really relies on  q,t -symmetric functions, but the lack of a well-developed  q,t -combinatorics beyond the symmetric group makes it difficult to investigate this beyond symmetric groups.
527: 
528: 
529: 
530: 
531: 
532: 
533: As the main technical contribution of the present work is about automorphisms of  \CPF^{(m)}  in the case of finite Coxeter groups, we hope that the natural analog of our conjectures (using Gordon’s ring [15] in place of diagonal coinvariants, or the corresponding modules of the rational Cherednik algebra) also holds. One should also investigate higher diagonal coinvariants defined by Garsia and Haiman [14, Section 5] to deal with the general case  m\geq 1 .
534: 
535: 
536: 
537: 
538: 1.4 Organization
539: 
540: 
541: 
542: 
543: We review the generalized cluster complex in Section 2, its dihedral automorphism group in Section 3, and parabolic types of faces in Section 4 (in particular, the latter contains the proof of Theorem 1.1). We review (noncrossing) parking functions in Section 5, and cluster parking functions in Section 6. We also define the dihedral action on them in Section 6, and the proof of Theorem 1.2 is completed in Section 7. Conjectures 1.3 and 1.4 are discussed in Section 8, with a perspective in Section 9.
544: 
545: 
546: 
547: 
548: 1.5 Acknowledgements
549: 
550: 
551: 
552: 
1264: 
1265: 
1266: 
1267: Let  \mu=e^{2i\pi/h}  be a primitive  h th root of  1 . It was conjectured in [1] that the character of  \PF  is:
1268: 
1269: 
1270: 
1271: 
1272:  (c^{k},w)\mapsto\lim_{q\to\mu^{k}}\frac{\det(1_W - q^{h+1} w)}{\det(1_W -q w)}=(h+1)^{\dim\ker(1_{W}-\mu^{k}w)}. 
1273: 
1274: 
1275: 
1276: Moreover, this has been checked in most cases (ibidem). To our knowledge, it is still open only in types  E_{7}  and  E_{8} .
2073: 
2074: 
2075: 
2076: We begin this section by discussing signs. In particular, we define the character  \Sigma  and thus complete the statement of the conjectures in the introduction.
2077: 
2078: 
2079: 
2080: 
2081: A general principle that guides us in understanding signs is the following. By [2], evaluating of the reduced homology character gives the reduced Euler characteristic of a fixed-point subposet:
2082: 
2083: 
2084: 
2085: 
2092: 
2093: 
2094: 
2095: In general,  \CPF_{n}^{(\mathbf{F},\sigma)}  is not a subcomplex: a face can be a fixed point while its vertices are permuted in a nontrivial way. Still, this subposet is expected to be the face poset of a Cohen-Macaulay simplicial complex, so that the sign of its reduced Euler characteristic is given by the parity of its dimension. We call them fixed-point subcomplexes (and conjecture the property of being the face poset of a Cohen-Macaulay simplicial complex).
2096: 
2097: 
2098: 
2099: Definition 8.1.
2100: 
2101: 
2102: 
2103: The character  \Sigma  of  \dih_{n+2}  is defined on the generators by:
2104: 
2147: 
2148: 
2149: 
2150: has the same sign as  (-1)^{\ell_{e}(\sigma)+\frac{n-\ell_{o}(\sigma)}{2}} . In particular, it is positive when  \sigma  is the identity (indeed,  \varDelta(e)\big|_{q=-t=1}=E_{n} , the  n th Euler number). It’s tempting to think about what should be the Coxeter theoretic analog (for example,  \ell_{e}(\sigma)  is the multiplicity of  -1  as an eigenvalue in the geometric representation) but we have no available data to test any conjecture in this direction.
2151: 
2152: 
2153: 
2154: 
2155: 
2156: 8.2 Rotations
2157: 
2158: 
2159: 
2383: 
2384: 
2385: 
2386: The previous proposition and previous lemma give a reformulation of our conjecture in the case of rotations.
2387: 
2388: 
2389: 
2390: Conjecture 8.6 ( \Lambda\Sigma=\Delta , the case of rotations).
2391: 
2392: 
2393: 
2394: Let  \mathbf{F}  be a rotation (a power of  \mathbf{R} ), and  \mu  a root of  1  with the same order as  \mathbf{F} . We have:
2395: 
2396: 
2397: 
2398: 
2399:  \Lambda(\mathbf{F},w)=(-1)^{n}\cdot(-h-1)^{\dim\ker(w-\mu 1_{W})}. 
2408: 
2409: 
2410: 
2411: The “Fuß” analog of the previous conjecture is straightforward: take  \CPF^{(m)}  and  -mh-1  in place of  \CPF  and  -h-1 .
2412: 
2413: 
2414: 
2415: 
2416: 
2417: Since we have a simple explicit formula in the right-hand side, it is easy to test this case of the conjecture and one can imagine a case-by-case proof based on the finite type classification.
2418: 
2419: 
2420: 
2421: 
2422: A confirmation of this conjecture would establish the existence of cluster parking spaces as an analog of the noncrossing parking spaces reviewed in Section 5. An important difference is that the cyclic group has order  h+2  (or  mh+2  in the Fuß case). In the perspective of [1], some natural questions are:
2423: 
2424: 
2425: • 
2426: 
2427: 
2428: 
2429: Besides clusters, does there exist other combinatorial construction of parking spaces having the same character ? (In the same way as noncrossing parking spaces are related with nonnesting parking spaces, for example.)
2430: 
2431: 
2433: 
2434: 
2435: 
2436: Is there an algebraic parking space, defined via homogeneous system of parameters, having the same character as the cluster parking spaces ? This could lead to analogs of the strong/intermediate conjectures from [1] for cluster parking spaces. (About this, see Appendix A.)
2437: 
2438: 
2439: 
2440: 
2441: 
2442: 
2443: While these are quite speculative, the computations that lead to Conjecture 8.6 might be a clue that it’s worth investigating these directions.
2444: 
2445: 
2446: 
2447: Remark 8.8.
2448: 
2449: 
2450: 
2451: To be precise, Conjecture 8.6 is only an analog of Conjecture 1.4 ( q,t -dihedral sieving, i.e., cyclic sieving in the present case). To have an exact analog of Conjecture 1.3 ( \Lambda\Sigma=\Delta ), one needs to check that the operator  \mathtt{R}  from (2) is well-defined in the context of the rational Cherednik algebra and it simple module of dimension  (h+1)^{n}  (which gives the appropriate generalization of diagonal coinvariants), so that there is indeed a character  \Delta  of  \rot_{h+2}\times W  beyond type  A_{n} . We will not do this here.
2452: 
2453: 
2454: 
2455: 
2456: 
2457: 8.3 Reflections
2458: 
2459: 
2460: 
2590: 
2591: 
2592: 
2593: Conjecture 8.10 (A very particular case of the  \Lambda\Sigma=\Delta  conjecture).
2594: 
2595: 
2596: 
2597: The bigraded character  \varDelta  of Gordon’s ring  R_{W}  is such that
2598: 
2599: 
2600: 
2601: 
2602:  \varDelta(1_{W})\big|_{t=-q=1}=S_{W}. 
2612: 
2613: 
2614: 
2615: The previous conjecture has been confirmed in dihedral types by direct examination (in fact, we can use explicit computations of Boij and Geramita [3] to check the full conjecture  \Lambda\Sigma=\Delta ). It has been checked for  B_{3}  using the operator conjecture from [18]. More precisely, we obtain
2616: 
2617: 
2618: 
2619: 
2620:  \displaystyle\varDelta(1_{B_{3}})=\, 
2621:  \displaystyle q^{9}+q^{8}t+q^{7}t^{2}+q^{6}t^{3}+q^{5}t^{4}+q^{4}t^{5}+q^{3}t^{6}+q^{2}t^{7}+qt^{8}+t^{9}+3q^{8}+3q^{7}t+3q^{6}t^{2}+ 
2622: 
2623: 
2624: 
2651: 
2652: 
2653: 
2654: which is indeed the Springer number of type  B_{3} . As for  B_{4} , the operator conjecture almost holds: the recipe gives a space of dimension  9^{4}-2  instead of the expected  9^{4} . The bigraded Hilbert series of this space is a polynomial with 153 terms, that we don’t reproduce here. It turns out that the only missing term to get  \varDelta(1_{B_{4}})  is  2t^{4}q^{4} , which has been confirmed by computer calculations (using the definition in Appendix B, and an AI-generated Sagemath program). This allowed us to get
2655: 
2656: 
2657: 
2658: 
2659:  \varDelta(1_{B_{4}})\big|_{t=-1,\,q=1}=57 
2660: 
2661: 
2662: 
2663: which is indeed the Springer number of type  B_{4} . Similar computations give
2722: 
2723: 
2724: 
2725: Our main technical contribution here is the definition of the dihedral automorphism group of cluster parking functions. We hope that our conjectures will lead to interesting developments, and finish this article by a few remarks that we hope to be relevant in the sequel.
2726: 
2727: 
2728: • 
2729: 
2730: 
2731: 
2732: In the case of the symmetric groups (and  m=1 ), it is likely that there exists an explicit generating function for the collection of numbers  \Lambda(\mathbf{S},\sigma)  (with  n\geq 0 ,  \sigma\in\mathfrak{S}_{n} ). It should be a symmetric functions given in terms of the homogeneous symmetric functions  h_{\lambda} . It is then reasonable to expect that symmetric functions theory will complete the proof of  \Lambda\Sigma=\Delta .
2733: 
2734: 
2759: 
2760: 
2761: 
2762: so that  \langle\mathtt{R},\mathtt{S}^{\prime}\rangle\simeq\mathbb{Z}_{h+2}\times\mathbb{Z}_{2} . Now,  \Delta  becomes a character of  \mathbb{Z}_{h+2}\times\mathbb{Z}_{2}\times\mathfrak{S}_{n} . But the relation  \Lambda\Sigma=\Delta  still makes sense, because the characters of  \mathbb{Z}_{h+2}\rtimes\mathbb{Z}_{2}  embed in those of  \mathbb{Z}_{h+2}\times\mathbb{Z}_{2}  (upon identifying the underlying sets of the two groups). This might be the correct path to state Conjecture 1.3 for finite Coxeter groups (where  \Delta  should be defined via a module of the rational Cherednik algebra).
2763: 
2764: 
2765: 
2766: 
2767: 
2768: 
2769: References
2770: 
2771: 
2810: [5]
2811: 
2812: Erik Carlsson, Anton Mellit:
2813: A proof of the shuffle conjecture.
2814: Journal of the American Mathematical Society, 31(3):661–697.
2815: 
2816: 
2817:       
2818: 
2819: [6]
2820: 
2821: Sylvie Corteel, Matthieu Josuat-Vergès, Anna Vanden Wyngaerd:
2822: Combinatorics of the Delta conjecture at  q=-1 .
2823: Algebr. Comb. 7, No. 1, 17–35 (2024).
2824: 
2825: 
2826:       
2827: 
2828: [7]
2829: 
2830: Bérénice Delcroix-Oger, Matthieu Josuat-Vergès, Lucas Randazzo:
2831: Some properties of the parking function poset.
2918: [17]
2919: 
2920: James Haglund, Sergel, Emily:
2921: Schedules and the delta conjecture.
2922: Ann. Comb. 25(1), 1–31 (2021).
2923: 
2924: 
2925:       
2926: 
2927: [18]
2928: 
2929: Mark D. Haiman:
2930: Conjectures on the quotient ring by diagonal invariants.
2931: J. Algebr. Comb. 3(1), 17–76 (1994).
2932: 
2933: 
2934:       
2935: 
2936: [19]
2937: 
2938: Mark Haiman:
2939: Vanishing theorems and character formulas for the Hilbert scheme of points in the plane.

## 375866 Reed's chromatic bound conjecture
235: We prove that, for every fixed integer  b\in\mathbb{N} , every digraph  D  with  \tilde{\Delta}(D)=\Delta  being sufficiently large with respect to  b  either contains a biclique whose size exceeds  \Delta-2b  or has dichromatic number at most  \Delta-b .
236:     
237: 
238: This extends a classical result of Reed to the directed setting and supports a conjecture of the present authors.
239: Furthermore, the theorem is tight, as for all integers  b  and  \Delta\geqslant 3b  there exists a digraph  D  with  \tilde{\Delta}(D)=\Delta , dichromatic number  \Delta-b+1 , and whose largest biclique has size  \Delta-2b+1 .
240:   
241: 
242: 
243: 
244: 
245: 
246: 1. Introduction
247: 
260: 
261: 
262: unless  \Delta(G)=2  and  G  contains an odd cycle.
263: Pushing this direction further, in 1977 Borodin and Kostochka [8] posed a celebrated conjecture stating that
264: 
265: 
266: 
267: 
268:  \chi(G)\leqslant\max\{\Delta(G)-1,\omega(G)\} 
269: 
270: 
271: 
272: holds for every graph  G  with  \Delta(G)\geqslant 9 .
273: Even though the conjecture is still open in general, Reed [32] proved that it holds for graphs  G  with  \Delta(G)\geqslant 10^{10} .
274: Moreover, in 1998 Reed [31] conjectured that these inequalities are just the tip of the iceberg, and posed the following famous conjecture.
275: 
276: 
277: 
278: Conjecture 1 ([31]).
279: 
280: 
281: 
282: Every graph  G  satisfies  \chi(G)\leqslant\lceil\frac{1}{2}(\Delta(G)+1+\omega(G))\rceil .
283: 
284: 
285: 
286: 
287: 
288: As supporting evidence for the conjecture, in the same paper Reed proved that, for every graph  G ,
289:  \chi(G)\leqslant\tfrac{1}{2}\big(\Delta(G)+1+\omega(G)\big) 
290: holds whenever  \Delta(G)  is sufficiently large and  \omega(G)  is sufficiently close to  \Delta(G) ; formally when  \Delta(G)\geqslant\Delta_{0}  and  \omega(G)\geqslant(1-\varepsilon)\Delta(G)  for some absolute constants  \Delta_{0}\in\mathbb{N}  and  \varepsilon\in(0,1) .
291: This has the following two main consequences.
292: 
293: 
294: 
295: Corollary 2 ([31]).
296: 
297: 
318: 
319: 
320: 
321: Observe that Conjecture 1 is precisely the statement of Corollary 2 for  \varepsilon=1/2 . This gave rise to a line of research aimed at determining the largest value of  \varepsilon>0  for which Corollary 2 holds.
322: The current best result is due to Hurley, Joannis de Verclos, and Kang [18], who proved that it holds for  \varepsilon=0.119  for graphs with sufficiently large maximum degree. This improves on earlier results obtained by Bonamy, Perrett, and Postle [7] and by Delcourt and Postle [10].
323: 
324: 
325: 
326: 
327: Let us briefly discuss the sharpness of Corollary 3 and its connection to Conjecture 1.
328: First, observe that the threshold  \Delta_{b}  in Corollary 3 must depend on  b . Indeed, for every integer  b\in\mathbb{N} , there exists a graph  G  with  \Delta(G)=6b+2 ,  \omega(G)=4b+2 , and  \chi(G)=5b+3 . One example is the graph obtained from a  5 -cycle by blowing up each vertex into a clique of size  2b+1 .
329: In particular, such a graph does not satisfy the conclusion of Corollary 3, showing that  \Delta_{b}  must be at least  6b+3 .
330: 
331: 
332: 
333: 
334: However, the dependence of  \Delta_{b}  on  b  might not be necessary under the stronger hypothesis  \omega(G)\leqslant\Delta-2b-1 . Indeed, Conjecture 1 is easily seen to be equivalent to the following.
335: 
336: 
337: 
338: Conjecture 4.
339: 
340: 
341: 
342: For every  b\in\mathbb{Z}  and every graph  G , if  \omega(G)\leqslant\Delta-2b-1  then  \chi(G)\leqslant\Delta-b .
343: 
344: 
345: 
346: 
347: 
388: 
389: 
390: 
391: unless  D  is a very specific obstruction. This generalizes the aforementioned result of Reed [32], which itself supports the conjecture of Borodin and Kostochka [8]. Moreover, Kawarabayashi and Picasarri-Arrieta [22] recently posed the following conjecture, which, if true, implies both Conjecture 1 and an independent conjecture posed by Harutyunyan and Mohar [17].
392: 
393: 
394: 
395: Conjecture 5 ([22]).
396: 
397: 
398: 
399: Every digraph  D  satisfies  \vec{\chi}(D)\leqslant\lceil\tfrac{1}{2}(\tilde{\Delta}(D)+1+\overset{\text{\tiny$\bm{\leftrightarrow}$}}{\omega}(D))\rceil .
400: 
401: 
402: 
403: 
404: 
432: 
433: It follows from Theorem 6 that every digraph  D  with
434:  \overset{\text{\tiny$\bm{\leftrightarrow}$}}{\omega}(D)\leqslant\tilde{\Delta}(D)-\frac{1}{\varepsilon}(b+2) 
435: satisfies  \vec{\chi}(D)\leqslant\tilde{\Delta}(D)-b . In view of Corollary 3 and Conjectures 4 and 5, this condition is certainly not optimal. In the present paper, we prove the following sufficient condition for a digraph  D  to be  (\tilde{\Delta}(D)-b) -colorable, which generalizes Corollary 3 to the directed setting and supports Conjecture 5.
436: 
437: 
438: 
439: Theorem 7.
440: 
441: 
442: 
443: For every  b\in\mathbb{Z} , there exists  \Delta_{b}\in\mathbb{N}  such that every digraph  D  with  \tilde{\Delta}(D)\geqslant\Delta_{b}  and  \overset{\text{\tiny$\bm{\leftrightarrow}$}}{\omega}(D)\leqslant\tilde{\Delta}(D)-2b  satisfies  \vec{\chi}(D)\leqslant\tilde{\Delta}(D)-b .
444: 
520: 
521: 
522: 
523: Bounding the dichromatic number of oriented graphs in terms of their maximum degree is at the heart of the following famous conjecture due to Erdős and Neumann-Lara (see [12]), which can be seen as a directed version of Johansson’s bound for triangle-free graphs [20].
524: 
525: 
526: 
527: Conjecture 10 ([12]).
528: 
529: 
530: 
531: Every oriented graph  D  satisfies  \vec{\chi}(D)=O(\Delta/\log\Delta) , where  \Delta  is the maximum degree of the underlying graph of  D .
532: 
533: 
534: 
535: 
536: 
537: The analogous conjecture in terms of  \tilde{\Delta}  has been posed by McDiarmid and Mohar, see [17].
538: 
539: 
540: 
541: 
542: 2. Technical Overview
543: 
544: 
545: 
546: 
3914: [10]
3915: M. Delcourt and L. Postle (2017)
3916: 
3917: On the list coloring version of Reed’s conjecture.
3918: 
3919: Electronic Notes in Discrete Mathematics 61, pp. 343–349.
3920: 
3921: Note: The European Conference on Combinatorics, Graph Theory and Applications (EUROCOMB’17)
3922: 
3923: External Links: ISSN 1571-0653,
3924: Document,
3925: Link
3926: 
3948: pp. 3–21.
3949: 
3950: Cited by: §1,
3951: Conjecture 10.
3952: 
3953: 
3954: [13]
3955: B. Farzad, M. Molloy, and B. Reed (2005)
3956: 
3957: ( \Delta-k )-critical graphs.
3958: 
3959: Journal of Combinatorial Theory, Series B 93 (2), pp. 173–185.
3960: 
4057: [21]
4058: K. Kawarabayashi and L. Picasarri-Arrieta (2024)
4059: 
4060: An analogue of Reed’s conjecture for digraphs.
4061: 
4062: Preprint arXiv:2407.05827.
4063: 
4064: Cited by: §1.
4065: 
4066: 
4067: [22]
4068: K. Kawarabayashi and L. Picasarri-Arrieta (2025)
4069: 
4070: An analogue of Reed’s conjecture for digraphs.
4071: 
4072: In Proceedings of the 2025 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA),
4073: 
4074: pp. 3310–3324.
4075: 
4076: Cited by: §1,
4077: §1,
4078: §1,
4079: §2,
4080: §3.3,
4081: Conjecture 5,
4082: Theorem 6,
4083: Problem 8.
4084: 
4085: 
4086: [23]
4087: A. D. King and B. A. Reed (2015)
4088: 
4089: A short proof that  \chi  can be bounded  \varepsilon  away from  \Delta+1  toward  \omega .
4090: 
4178: Cited by: §1,
4179: §1,
4180: §3.3,
4181: Conjecture 1,
4182: Corollary 2,
4183: Corollary 3.
4184: 
4185: 
4186: [32]
4187: B. Reed (1999)
4188: 
4189: A strengthening of Brooks’ theorem.
4190: 

## 375867 Kawarabayashi–Picasarri-Arrieta dichromatic bound conjecture
235: We prove that, for every fixed integer  b\in\mathbb{N} , every digraph  D  with  \tilde{\Delta}(D)=\Delta  being sufficiently large with respect to  b  either contains a biclique whose size exceeds  \Delta-2b  or has dichromatic number at most  \Delta-b .
236:     
237: 
238: This extends a classical result of Reed to the directed setting and supports a conjecture of the present authors.
239: Furthermore, the theorem is tight, as for all integers  b  and  \Delta\geqslant 3b  there exists a digraph  D  with  \tilde{\Delta}(D)=\Delta , dichromatic number  \Delta-b+1 , and whose largest biclique has size  \Delta-2b+1 .
240:   
241: 
242: 
243: 
244: 
245: 
246: 1. Introduction
247: 
260: 
261: 
262: unless  \Delta(G)=2  and  G  contains an odd cycle.
263: Pushing this direction further, in 1977 Borodin and Kostochka [8] posed a celebrated conjecture stating that
264: 
265: 
266: 
267: 
268:  \chi(G)\leqslant\max\{\Delta(G)-1,\omega(G)\} 
269: 
270: 
271: 
272: holds for every graph  G  with  \Delta(G)\geqslant 9 .
273: Even though the conjecture is still open in general, Reed [32] proved that it holds for graphs  G  with  \Delta(G)\geqslant 10^{10} .
274: Moreover, in 1998 Reed [31] conjectured that these inequalities are just the tip of the iceberg, and posed the following famous conjecture.
275: 
276: 
277: 
278: Conjecture 1 ([31]).
279: 
280: 
281: 
282: Every graph  G  satisfies  \chi(G)\leqslant\lceil\frac{1}{2}(\Delta(G)+1+\omega(G))\rceil .
283: 
284: 
285: 
286: 
287: 
288: As supporting evidence for the conjecture, in the same paper Reed proved that, for every graph  G ,
289:  \chi(G)\leqslant\tfrac{1}{2}\big(\Delta(G)+1+\omega(G)\big) 
290: holds whenever  \Delta(G)  is sufficiently large and  \omega(G)  is sufficiently close to  \Delta(G) ; formally when  \Delta(G)\geqslant\Delta_{0}  and  \omega(G)\geqslant(1-\varepsilon)\Delta(G)  for some absolute constants  \Delta_{0}\in\mathbb{N}  and  \varepsilon\in(0,1) .
291: This has the following two main consequences.
292: 
293: 
294: 
295: Corollary 2 ([31]).
296: 
297: 
318: 
319: 
320: 
321: Observe that Conjecture 1 is precisely the statement of Corollary 2 for  \varepsilon=1/2 . This gave rise to a line of research aimed at determining the largest value of  \varepsilon>0  for which Corollary 2 holds.
322: The current best result is due to Hurley, Joannis de Verclos, and Kang [18], who proved that it holds for  \varepsilon=0.119  for graphs with sufficiently large maximum degree. This improves on earlier results obtained by Bonamy, Perrett, and Postle [7] and by Delcourt and Postle [10].
323: 
324: 
325: 
326: 
327: Let us briefly discuss the sharpness of Corollary 3 and its connection to Conjecture 1.
328: First, observe that the threshold  \Delta_{b}  in Corollary 3 must depend on  b . Indeed, for every integer  b\in\mathbb{N} , there exists a graph  G  with  \Delta(G)=6b+2 ,  \omega(G)=4b+2 , and  \chi(G)=5b+3 . One example is the graph obtained from a  5 -cycle by blowing up each vertex into a clique of size  2b+1 .
329: In particular, such a graph does not satisfy the conclusion of Corollary 3, showing that  \Delta_{b}  must be at least  6b+3 .
330: 
331: 
332: 
333: 
334: However, the dependence of  \Delta_{b}  on  b  might not be necessary under the stronger hypothesis  \omega(G)\leqslant\Delta-2b-1 . Indeed, Conjecture 1 is easily seen to be equivalent to the following.
335: 
336: 
337: 
338: Conjecture 4.
339: 
340: 
341: 
342: For every  b\in\mathbb{Z}  and every graph  G , if  \omega(G)\leqslant\Delta-2b-1  then  \chi(G)\leqslant\Delta-b .
343: 
344: 
345: 
346: 
347: 
388: 
389: 
390: 
391: unless  D  is a very specific obstruction. This generalizes the aforementioned result of Reed [32], which itself supports the conjecture of Borodin and Kostochka [8]. Moreover, Kawarabayashi and Picasarri-Arrieta [22] recently posed the following conjecture, which, if true, implies both Conjecture 1 and an independent conjecture posed by Harutyunyan and Mohar [17].
392: 
393: 
394: 
395: Conjecture 5 ([22]).
396: 
397: 
398: 
399: Every digraph  D  satisfies  \vec{\chi}(D)\leqslant\lceil\tfrac{1}{2}(\tilde{\Delta}(D)+1+\overset{\text{\tiny$\bm{\leftrightarrow}$}}{\omega}(D))\rceil .
400: 
401: 
402: 
403: 
404: 
432: 
433: It follows from Theorem 6 that every digraph  D  with
434:  \overset{\text{\tiny$\bm{\leftrightarrow}$}}{\omega}(D)\leqslant\tilde{\Delta}(D)-\frac{1}{\varepsilon}(b+2) 
435: satisfies  \vec{\chi}(D)\leqslant\tilde{\Delta}(D)-b . In view of Corollary 3 and Conjectures 4 and 5, this condition is certainly not optimal. In the present paper, we prove the following sufficient condition for a digraph  D  to be  (\tilde{\Delta}(D)-b) -colorable, which generalizes Corollary 3 to the directed setting and supports Conjecture 5.
436: 
437: 
438: 
439: Theorem 7.
440: 
441: 
442: 
443: For every  b\in\mathbb{Z} , there exists  \Delta_{b}\in\mathbb{N}  such that every digraph  D  with  \tilde{\Delta}(D)\geqslant\Delta_{b}  and  \overset{\text{\tiny$\bm{\leftrightarrow}$}}{\omega}(D)\leqslant\tilde{\Delta}(D)-2b  satisfies  \vec{\chi}(D)\leqslant\tilde{\Delta}(D)-b .
444: 
520: 
521: 
522: 
523: Bounding the dichromatic number of oriented graphs in terms of their maximum degree is at the heart of the following famous conjecture due to Erdős and Neumann-Lara (see [12]), which can be seen as a directed version of Johansson’s bound for triangle-free graphs [20].
524: 
525: 
526: 
527: Conjecture 10 ([12]).
528: 
529: 
530: 
531: Every oriented graph  D  satisfies  \vec{\chi}(D)=O(\Delta/\log\Delta) , where  \Delta  is the maximum degree of the underlying graph of  D .
532: 
533: 
534: 
535: 
536: 
537: The analogous conjecture in terms of  \tilde{\Delta}  has been posed by McDiarmid and Mohar, see [17].
538: 
539: 
540: 
541: 
542: 2. Technical Overview
543: 
544: 
545: 
546: 
3914: [10]
3915: M. Delcourt and L. Postle (2017)
3916: 
3917: On the list coloring version of Reed’s conjecture.
3918: 
3919: Electronic Notes in Discrete Mathematics 61, pp. 343–349.
3920: 
3921: Note: The European Conference on Combinatorics, Graph Theory and Applications (EUROCOMB’17)
3922: 
3923: External Links: ISSN 1571-0653,
3924: Document,
3925: Link
3926: 
3948: pp. 3–21.
3949: 
3950: Cited by: §1,
3951: Conjecture 10.
3952: 
3953: 
3954: [13]
3955: B. Farzad, M. Molloy, and B. Reed (2005)
3956: 
3957: ( \Delta-k )-critical graphs.
3958: 
3959: Journal of Combinatorial Theory, Series B 93 (2), pp. 173–185.
3960: 
4057: [21]
4058: K. Kawarabayashi and L. Picasarri-Arrieta (2024)
4059: 
4060: An analogue of Reed’s conjecture for digraphs.
4061: 
4062: Preprint arXiv:2407.05827.
4063: 
4064: Cited by: §1.
4065: 
4066: 
4067: [22]
4068: K. Kawarabayashi and L. Picasarri-Arrieta (2025)
4069: 
4070: An analogue of Reed’s conjecture for digraphs.
4071: 
4072: In Proceedings of the 2025 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA),
4073: 
4074: pp. 3310–3324.
4075: 
4076: Cited by: §1,
4077: §1,
4078: §1,
4079: §2,
4080: §3.3,
4081: Conjecture 5,
4082: Theorem 6,
4083: Problem 8.
4084: 
4085: 
4086: [23]
4087: A. D. King and B. A. Reed (2015)
4088: 
4089: A short proof that  \chi  can be bounded  \varepsilon  away from  \Delta+1  toward  \omega .
4090: 
4178: Cited by: §1,
4179: §1,
4180: §3.3,
4181: Conjecture 1,
4182: Corollary 2,
4183: Corollary 3.
4184: 
4185: 
4186: [32]
4187: B. Reed (1999)
4188: 
4189: A strengthening of Brooks’ theorem.
4190: 

## 375879 Erdős Matching Conjecture for uniform hypergraphs
1: 
2: 
3: 
4: A Spectral Confirmation of the Erdős Matching Conjecture
5: 
6: 
7: 
8:  
9: 
10:   // Restore the saved color scheme preference, or
11:   // enact the browser preference if "automatic", 
12:   // without expecting DOM load to have completed.
13:   //
196: 
197: 
198: 
199: A Spectral Confirmation of the Erdős Matching Conjecture 
200: 
201: 
202: 
203: Liying Kang
204: 
205: Affiliation:  Department of Mathematics, Shanghai University, Shanghai 200444, PR China 
206:  Newtouch Center for Mathematics of Shanghai University, Shanghai 200444, PR China
207: 
208:   
228: Abstract
229:     
230: 
231: The Erdős Matching Conjecture concerns the maximum number of hyperedges in an  r -uniform hypergraph with bounded matching number. In this paper, we study a spectral counterpart of this conjecture. For sufficiently large  n , we determine the maximum spectral radius over all  n -vertex  r -uniform hypergraphs whose matching number is less than  s , and characterize the unique extremal hypergraph.
232:     
233: 
234: To establish the main theorem, we first apply the shifting method to reduce the problem to shifted hypergraphs. We then derive several spectral upper bounds through hypergraph decomposition and related variational estimates for tensor spectral radii.
235: With these estimates, we analyze the structural properties of shifted-saturated hypergraphs and prove the spectral extremal theorem for shifted hypergraphs with bounded matching numbers. Finally, we drop the shifted condition and extend our spectral bound to general  r -uniform hypergraphs.
236:     
237: 
238: Our main theorem states that for any  n -vertex  r -uniform hypergraph  H  with matching number  \nu(H)<s , the inequality  \rho(H)\leq\rho(\mathcal{F}_{s-1}(n))  holds whenever  n  is sufficiently large. Here  \mathcal{F}_{a}(n)  denotes the family of all  r -subsets of  [n]  intersecting the vertex set  [a] , and equality is attained if and only if  H  is isomorphic to  \mathcal{F}_{s-1}(n) . As an immediate corollary, we derive a spectral counterpart of the classical Erdős-Ko-Rado theorem for intersecting hypergraph families.
239:   
240: ††footnotetext: *Corresponding author.††footnotetext: Email addresses: lykang@shu.edu.cn (L. Kang), luyongchun@shu.edu.cn (Y. Lu),
245: 
246: 
247: 
248: Keywords: Hypergraph, Spectral radius, Erdős Matching Conjecture, Shifting
249: 
250: AMS (2000) subject classification: 05C50, 05C65
251: 
252:   
253: 
254: 
255: 
256: 1. Introduction
257: 
266: 
267: 
268: Given an  r -graph  \mathcal{F} , an  r -graph  {\mathcal{H}}  is called  \mathcal{F} -free if  {\mathcal{H}}  does not contain a copy of  \mathcal{F}  as a subhypergraph. The Turán number of  \mathcal{F} , denoted by  {\rm{ex}}_{r}(n,\mathcal{F}) , is the maximum number of hyperedges among all  n -vertex  \mathcal{F} -free  r -graphs.
269: A classical result in extremal graph theory is the Erdős–Gallai theorem [4], which determines the Turán number of  M_{s} , where  M_{s}  denotes a matching of size  s , i.e., the graph consisting of  s  independent edges. It is natural to consider the corresponding problem for hypergraphs. Let  M^{r}_{s}  denote a matching of size  s  in an  r -graph. In 1965, Erdős [3] proposed the following conjecture on hypergraph matchings.
270: 
271: 
272: 
273: Conjecture 1.1 (Erdős Matching Conjecture [3]).
274: 
275: 
276: 
277: Let integers  s,r\geq 2  and  n\geq sr-1 . Then
278: 
279: 
280: 
281: 
282:  \mathrm{ex}_{r}(n,M_{s}^{r})\leq\max\left\{\binom{sr-1}{r},\binom{n}{r}-\binom{n-s+1}{r}\right\}. 
287: 
288: 
289: 
290: The above conjecture is known to hold for the cases  r=2  [4] and  r=3  [8, 18]. For the general case, Erdős [3] verified Conjecture 1.1 for sufficiently large  n . Later, this threshold was improved by Bollobás, Daykin and Erdős [1], Huang, Loh and Sudakov [14], and Frankl, Łuczak and Mieczkowska [11]. For further developments and relevant results concerning this conjecture, one can refer to [7, 9, 10, 15]. Very recently, Kupavskii and Sokolov [16] completely resolved the non-uniform case of the conjecture for  n\leq 3s . Hou, Hu and Liu [13] proved the conjecture for the case  r=4  and  s\geq 6961 .
291: 
292: 
293: 
294: 
295: The goal of this paper is to establish a spectral confirmation of the Erdős Matching Conjecture for sufficiently large  n . We begin by introducing some notation. For positive integers  r  and  n , a real tensor  \mathcal{A}=  (  a_{i_{1}i_{2}\cdots i_{r}}  ) of order  r  and dimension  n  is defined as a multidimensional array where each entry  a_{i_{1}i_{2}\cdots i_{r}}\in\mathbb{R}  for all  i_{1},i_{2},\ldots,i_{r}\in[n] . A tensor  \mathcal{A}  is called symmetric if  \mathcal{A}_{i_{1}i_{2}\cdots i_{r}}=\mathcal{A}_{\sigma({i_{1}})\cdots\sigma({i_{r}})} , where  \sigma  is any permutation of its indices. The concept of tensor eigenvalues was independently established by Qi [20] and Lim [17] in 2005.
296: 
297: 
298: 
299: Definition 1.2 ([17], [20]).
300: 
301: 
302: 
303: Let  \mathcal{A}  be a tensor of order  r  and dimension  n . Let  {\bf x}^{[r]}=(x_{1}^{r},\ldots,x_{n}^{r})^{\rm T} . Then  \mathcal{A}{\bf{x}}^{r-1}  is defined to be a vector in  \mathbb{C}^{n}  whose  i -th component is
304: 
413: 
414: 
415: 
416: In this paper, we consider the Erdős Matching Conjecture in the spectral setting, thereby confirming the Erdős Matching Conjecture from a spectral perspective.
417: Let  \nu({\mathcal{H}})  denote the matching number of an  r -graph  {\mathcal{H}} , i.e., the maximum size of a matching in  {\mathcal{H}} . For an integer  a\geq 0 , define
418: 
419: 
420: 
421: 
422:  \mathcal{F}_{a}(n)=\left\{e\in\binom{[n]}{r}:e\cap[a]\neq\emptyset\right\}. 
423: 
424: 
425: 
1320:       
1321: 
1322: [7]
1323:  P. Frankl, Improved bounds for Erdős’ matching conjecture, J. Combin. Theory Ser. A 120 (2013) 1068–1072.
1324: 
1325: 
1326:       
1327: 
1328: [8]
1329:  P. Frankl, On the maximum number of edges in a hypergraph with a given matching number, Discrete Appl. Math. 216 (2017) 562–581.
1330: 
1331: 
1332:       
1333: 
1334: [9]
1335:  P. Frankl, Proof of the Erdős Matching Conjecture in a new range, Israel J. Math. 222(1) (2017) 421–430.
1336: 
1337: 
1338:       
1339: 
1340: [10]
1341:  P. Frankl, A. Kupavskii, The Erdős matching conjecture and concentration inequalities, J. Combin. Theory Ser. B 157 (2022) 366–400.
1342: 
1343: 
1344:       
1345: 
1346: [11]
1347:  P. Frankl, T. Łuczak, K. Mieczkowska, On matchings in hypergraphs, Electron. J. Combin. 19(2) (2012) P42.
1348: 
1349: 
1350:       
1356:       
1357: 
1358: [13]
1359:  J. Hou, C. Hu, X. Liu, A finite-board reduction for the Erdős Matching Conjecture and the 4-uniform case via exact certificates, arXiv preprint, arXiv:2605.26060, 2026.
1360: 
1361: 
1362:       
1363: 
1364: [14]
1365:  H. Huang, P. Loh, B. Sudakov, The size of a hypergraph and its matching number, Combin. Probab. Comput. 21(03) (2012) 442–450.
1366: 
1367: 
1368:       
1369: 
1370: [15]
1371:  D. Kolupaev, A. Kupavskii, Erdős’ Matching Conjecture for almost perfect matchings, Discrete Math. 346 (2023) 113304.
1372: 
1373: 
1374:       
1375: 
1376: [16]
1377:  A. Kupavskii, G. Sokolov, A complete solution of the Erdős-Kleitman matching problem for  n\leq 3s , arXiv preprint, arXiv:2511.21628, 2025.
1378: 
1379: 
1380:       

## 375901 The maximality conjecture for nm-independence on Polish groups
188:     
189: 
190: Inspired by the non-meager independence  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm}  introduced by Krupiński [3], we study further possible independence relations induced by ideals and provide a general framework for this topic. We show that the independence relation  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{\mathrm{Haar}}  induced by Haar null ideals is a good example for locally compact groups and provide an example showing  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{\mathrm{Haar}}\neq\mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm} .
191: Moreover, we introduce an order on the collection of all well-behaved independence relations and conjecture that  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm}  is the maximum one for Polish groups. We prove the conjecture under the extra hypothesis of  \sigma -compactness. For Lie groups, we discuss  \mathrm{SO}(3)  and
192:  \mathrm{SE}(2)  as examples, and prove that the independence relation is unique for nilpotent Lie groups.
193:   
194: 
195: 
196: 
197: 1 Introduction
198: 
199: 
200: 
268: 
269: 
270: 
271: In section 4, we try to classify all independence relations on certain groups in our framework. Moreover, we will give an order on the collection of the independence relations for  G , based on their induced ranks. We conjecture that  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm}  is the maximum independence relation when  G  is Polish. We prove the conjecture under the additional assumption that  G  is  \sigma -compact. We also give a more detailed study for the case where  G  is a Lie group. We We obtain a complete classification of all independence relations on the special orthogonal group  \mathrm{SO}(3)  and the special Euclidean group of the plane  \mathrm{SE}(2) . Moreover, we show the uniqueness of the independence relation when  G  is a nilpotent Lie group.
272: 
273: 
274: 
275: 
276: 2 Ideal-equipped group
277: 
278: 
279: 
280: 
894: 
895: 
896: Now we study maximal strongly admissible geometries. In well-behave cases, the maximum strongly admissible geometry exists.
897: Note that the maximum strongly admissible geometry is the finest independence relation and imposes the strongest requirement of stability. I conjecture that  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm}  is the maximum strongly admissible geometry and therefore intrinsic when  G  is a Polish group.
898: 
899: 
900: 
901: Conjecture 17.
902: 
903: 
904: 
905: Let  G  be a Polish group. Then  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm}  is the maximum strongly admissible geometry.
906: 
907: 
908: 
909: 
910: 
911: At least we can prove this conjecture under the additional condition that  G  is  \sigma -compact.
912: 
913: 
914: 
915: Theorem 18.
916: 
917: 
918: 
919: Let  G  be a  \sigma -compact Polish group. Then  \mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{nm}=\mathrel{\raise 0.86108pt\hbox{\vtop{\halign{#\cr$|$\cr\raise-3.87495pt\hbox{$\smile$}\crcr}}}}^{o}  is the maximum strongly admissible geometry.
920: 

## 375905 The maximal product-of-trees embedding conjecture for handlebody groups
515: 
516: 
517: 
518: Conjecture 1.
519: 
520: 
521: 
522: The maximal integer  n  such that  F_{2}^{n}  quasi-isometrically embeds into the handlebody group of genus  g  is  n=g-1 .
523: 
524: 
525: 
526: 
527: 
528: In order to prove the conjecture, because of Corollary 3.6, it suffices to show that the collection of all one-holed tori is incompatible with the handlebody group, as defined in Definition 3.5. This would be the same strategy as for Torelli groups.
529: 
530: 
531: 
532: 
533: Secondly, while we obtain bounds in the context of surface braid groups, we do not determine optimal ones. It is then natural to pose the following:
534: 
535: 
536: 
537: Problem 2.

## 375920 Boltyanskii's illumination conjecture for convex bodies
157: 
158: 1.1 Definitions
159: 
160: 1.2 Illumination Conjecture
161: 
162: 1.3 Primitive Polytopes and Positive Bases
163: 
164: 1.4 Two Kinds of Primitive Polytopes
165: 
166: 1.5 Preliminary Claims
167: 
168: 1.6 Proof of Theorem 
169: 
198: 
199: A convex  d -dimensional polytope may be defined as a bounded intersection of closed halfspaces in  \mathbb{E}^{d}  with interior.
200: A polytope is primitive if omitting any halfspace renders the intersection unbounded.
201: In this paper, we prove the Illumination Conjecture for the primitive polytopes: any primitive convex  d -polytope  P  can be illuminated with at most  2^{d}  directions; even fewer if  P  is not a linear image of a  d -cube.
202:   
203: 
204: 
205: 
206: 1 Introduction
207: 
208: 
209: 
210: 1.1 Definitions
300: 
301: 
302: 
303: 1.2 Illumination Conjecture
304: 
305: 
306: 
307: 
308: We can now write down one of at least five equivalent statements of the Illumination Conjecture itself, stated by V. Boltyanskiy [5]:
309: 
310: 
311: 
312: Conjecture 1.
313: 
314: 
315: 
316: A convex body  K\in\mathcal{K}^{d}  can be illuminated by at most  2^{d}  directions, even fewer if  K  is not a linear image of a  d -dimensional cube.
317: 
318: 
319: 
320: 
321: 
322: Prior to Boltyanskiy, the equivalent versions of the Illumination Conjecture were stated by H. Hadwiger [14, 15], and A. Markus together with I. Gohberg [13].
323: 
324: 
325: 
326: 
327: The Illumination Conjecture is conclusively proven for  K\in\mathcal{K}^{d}  only in case  d=2  (see, for example, Boltyanskiy and Gohberg’s [6] book).
328: The best available three-dimensional estimate,  \Ill(K)\leq 14:K\in\mathcal{K}^{3} , is by A. Prymak [20].
329: As of February 2026, the best general upper bound is by M. Campos, P. van Hintum, R. Morris, and M. Tiba [8]:
330: 
331: 
332: 
333: 
334:  Ill_{d}\leq 4^{d}\exp\left(-c\left(\frac{d}{(\log d)^{8}}\right)\right)\text{ for some universal constant }c. 
335: 
336: (2)
340: 
341: 
342: The problem of illuminating convex polytopes is wide open even in  \mathbb{E}^{3} .
343: The Illumination Conjecture is proven for some particular classes of polytopes, such as 3-polytopes with affine symmetry (K. Bezdek [1]), dual cyclic polytopes (K. Bezdek, T. Bisztriczky [2]), totally-sewn 4-polytopes (T. Bizstriczky, F. Fodor [4]), strongly monotypic polytopes (V. Bui [7]), and zonotopes (H. Martini [16]).
344: This list is by no means exhaustive, for the detailed history of the Illumination Conjecture, and the related results, refer to the survey articles by K. Bezdek and M. Khan [3], G. Fejes Tóth [10], and H. Martini [17].
345: 
346: 
347: 
348: 
349: 1.3 Primitive Polytopes and Positive Bases
350: 
351: 
352: 
353: 
376: 
377: 
378: Our motivation to study the primitive polytopes arose from tinkering. To illuminate a convex polytope, it is necessary and sufficient to illuminate its vertices. That’s why, at first, we tried to describe the effect that removing a vertex of a convex polytope has on the illumination number. However, removing vertices one by one inevitably ends on a simplex, and the illumination number of a simplex in  \mathbb{E}^{d}  is only  d+1 . Moreover, removing a vertex may increase the illumination number, or may decrease it, and we aimed for a somewhat monotonous process, some transformation that, hopefully, wouldn’t decrease the illumination number.
379: A convex polytope is the convex hull of a finite set of points with interior. However, it may also be defined as a bounded intersection of a finite number of halfspaces with interior. Omitting halfspaces immediately looks more promising than removing vertices: you end on a primitive polytope, and there’s several combinatorially different kinds in  \mathbb{E}^{d},d\geq 2 . Moreover, a cube is primitive. We proved the Illumination Conjecture for the primitive polytopes. If we could find some process, which takes any convex polytope to some primitive polytope without decreasing the illumination number, then the Illumination Conjecture for the convex polytopes would be proven. Unfortunately, ”omitting halfspaces” also may increase the illumination number, or may decrease it, there’s no monotonous effect on the illumination number.
380: 
381: 
382: 
383: 
384: 
385: Let  P  be the bounded intersection of some finite number of negative halfspaces:  P=H^{-}_{1}\cap\ldots\cap H^{-}_{n} . For each  i:1\leq i\leq n , we denote the respective facet  P\cap H_{i}  by  F_{i} . Let  \left\{\mathbf{b}_{i}:1\leq i\leq n\right\}  be the set of outer normals of  P ’s facets. We scale each  b_{i}  so that  H_{i}=H_{\mathbf{b}_{i},1} . In this way, this set of outer normals is also the set of vertices of the polar polytope  Q=P^{o} .
386: 
387: 
388: 
463: 
464: 
465: 
466: If this hypothesis held, proving the Illumination Conjecture for the primitive polytopes would directly imply the Illumination Conjecture for all the convex polytopes. Unfortunately, this hypothesis is false.
467: 
468: 
469: 
470: 
471: Claim 5.
472: 
473: 
474: 
475: There exists a convex polytope  P\in\mathcal{K}^{3} , such that any spill of  P  through a single facet has greater illumination number than  P .
495: 
496: 
497: 
498: The main result of this chapter is Theorem 2, the Illumination Conjecture for the primitive polytopes. Moreover, we pose the following conjecture:
499: 
500: 
501: 
502: Conjecture 6.
503: 
504: 
505: 
506: A primitive polytope in  \mathbb{E}^{d},d\geq 4  has at most  2^{d}  vertices, even fewer if it isn’t an affine  d -cube.
507: 
508: 
509: 
510: 
511: Remark 5.
512: 
513: 
514: 
515: Conjecture 6 is trivial in  \mathbb{E}^{2} , since there are only two classes of primitive polygons: triangles and parallelograms. Primitive polytopes in  \mathbb{E}^{3}  were enumerated by Steinitz [23]. Later, L. Fejes Tóth [11] came up with a shorter proof.
516: 
517: 
518: 
519: 
520: Remark 6.
521: 
522: 
523: 
524: A number of vertices of a primitive polytope  P\subset\mathbb{E}^{d}  is equal to the number of facets of  \conv\mathcal{P} , a convex hull of a corresponding positive basis. A positive basis of  \mathbb{E}^{d}  can have at most  2d  vectors. According to McMullen’s [18] upper bound theorem, for a given dimension  d\geq 2 , the polytope with the greatest number of facets is the cyclic polytope. The number of facets of a cyclic polytope with  n  vertices in  \mathbb{E}^{d} , denoted by  f_{d-1}\left(C(d,n)\right)  is expressed by the following formula (see, for example, K. Fukuda’s [12] survey article):
713: 
714: 
715: 
716: Now we can prove the Illumination Conjecture for the primitive polytopes.
717: The proof is inductive: the only primitives in  \mathbb{E}^{2}  are triangles and parallelograms, their illumination numbers are 3 and 4 respectively.
718: Suppose that the Illumination Conjecture holds for the primitive polytopes in  \mathbb{E}^{k}:k\in\left\{1,\ldots,d-1\right\}  for some fixed  d\geq 3 .
719: 
720: 
721: 
722: 
723: We will use the separation lemma, proved by P. Soltan and V. Soltan [22] and, independently, for illumination by affine subspaces, by K. Bezdek [1]:
724: 
725: 
726: 
727: Lemma 12.
806: [2]
807: Károly Bezdek and Tibor Bisztriczky
808: 
809: “A proof of Hadwiger’s covering conjecture for dual cyclic polytopes”
810: 
811: In Geom. Dedicata 68.1, 1997, pp. 29–41
812: 
813: DOI: 10.1023/A:1004965512469
814: 
815:       
816: 
817: [3]
818: Károly Bezdek and Mohammad. Khan
872: [8]
873: Marcelo Campos, Peter van Hintum, Robert Morris and Marius Tiba
874: 
875: “Towards Hadwiger’s conjecture via Bourgain slicing”
876: 
877: In Int. Math. Res. Not. 2024.10, 2024, pp. 8282–8295
878: 
879: DOI: 10.1093/imrn/rnad198
880: 
881:       
882: 
883: [9]
884: Chandler Davis
976: [18]
977: P McMullen
978: 
979: “On the upper-bound conjecture for convex polytopes”
980: 
981: In J. Comb. Theory B 10.3, 1971, pp. 187–200
982: 
983: DOI: 10.1016/0095-8956(71)90042-6
984: 
985:       
986: 
987: [19]
988: Peter McMullen, Rolf Schneider and Geoffrey Shephard

## 375932 Kao's conjecture on Hamiltonicity of Cartesian products with odd paths
211: A  \{P_{2},P_{3}\} -factor in a graph  G  is a factor of  G  in which every component is a path on two or three vertices. Let  T\Box P_{n}  be the Cartesian product of a tree  T  and a path on  n  vertices.
212: Kao and Weng [9] proved that  T\Box P_{n}  is hamiltonian if  T  has a path factor and  n  is a sufficiently large even integer.
213: In this article we prove that, for every odd  n , there exists a tree  T  of maximum degree 4 that has a  \{P_{2},P_{3}\} -factor such that  T\Box P_{n}  is not hamiltonian,
214: thereby refuting a conjecture given in [9].
215:   
216: 
217: 
218: 
219: 
220: Key words: Cartesian product, hamiltonian graph.
221: 
222: 
223: 
330: 
331: 
332: This approach does not work when  n  is odd, for the simple reason that  P_{3}\Box P_{n}  is not hamiltonian. As we shall see hamiltonicity of  G\Box P_{n}  does not depend on
333: maximum degree of  G , contrary to the conjecture raised in [9].
334: 
335: 
336: 
337: Conjecture 1.4
338: 
339: 
340: 
341: [9]
342: Let  G  be a graph with a  \{P_{2},P_{3}\} -factor and  n\geq 4\Delta(G)-2 . If  G\Box P_{n}  is balanced bipartite, then  G\Box P_{n}  is hamiltonian.
343: 
344: 
345: 
346: 
347: 
348: In particular, if  n  is odd,  T\Box P_{n}  might be non-hamiltonian even if  n  is arbitrarily large relative to  \Delta(T) .
349: In this article we refute the above conjecture by proving that for every odd integer  n  there exists a graph  G  of maximum degree four, that has  \{P_{2},P_{3}\} -factor, such that for every odd  i\leq n  the graph  G\Box P_{i}  is not hamiltonian.
350: 
351: 
352: 
353: Theorem 1.5
354: 
355: 
356: 
357: For every positive integer  n  there exists a balanced bipartite graph  G  of maximum degree four, that has a  \{P_{2},P_{3}\} -factor, such that  G\Box P_{i}  is not hamiltonian for every odd  i\leq n .
358: 

## 375980 Cancellative elements in bend quotients of tropical principal prime ideals
408: 
409: 
410: 
411: Using results from [7] we are able to give geometric examples of normalization of tropical curves; see Example 7.6, Example 8.7, and Example 8.12, the last of which is dependent on Conjecture 8.10 about cancellative elements in  A .
412: 
413: 
414: 
415: 
416: In these examples, the normalization of the tropicalization of a curve with unique singular point at the origin looks like the tropicalization of the normalization. We make the following conjecture:
417: 
418: 
419: 
420: Conjecture 1.6.
421: 
422: 
423: 
424: Let  C  be an irreducible affine algebraic curve with one singular point. Then there is an embedding of  C  with ideal  I\subseteq K[x_{1},\ldots,x_{n}]  satisfying the following property. Let  A=S[x_{1},\ldots,x_{n}]/\operatorname{Bend}(\operatorname{trop}I) , let  R=\operatorname{Frac}(A) , and let  \overline{A}^{\mathrm{V}}  be the valuative integral closure of  A  in  R . Then the integral closure of  B=K[x_{1},\ldots,x_{n}]/I  in its field of fractions is obtained by adjoining to  B  lifts of the elements in  \overline{A}^{\mathrm{V}}\backslash A .
425: 
426: 
427: 
428: 
429: 
430: Of course, one cannot begin addressing this conjecture until one can compute  \operatorname{Frac}(A) , i.e., identify the cancellative elements of  A . Construction 9.7 tells us how to find pairs of polynomials certifying that a polynomial is not cancellative and
431: Corollary A.4
432: gives a sufficient condition for verifying that  f  is not cancellative in the quotient by the bend congruence of a
433: tropicalized ideal  I .
434: In
435: Appendices A and B
436: we outline a method that can be used to computationally check that polynomials of small support are not cancellative modulo the bend congruence of a tropicalized ideal. We illustrate part of this computation for the case of the tropicalization of a principal ideal generated by a general trinomial.
437: 
438: 
439: 
3335: 
3336: 
3337: 
3338: Based on computing examples, including the ones above, we make the following conjecture.
3339: 
3340: 
3341: 
3342: Conjecture 8.10.
3343: 
3344: 
3345: 
3346: Let  K  be a field with valuation  K\to S , where  S  is a sub-semifield of  \mathbb{T}  and let  \mathcal{M}  a toric monoid. Given any principal prime ideal  I\subseteq K[\mathcal{M}]  that does not contain a monomial or binomial1414
3347:                 14
3348:                 
3349:                 
3350:                 
3351:               If  I  is prime and contains a monomial  m  then  V(I)  is contained in the closure of a toric boundary stratum. If  I  contains a binomial then  V(I)  is contained in the closure of (a translate of) a proper subtorus. Either way,  V(I)  is best viewed as being embedded in a different toric variety and so  S[\mathcal{M}]/\operatorname{Bend}(\operatorname{trop}I)  is best given by a different presentation.
3362: 
3363: 
3364: 
3365: The ( \Leftarrow ) direction follows from Corollary 7.4. So the open content of the conjecture is the ( \Rightarrow ) direction.
3366: 
3367: 
3368: 
3369: Remark 8.11.
3370: 
3371: 
3372: 
3373: Let  K ,  S ,  \mathcal{M} , and  I  be as in Conjecture 8.10. Since  I  is prime  V(I)  has only one component, and since  I  does not contain a monomial, that component is not contained in the toric boundary. Thus Corollary 7.4 tells us that, if we let  A=S[\mathcal{M}]/\operatorname{Bend}(\operatorname{trop}I)  and  R=\operatorname{Frac}(A) , then  \overline{A}^{\mathrm{V}}=\overline{A}^{\mathrm{Q}}=\overline{A}^{\mathrm{aQ}}=\overline{A}^{\mathrm{wQ}} .
3374: 
3375: 
3376: 
3377: 
3378: 
3379: If we assume Conjecture 8.10 then we can compute  \overline{A}^{\mathrm{V}}  in concrete cases.
3380: 
3381: 
3382: 
3383: Example 8.12.
3384: 
3385: 
3386: 
3387: Let  K  be a field, let  f^{\prime}=x^{2}+x^{3}-y^{2}\in K[x,y] , let  I:=(f^{\prime})\subseteq K[x,y] , and let  J=\operatorname{trop}I .
3388: If we let  A=\mathbb{T}[x,y]/\operatorname{Bend}(J) , then Conjecture 8.10 would give us that  R=\operatorname{Frac}(A)  is  =\mathbb{T}[x^{\pm},y^{\pm}]/\operatorname{Bend}(J) .
3389: The same computations as in Example 7.6 would then show that
3390: 
3391: 
3392: 
3393: 
3394:  \overline{A}^{\mathrm{V}}=R_{P_{1}}\cap R_{P_{2}}=\mathbb{T}[x^{n}y^{m}:m\geq 0,m+n\geq 0]/\operatorname{Bend}(J)=A\big[\frac{y}{x}\big]. 
3395: 
3396: 
3397: 
3402: 
3403: 
3404: 
3405: Based on Examples 8.7 and 8.12 we have the following conjecture.
3406: 
3407: 
3408: 
3409: Conjecture 8.13.
3410: 
3411: 
3412: 
3413: Let  C  be an irreducible affine algebraic curve with one singular point. Then there is an embedding of  C  with ideal  I\subseteq K[x_{1},\ldots,x_{n}]  satisfying the following property. Let  A=S[x_{1},\ldots,x_{n}]/\operatorname{Bend}(\operatorname{trop}I) , let  R=\operatorname{Frac}(A) , and let  \overline{A}^{\mathrm{V}}  be the valuative integral closure of  A  in  R . Then the integral closure of  B=K[x_{1},\ldots,x_{n}]/I  in its field of fractions is obtained by adjoining to  B  lifts of the elements in  \overline{A}^{\mathrm{V}}\backslash A .
3414: 
3415: 
3416: 
3417: 
3418: 
3419: If this conjecture is true, it would naturally bring up the following question.
3420: 
3421: 
3422: 
3423: Question 8.14.
3424: 
3425: 
3426: 
3427: Let  C  be an arbitrary algebraic curve. Is there an embedding of  C  in a toric variety such that the normalization of  C  can be seen at a tropical level by looking in each torus-invariant open affine?
3428: 
3843: 
3844: 
3845: 
3846: One way to approach Conjecture 8.10 would be to show that if  f\in S[\mathcal{M}]  has more than one term then there is a pair  (g,h)\notin\operatorname{Bend}(J)  such that  fg=fh  in  S[\mathcal{M}] , i.e., there is a witness pair for  f  that is not in  \operatorname{Bend}(J) .
3847: Corollary 9.13 tells us that this is equivalent to the existence of a pair that arises from Construction 9.7 but is not contained in  \operatorname{Bend}(J) .
3848: 
3849: 
3850: 
3851: 
3852: Appendix A Bounds on circuits
3853: 
3854: 
3855: 
3856: 
3857: In this appendix, we give a computational approach to Conjecture 9.13. Using as a starting point the discussion at the end of Section 9, we want to show that there are pairs  (g,h)  that arise from Construction 9.7 that are not in  \operatorname{Bend}(\operatorname{trop}I) . We begin by characterizing when such a pair is in  \operatorname{Bend}(\operatorname{trop}I) .
3858: 
3859: 
3860: 
3861: Proposition A.1.
3862: 
3863: 
3864: 
3865: Let  S  be a subsemifield of  \mathbb{T} , let  v:K\to S  be a valuation on a field  K , and let  \mathcal{M}  be a toric monoid.
3866: Let  I\subseteq K[\mathcal{M}]  be an ideal.

## 376009 Borodin–Kostochka conjecture
167: 2.1 Structural framework around an induced  C_{5} 
168: 
169: 
170: 3 The Borodin-Kostochka conjecture on  (P_{6},C_{4},C_{6}) -free graphs
171: 
172: 
173: 3.1 Properties of  B -vertices
174: 
175: 3.2 Properties of  A -vertices
176: 
177: 3.3 Analysis when  A=\emptyset  and  B\neq\emptyset 
178: 
179: 3.4 Analysis when  A=B=\emptyset 
236: 
237: 
238: Keywords:
239: Borodin–Kostochka conjecture;  (P_{6},C_{4}) -free graphs; chromatic number; induced subgraph.
240: 
241: 
242: 
243: 
244: MSC (2020):
245: 05C15, 05C69
246: 
247: 
248: 
265: 
266: 
267: 
268: For graphs with  \omega(G)=\Delta(G)\geq 3 , Brooks’ theorem assures  \omega(G)=\chi(G)=\Delta(G) ; thus the bound in Brooks’ theorem is tight. Also, for  3\leq\Delta(G)\leq 8 , there exist graphs with  \omega(G)\leq\Delta(G)-1  and  \chi(G)=\Delta(G)  [12]. Hence, for  3\leq\Delta(G)\leq 8 , Brooks’ bound cannot be improved to  \chi(G)\leq\Delta(G)-1  by taking the hypothesis  \omega(G)\leq\Delta(G)-1 . However, the situation may be different for  \Delta(G)\geq 9 . In 1977, Borodin and Kostochka conjectured the following strengthening of the Brooks’ bound.
269: 
270: 
271: 
272: Conjecture 1.2 (Borodin–Kostochka conjecture [2]).
273: 
274: 
275: 
276: For a graph  G , if  \Delta(G)\geq 9  and  \omega(G)\leq\Delta(G)-1 , then  \chi(G)\leq\Delta(G)-1 .
277: 
278: 
279: 
280: 
281: 
282: Since there exist graphs with  \omega(G)\leq\Delta(G)-2  and  \chi(G)\geq\Delta(G)-1  [12], Conjecture 1.2 cannot be further strengthened to  \chi(G)\leq\Delta(G)-2  if the condition  \omega(G)\leq\Delta(G)-1  is replaced by  \omega(G)\leq\Delta(G)-2 . In the same paper [2] where Borodin and Kostochka proposed Conjecture 1.2, they proved the conjecture for graphs with  \omega(G)\leq\left\lfloor\tfrac{\Delta(G)-1}{2}\right\rfloor . Note that Conjecture 1.2 can be restated as: any graph  G  with  \chi(G)\geq\Delta(G)\geq 9  contains a clique of size  \Delta(G) . This reformulation motivated researchers to show the existence of large cliques in the graphs whose chromatic number is very close to its maximum degree. In [22], Kostochka showed that any graph  G  with  \chi(G)=\Delta(G)\geq 29  contains a clique of size at least  \Delta(G)-28 . In [14], Cranston and Rabern proved that any graph  G  with  \chi(G)=\Delta(G)\geq 13  contains a clique of size at least  \Delta(G)-3 . Another direction of research towards the resolution of Conjecture 1.2 is to assume the existence of a minimal (in terms of number of vertices) counterexample to the conjecture and study its structure. In [13], Cranston and Rabern did an in-depth study on the structure of a minimal counterexample to the conjecture. In fact, they obtained a list of small graphs that should not appear as induced subgraphs in any such counterexample. We suggest the readers to visit the website (https://landon.github.io/graphdata/borodinkostochka/offline/index.html) to find the list of such small graphs.
283: 
284: 
285: 
286: 1.1.  Related Work
287: 
288: 
289: Figure 1: Some special graphs.
290: 
291: 
292: 
293: 
294: Although substantial progress has been made towards the resolution of the Borodin-Kostochka conjecture, it remains open in general. By using some probabilistic methods, Reed [25] proved that the Borodin-Kostochka conjecture is true for graphs with  \Delta(G)\geq 10^{14} . Recently, Dvořák et al. [18] proved the conjecture for graphs with  \Delta(G)\geq 3\cdot 10^{9}  in the stronger setting of correspondence coloring. Together, these results provide asymptotic confirmation of the conjecture. A class of graphs is hereditary if it is closed under taking induced subgraphs. For a family  \mathcal{H}=\{H_{1},H_{2},\ldots,H_{n}\}  of graphs, a graph  G  is said to be  \mathcal{H} -free (or  (H_{1},H_{2},\ldots,H_{n}) -free) if no induced subgraph of  G  is isomorphic to any  H_{i},i\in[n] . In particular, for  \mathcal{H}=\{H\} , we simply write  H -free instead of  \{H\} -free. Note that a class of  \mathcal{H} -free graphs is hereditary. Many well-known classes of graphs such as perfect graphs, chordal graphs, and cographs can be characterized as  \mathcal{H} -free graphs for a suitable family  \mathcal{H}  of graphs. So it is natural to attack any graph problem on graphs with some forbidden induced subgraphs. Consequently, the recent trend shows an increasing interest to prove the Borodin-Kostochka conjecture for  \mathcal{H} -free graphs. Below, we present a list of such  \mathcal{H} -free graph classes for which the conjecture has been proved.
295: 
296: 
297: Table 1: Graph classes for which Conjecture 1.2 holds.
298: 
299: 
300: 
301: 
302: Year
303: Authors      
304: 
305: 
306: Graph Class
409: 
410: 
411: 
412: In this paper, we show that Borodin-Kostochka conjecture is true for  (P_{6},C_{4}) -free graphs. This extends the results of [9, 19, 20, 24, 26]. In particular, we prove the following theorem.
413: 
414: 
415: 
416: Theorem 1.3 (Main Theorem).
417: 
418: 
419: 
420: Let  G  be a  (P_{6},C_{4}) -free graph. If  \Delta(G)\geq 9  and  \omega(G)\leq\Delta(G)-1 , then  \chi(G)\leq\Delta(G)-1 .
421: 
555: 
556: 
557: 
558: A list assignment  L  of a graph  G  is a mapping that assigns to each vertex  v\in V(G)  a set  L(v)  of colors. The graph  G  is said to be  L -colorable if there exists a proper coloring  c  of  G  such that  c(v)\in L(v)  for every  v\in V(G) . For a function  f:V(G)\to\mathbb{N} , an  f -assignment is a list assignment  L  of  G  such that  |L(v)|=f(v)  for every  v\in V(G) . A graph  G  is called  f -choosable if it is  L -colorable for every  f -assignment  L  of  G . In particular, if  G  is  f -choosable with  f(v)=d_{G}(v)-1  for every  v\in V(G) , the graph  G  is called  d_{1} -choosable. The following result implies that any vertex-critical counterexample to the Borodin-Kostochka conjecture cannot contain a  d_{1} -choosable subgraph.
559: 
560: 
561: 
562: Lemma 2.2 ([13]).
563: 
564: 
565: 
566: If  G  is a  \Delta -vertex-critical graph, then  G  cannot contain any non-empty  d_{1} -choosable induced subgraph  H . So such a graph  G  contains none of the following graphs: (i)  K_{3}\vee P_{4} , (ii)  K_{4}\vee S , where  S  is any spanning subgraph of  C_{4} , (iii)  K_{2}\vee C_{5} , (iv)  K_{2}\vee\textit{kite} . (see Figure 2)
567: 
569: 
570: 
571: 
572: For a positive integer  k , we define  \mathcal{C}_{k}=\{G\mid\Delta(G)=\chi(G)=k\ \text{and}\ \omega(G)<k\} . Note that  \mathcal{C}_{1}=\mathcal{C}_{2}=\emptyset  and  \mathcal{C}_{k}\neq\emptyset  for  3\leq k\leq 8  [12]. Also, note that if  G  is a counterexample to the Borodin-Kostochka conjecture, then we have  \Delta(G)\geq 9 ,  \omega(G)<\Delta(G) , and  \chi(G)=\Delta(G) . Clearly, for  k\geq 9 , the set  \mathcal{C}_{k}  consists of the counterexamples to the Borodin-Kostochka conjecture. The following result was independently established by Kostochka and Catlin.
573: 
574: 
575: 
576: Theorem 2.3 ([5, 22]).
577: 
578: 
579: 
580: Let  \mathcal{F}  be a hereditary class of graphs. If  \mathcal{C}_{k}\cap\mathcal{F}=\emptyset  for  k\geq 5 , then  \mathcal{C}_{k+1}\cap\mathcal{F}=\emptyset .
581: 
583: 
584: 
585: 
586: We use the following result about the counterexamples to the Borodin-Kostochka conjecture in a hereditary graph class frequently in our work. This result has appeared in several papers implicitly [11, 15, 19] and for the sake of completeness, we provide a brief proof of it.
587: 
588: 
589: 
590: Lemma 2.4.
591: 
592: 
593: 
594: For a hereditary graph class  \mathcal{F} , if  \mathcal{F}\cap\mathcal{C}_{k}\neq\emptyset  for some  k\geq 9 , then there exists an imperfect vertex-critical graph  G\in\mathcal{F}\cap\mathcal{C}_{9}  with  |d(u)-d(v)|\leq 1  for any  u,v\in V(G) . Moreover, if  \mathcal{F}  is the class of  (P_{6},C_{4}) -free graphs, then  G  contains an induced  C_{5} .
595: 
640: 
641: 
642: 
643: If  G  is a blowup of the Petersen graph, then  G  satisfies the Borodin–Kostochka conjecture.
644: 
645: 
646: 
647: 
648: 2.1.  Structural framework around an induced  C_{5} 
649: 
650: 
651: 
652: 
772: 
773: 
774: 
775: 3 The Borodin-Kostochka conjecture on  (P_{6},C_{4},C_{6}) -free graphs
776: 
777: 
778: 
779: 
780: In this section, we give the proofs of Theorem 1.4 and Theorem 1.5.
781: To prove the structural result stated in Theorem 1.5, we consider a graph  G  satisfying the hypothesis of Theorem 1.5 and prove a series of lemmas describing the structure of  G .
782: 
783: 
784: 
1541: 
1542: 
1543: 
1544: Now we proceed to prove the Borodin-Kostochka conjecture for the class of  (P_{6},C_{4}) -free graphs. We denote by  \mathcal{G}  the class of  (P_{6},C_{4}) -free graphs. For the sake of contradiction, we assume that the class  \mathcal{G}  contains a counterexample to the Borodin-Kostochka conjecture implying that  \mathcal{G}\cap\mathcal{C}_{k}\neq\emptyset  for some  k\geq 9 . Then by Lemma 2.4, there exists an imperfect vertex-critical graph  G\in\mathcal{G}\cap C_{9}  containing an induced  C_{5}  and  |d(u)-d(v)|\leq 1  for any  u,v\in V(G) . By Lemma 2.1,  G  does not contain any clique-cutset. Also, since  G  is  \Delta -critical, by Lemma 4.3,  G  does not contain any universal vertex. To make the context clear, we mention that, this graph  G  is taken in the hypotheses of Lemmas 4.4, 4.5, 4.7, 4.8, 4.9, 4.10, and their respective proofs given in the following subsections.
1545: 
1546: 
1547: 
1548: 4.1.  Analysis of  G  around  F_{1}  or  F_{3} 
1549: 
1550: 
1551: 
1552: 
1553: In this subsection, we analyze the structure of  G  around  F_{1}  or  F_{3} .
2058: 
2059: 
2060: 
2061: Now we are ready to prove the main result of this paper, that is Theorem 1.3, which validates the Borodin-Kostochka conjecture for  (P_{6},C_{4}) -free graphs.
2062: 
2063: 
2064: 
2065: Proof of Theorem 1.3.
2066: 
2067: 
2068: 
2069: For the sake of contradiction, assume that there exists a counterexample to Theorem 1.3, that is  \mathcal{G}\cap\mathcal{C}_{k}\neq\emptyset  for some  k\geq 9 . Then by Lemma 2.4, there exists an imperfect vertex-critical graph  G\in\mathcal{G}\cap\mathcal{C}_{9}  with  |d(u)-d(v)|\leq 1  for any  u,v\in V(G) . Moreover,  G  contains an induced  C_{5} . By Lemma 2.1 and Lemma 4.3,  G  does not contain any clique-cutset and any universal vertex. Also, by Theorem 1.4,  G  contains an induced  C_{6} . Note that  G  satisfies Lemma 4.4 and Lemmas 4.7-4.10. Then by Theorem 4.2, the only possible situation is that  G  is a blowup of  H_{1} , where the constituent-cliques corresponding to  v_{i},i\in[6]  are not empty (see Figure 4), that is,  G  is a blowup of the Petersen graph. This contradicts Lemma 2.6. So we conclude that there does not exist any such counterexample  G\in\mathcal{G} . Hence, Theorem 1.3 follows.
2070: ∎
2151: 
2152: [7]
2153: 
2154: R. Chen, K. Lan, X. Lin, Y. Zhou, Borodin-Kostochka conjecture holds for odd-hole-free graphs, Graphs Combin. 40 (2024) 26.
2155: 
2156: 
2157:       
2158: 
2159: [8]
2160: 
2161: R. Chen, K. Lan, Y. Zhou, Coloring  \{P_{2}\cup P_{3},\textit{house}\} -free graphs with  \Delta-1  colors, Discrete Appl. Math. 342 (2024) 12–18.
2162: 
2163: 
2193: 
2194: [13]
2195: 
2196: D. W. Cranston, L. Rabern, Coloring a graph with  \Delta-1  colors: Conjectures equivalent to the Borodin-Kostochka conjecture that appear weaker, Eur. J. Combin. 44 (2015) 23–42.
2197: 
2198: 
2199:       
2200: 
2201: [14]
2202: 
2203: D. W. Cranston, L. Rabern, Graphs with  \chi=\Delta  have big cliques, SIAM J. Discrete Math. 29 (2015) 1792–1814.
2204: 
2205: 
2214: 
2215: [16]
2216: 
2217: M. Dhurandhar, Validity of Borodin and Kostochka conjecture for classes of graphs without a single, forbidden subgraph on  5  vertices, (2021) arXiv:2101.01354.
2218: 
2219: 
2220:       
2221: 
2222: [17]
2223: 
2224: G. A. Dirac, Note on the colouring of graphs, Math. Z. 54 (1951) 347–353.
2225: 
2226: 
2228: 
2229: [18]
2230: 
2231: Z. Dvořák, R. J. Kang, D. Mikšaník, On Borodin-Kostochka conjecture for correspondence coloring, (2026) arXiv:2603.14427.
2232: 
2233: 
2234:       
2235: 
2236: [19]
2237: 
2238: U. K. Gupta, D. Pradhan, Borodin–Kostochka’s conjecture on  (P_{5},C_{4}) -free graphs, J. Appl. Math. Comput. 65 (2021) 877–884.
2239: 
2240: 
2241:       
2242: 
2243: [20]
2244: 
2245: U. K. Gupta, D. Pradhan, Strengthening Brooks’ chromatic bound on  P_{6} -free graphs, Discrete Appl. Math. 342 (2024) 334–346.
2246: 
2247: 
2263: 
2264: [23]
2265: 
2266: K. Lan, X. Lin, Borodin-Kostochka conjecture holds for  \overline{K_{1,3}} -free graphs, Discrete Appl. Math. 356 (2024) 263–268.
2267: 
2268: 
2269:       
2270: 
2271: [24]
2272: 
2273: K. Lan, F. Liu, Y. Zhou, Borodin-Kostochka conjecture on  \{P_{2}\cup P_{3},C_{4}\} -free graphs, Graphs Combin. 40 (2024) 123.
2274: 
2275: 
2276:       
2277: 
2278: [25]
2279: 
2280: B. Reed, A strengthening of Brooks’ theorem, J. Combin. Theory Ser. B 76 (1999) 136–149.
2281: 
2282: 
2284: 
2285: [26]
2286: 
2287: D. Wu, R. Wu, Borodin–Kostochka conjecture for a family of  P_{6} -free graphs, Acta Math. Appl. Sin. Engl. Ser. (2025). 
2288: 
2289:       
2290: 
2291: [27]
2292: 
2293: Q. Wu, J. Yang, On the chromatic number of (bull, diamond)-free graphs, Discuss. Math. Graph Theory 46 (2026) 443–449.
2294: 
2295: 
2296:     

## 376073 Bollobás–Erdős–Tuza conjecture on transversals of maximum independent sets
175: 
176: 7.1 Graphs with large and small values of  \beta(G) 
177: 
178: 7.2 The strong conjecture
179: 
180: 
181: A Appendix
182: 
183: References
184: 
185: 
186: 
187: 
218: Abstract
219:     
220: 
221: Fix a constant  c  with  0<c<1 . We say a graph  G  on  n  vertices is  c -hollow if every maximal independent set of  G  has size at least  cn . Denote by  \tau(G)  the size of a smallest set of vertices  T\subseteq V(G)  such that every maximal independent set in  G  intersects  T , i.e.,  T  is a transversal for the family of maximal independent sets. In 1991, Bollobás, Erdős, and Tuza conjectured that if  G  is  c -hollow, then  \tau(G)=o(n) . Using a random construction, we show there exist  c -hollow graphs with  \tau(G)=\Omega\left(\frac{n^{1/3}}{\log n}\right) , establishing the first nontrivial lower bound constraining the conjecture and complementing a closely related lower bound due to Alon for maximum independent sets. We also show the conjecture holds in a strong form for the class of cographs and split graphs.
222:   
223: 
224: 
225: 
226: 1 Introduction
227: 
228: 
229: 
230: 1.1 Background
280: 
281: 
282: 
283: The following conjecture is the focus of this paper.
284: 
285: 
286: 
287: Conjecture 1.1 (Bollobás, Erdős, Tuza 1991).
288: 
289: 
290: 
291: Let  0<c<1  be a constant. If  G  is a  c -hollow graph on  n  vertices, then  \tau(G)=o(n) .
292: 
293: 
294: 
295: 
296: 
297: This question appears to have been first raised in 1991 by Bollobás, Erdős, and Tuza in [9] and was later discussed in [7, p.52], although the terminology “ c -hollow” is not used there. Similar problems were also proposed in the 1992 paper [8] of Erdős, Tuza, and Gallai. Unpacking the  o(n)  notation, the conjecture is equivalent to the statement: for every  c\in(0,1)  and every  \epsilon>0 , there exists some  N=N(c,\epsilon)  such that if  G  is a  c -hollow graph on  n\geq N  vertices, then  \tau(G)\leq\epsilon n . So, it is conjectured that large  c -hollow graphs admit sublinear-sized (in  n ) transversals for  \operatorname{MIS}(G) .
298: 
299: 
300: 
301: 
302: We now give a few remarks illustrating why one might expect small MIS transversals in general for  c -hollow graphs.
303: 
304: 
305: 
306: Remark 1.4.
331: 
332: 
333: 
334: We know of no published results directly concerning Conjecture 1.1. However, the following closely related conjecture by Bollobás, Erdős, and Tuza in the early 1990s has received recent attention and is discussed in [7, 9]. The independence number of  G , denoted  \alpha(G) , is the size of a largest independent set of  G . We say that  I\subseteq V(G)  is a maximum independent set if  |I|=\alpha(G) .
335: 
336: 
337: 
338: Conjecture 1.2 (Bollobás, Erdős, and Tuza).
339: 
340: 
341: 
342: Let  0<c<1  be a constant. Let  h(G)  denote the size of a smallest hitting set for the collection of maximum independent sets of  G . If  G  is a graph on  n  vertices with  \alpha(G)\geq cn , then  h(G)=o(n) .
343: 
344: 
345: 
346: 
347: 
348: We remark that this “maximum conjecture” is neither a direct strengthening nor weakening of Conjecture 1.1. On the one hand, the maximum conjecture is only concerned with hitting the maximum independent sets, which is a strict subset of  \operatorname{MIS}(G)  in general. On the other hand, the hypothesis in Conjecture 1.1 that  G  is  c -hollow is much stronger than only assuming  \alpha(G)\geq cn . In 2021, Alon ([4]) observed that an old result of Hajnal ([12]) implies  h(G)=1  when  \alpha(G)>\frac{n}{2} . Combining Hajnal’s result with the container method, Alon showed that if  G  is regular and  \alpha(G)\geq(\frac{1}{4}+\epsilon)n , then  h(G)=O(\sqrt{n\log n}) . Alon also gave a construction with  h(G)=\Theta(\sqrt{n})  and  \alpha(G)\geq n/4 ; this is the largest known value for  h(G)  when  \alpha(G)=\Omega(n) . Significant progress on this question occurred in the next few years. First, Hajebi, Li, and Spirkl ([11]) showed that if  G  contains no induced  P_{5} , then  h(G)  is bounded above by a function of the clique number  \omega(G) . Next, Ai, Liu, Xu, and Zhou ([1]) showed that if  G  contains no induced matching of size  t , then  h(G)\leq\omega(G)^{3t-3+o(1)} . Cheng, Huang, Rong, and Xu ([5]) showed Conjecture 1.2 holds in several geometric graph families satisfying a certain “locally sparse” condition. In particular, they showed  h(G)=O(\frac{n}{\log n})  for even-hole-free graphs with  \alpha(G)=\Omega(n) . As a follow-up, Cheng and Xu showed in [6] that  h(G)=o(n)  for  K_{s,t} -free graphs with  \alpha(G)=\Omega(n)  using an elegant probabilistic argument. It is unclear if the methods of these publications can illuminate Conjecture 1.1, since the arguments are tailored to analyze maximum independent sets.
349: 
350: 
351: 
352: 
353: 1.2 Results and organization
354: 
355: 
356: 
357: 
358: Our main result is a lower bound construction constraining Conjecture 1.1.
359: 
360: 
361: 
362: Theorem 1.7.
363: 
364: 
365: 
366: Let  0<c<1  be a constant. There exists a  c -hollow graph  G  on  n  vertices with  \tau(G)=\Omega\left(\frac{n^{1/3}}{\log n}\right) .
367: 
369: 
370: 
371: 
372: Therefore, the  o(n)  in Conjecture 1.1 cannot be made asymptotically lower than  \frac{n^{1/3}}{\log n} . The idea behind the construction is to build a graph  G  where  |\operatorname{MIS}(G)|  is large and  \operatorname{MIS}(G)  resembles a uniformly distributed random set system. Alon showed in [3] that  k -uniform hypergraphs with uniformly random edges have large transversal numbers. Unlike Alon’s hypergraphs, the random MIS’s in our construction will only be approximately independent, enabling the application of Janson’s inequalities ([14]).
373: 
374: 
375: 
376: 
377: Next, we prove Conjecture 1.1 holds in a strong form for cographs and split graphs. A graph is a cograph if it contains no induced path on 4 vertices. Disjoint unions of cliques and complete multipartite graphs are examples of cographs. We denote by  i(G)  the size of a smallest MIS of a graph  G , i.e.,  c=i(G)/n  is the largest value so that  G  is  c -hollow. Equivalently,  i(G)  is the size of a smallest independent dominating set of  G . In 1990, Tuza proved a strong upper bound on  \tau(G)  for some graphs arising as complements of chordal graphs. We have restated Tuza’s theorem, as it was originally formulated in terms of cliques.
378: 
379: 
380: 
381: Theorem 1.8 (Tuza [19]).
382: 
383: 
384: 
385: If  \overline{G}  is strongly chordal, then  \tau(G)\leq\frac{n}{i(G)} . Moreover,  \tau(G)\leq\frac{n}{i(G)}  if  \overline{G}  is chordal and  i(G)=3 .
386: 
468: 
469: 
470: 
471: Given a graph  G  on  n  vertices, we define the parameter  \beta(G)=\frac{\tau(G)i(G)}{n} . The parameter  \beta(G)  behaves nicely under disjoint unions and joins (see Section 5) and it allows for a reformulation of Conjecture 1.1 (see Section 7).
472: 
473: 
474: 
475: 
476: 
477: In our constructions for Theorem 1.7 and 1.2, we employ standard probabilistic arguments. We refer the reader to [2] for more explanations and examples of probabilistic techniques in combinatorics. Given a sequence of events  \{A_{n}\}_{n\in\mathbb{N}}  in associated probability spaces  (\Omega_{n},\mathcal{A}_{n},\mathbb{P}_{n})_{n\in\mathbb{N}} , we say that  A_{n}  holds with high probability (whp) if  \mathbb{P}_{n}(A_{n})=1-o_{n\to\infty}(1) . When referring to random variables  X_{1},X_{2},\dots,X_{n} , we use iid as shorthand for independent and identically distributed. We will need the following special case of Hoeffding’s inequality.
478: 
479: 
480: 
1244: 
1245: 
1246: 
1247: Conjecture 1.1 remains wide open in general. The construction in Theorem 1.7 shows that one cannot hope to show  \tau(G)=o\left(n^{1/3-\epsilon}\right)  for general  c -hollow graphs. In the next two subsections, we propose further directions of study.
1248: 
1249: 
1250: 
1251: 7.1 Graphs with large and small values of  \beta(G)  
1252: 
1253: 
1254: 
1255: 
1256: Recall that  i(G)  is the size of a smallest MIS in  G  and  \beta(G)\coloneqq\frac{\tau(G)i(G)}{n} . Conjecture 1.1 can be reformulated as follows.
1257: 
1258: 
1259: 
1260: Conjecture 7.1 (Reformulation of Conjecture 1.1).
1261: 
1262: 
1263: 
1264: For all graphs  G  on  n  vertices,  \beta(G)=o(n) . Note that this trivially holds when  i(G)=o(n) , i.e., when  G  is not  c -hollow.
1265: 
1266: 
1267: 
1268: 
1269: 
1300: 
1301: 
1302: 
1303: 7.2 The strong conjecture
1304: 
1305: 
1306: 
1307: 
1308: Conjecture 1.1 asserts that  c -hollow graphs admit  o(n) -sized transversals for  \operatorname{MIS}(G) . Conjecture 1.2 (the “maximum conjecture”) asserts that graphs with  \alpha(G)\geq cn  admit  o(n) -sized transversals for the collection of maximum independent sets. We tentatively conjecture the following.
1309: 
1310: 
1311: 
1312: Conjecture 7.2 (Strong conjecture).
1313: 
1314: 
1315: 
1316: Let  0<c<1  be a constant. All graphs  G  on  n  vertices admit  o(n) -sized transversals for the set of large MIS’s, i.e.,
1317: 
1318: 
1319: 
1320: 
1321:  \operatorname{MIS}_{\text{large}}(G)=\{I\in\operatorname{MIS}(G):|I|\geq cn\}. 
1326: 
1327: 
1328: 
1329: Note that Conjecture 7.2 implies both Conjecture 1.1 and Conjecture 1.2, earning its name. A counterexample to this strong conjecture would be helpful in mapping out the boundaries of what one could hope to prove regarding the other two conjectures.
1330: 
1331: 
1332: 
1333: 
1334: 
1335: Appendix A Appendix
1336: 
1337: 
1338: 
1622: [6]
1623: X. Cheng and Z. Xu (2025)
1624: 
1625: Bollobás-Erdős-Tuza conjecture for graphs with no induced  K_{s,t} .
1626: 
1627: Journal of Graph Theory 109 (4), pp. 514–517.
1628: 
1629: Cited by: §1.1.
1630: 
1631: 
1632: [7]
1633: F. Chung and R. Graham (1998)
1634: 

## 376106 Friedlander–Iwaniec Conjecture 2 on automorphic summatory errors
1: 
2: 
3: 
4: Counterexamples of Friedlander–Iwaniec dual sums conjecture
5: 
6: 
7: 
8:  
9: 
10: 
11:   // Restore the saved color scheme preference, or
12:   // enact the browser preference if "automatic", 
13:   // without expecting DOM load to have completed.
163: 
164: 1.4 The method and main results
165: 
166: 1.5 Remarks on Friedlander–Iwaniec Conjecture 2
167: 
168: 1.6 Organiztion
169: 
170: 1.7 Notation and convention
171: 
172: 
173: 2 A sharp-endpoint sector lemma
174: 
175: 3 The zeta-product datum and the sharp conjecture
176: 
177: 
178: 3.1 Friedlander–Iwaniec normalization
179: 
180: 3.2 Proof of the endpoint lower bound
181: 
182: 3.3 Proof of Corollary 
183: 
184: 
199: 
200: 
201: 
202: Counterexamples of Friedlander–Iwaniec dual sums conjecture
203: 
204: 
205: 
206: Khai-Hoan Nguyen-Dang
207: 
208: Address: Morningside Center of Mathematics, Chinese Academy of Sciences, No. 55 Zhongguancun East Road, Beijing 100190, China
209: 
210: Email address: khaihoann@gmail.com
211: 
243: is determined by the archimedean weight  k  of the functional equation.
244:     
245: 
246: Their Conjecture 1 predicts that, for every  \varepsilon>0 ,
247:     
248: 
249: 
250: 
251: 
252:  \mathcal{B}_{\ell,D}(x,N)\ll_{\varepsilon,\boldsymbol{\kappa}}(DNx)^{\varepsilon}, 
253: 
254: 
255:     
281: 
282: 
283: 
284: Key words and phrases: Friedlander–Iwaniec conjecture, nonlinear dual sums, sharp truncation, endpoint resonance, divisor functions, automorphic  L -functions
285: 
286: 
287: 2020 Mathematics Subject ClassificationPrimary 11M41, 11L07; Secondary 11N37, 11F66
288: 
289: 
290: 
291: 1. Introduction
292: 
293: 
466: 
467: 
468: 
469: Friedlander and Iwaniec formulate the following conjecture.
470: 
471: 
472: 
473: Conjecture 1.1 (Friedlander–Iwaniec Conjecture 1).
474: 
475: 
476: 
477: For every  \varepsilon>0  and every automorphic series  B(s)  in their
478: framework, with the automorphic datum fixed,
479: 
480: 
481: 
482: (1.9)
489: 
490: 
491: 
492: We explain why the conjecture is hard at first glance. The assumed coefficient bound  b(n)\ll_{\eta}n^{\eta}  gives only
493: 
494: 
495: 
496: (1.10)
497: 
498:  |\mathcal{B}_{\ell,D}(x,N)|\leq\sum_{n\leq N}|b(n)|n^{-\beta_{m}}\ll_{\eta}N^{1-\beta_{m}+\eta}=N^{\theta_{m}+\eta}. 
499: 
500: 
501: 
502: Conjecture 1.1 asks that the entire positive power
503:  N^{\theta_{m}}  be replaced by a subpower factor. A heuristic provides limited motivation. For example, if
504:  0<\eta<1/(2m) , then
505: 
506: 
507: 
508: 
509:  \sum_{n\geq 1}|b(n)|^{2}n^{-2\beta_{m}}\ll_{\eta}\sum_{n\geq 1}n^{-1-1/m+2\eta}<\infty. 
510: 
511: 
553: equation of a new type, and a detailed description of its poles and residues
554: [12, (1.1), Theorems 2–3]. These results clarify the analytic structure of
555: the nonlinear twist but do not estimate every sharp partial sum in
556: Conjecture 1.1. Lin and Sun obtain nontrivial estimates for smoothly weighted nonlinear
557: twists attached to  \mathrm{GL}_{3}\times\mathrm{GL}_{2}  and derive sharp-cut
558: consequences in specified parameter ranges
559: [17, Theorem 1.1 and Corollary 1.2]. These results are
560: substantial, but they do not furnish a subpower estimate uniformly as required by Conjecture 1.1.
561: 
562: 
563: 
564: 
565: 1.4. The method and main results
566: 
567: 
568: 
569: 
570: We test Conjecture 1.1 on
571: 
572: 
573: 
574: 
575:  A(s)=B(s)=\zeta(s)^{m}. 
576: 
577: 
578: 
579: Its coefficients are the  m -fold divisor numbers
686: 
687: 
688: 
689: A positive value of  \Delta_{m}(a)  gives a power-sized obstruction to any uniform subpower estimate, hence produces counterexamples for the conjecture 1.1.
690: 
691: 
692: 
693: Corollary 1.3.
694: 
695: 
696: 
697: The following statements hold.
698: 
738: 
739: 
740: 
741: Thus the Conjecture 1 fails even in the printed
742: range  1\leq N\leq x .
743: 
744: 
745: (iii) 
746: 
747: 
748: 
749: Let  m\geq 5 . One may take
750: 
799:  w(\pi m)^{-1/2}D^{1/(2m)} . The last formula on p. 499, gives  w\left(\frac{2Q}{\pi m}\right)^{1/2}=\frac{wD^{1/(2m)}}{\pi\sqrt{m}}.  Thus the printed statement contains an extraneous factor  \sqrt{\pi} . The
800: same discrepancy persists in the printed degree-two specialization, and the
801: typo is recorded explicitly in [15, p. 835, footnote 2]. This fixed
802: nonzero factor has no effect on the sharp-sum conjecture or on any exponent
803: below. Clozel and Sarnak further explain that a general archimedean analysis
804: may carry two leading constants rather than a single cosine; see
805: [3, Hypothesis 2.1, Lemma 2.1, and (2.30)]. For the datum
806:  \zeta(s)^{m} , all gamma parameters are real and zero, so the cosine form is
807: valid. The two-frequency version is treated in Remark 2.3.
808: 
809: 
810: 
811: 
812: 
813: 1.5. Remarks on Friedlander–Iwaniec Conjecture 2
814: 
815: 
816: 
817: 
818: Set
819: 
820: 
821: 
822: 
828: 
829: 
830: 
831: Conjecture 1.6 (Friedlander–Iwaniec Conjecture 2).
832: 
833: 
834: 
835: Let  A(s)  be an automorphic series of degree  m  and conductor  D 
836: in the Friedlander–Iwaniec framework. Then, for every
837:  \varepsilon>0 ,
838: 
839: 
840: 
861: 
862: 
863: see [6, p. 500]. They propose to deduce
864: Conjecture 1.6 from Conjecture 1.1, after
865: relaxing the printed condition  N\leq x , by choosing
866: 
867: 
868: 
869: 
870:  N\asymp D^{1/2}x^{(m-1)/2}. 
871: 
872: 
873: 
901: 
902: see [6, Proposition 1.1 and Theorem 4.2].
903: The counterexamples in the present paper invalidate the proposed
904: uniform sharp-dual-sum route to Conjecture 1.6, but do not
905: themselves disprove Conjecture 1.6. For  A(s)=\zeta(s)^{m} , one has
906: 
907: 
908: 
909: 
910:  R_{A}(x)=xP_{m-1}(\log x), 
911: 
912: 
913: 
914: with  P_{m-1}  a polynomial of degree  m-1 , and
915: Conjecture 1.6 becomes the Piltz divisor conjecture
916: 
917: 
918: 
919: 
920:  \Delta_{m}(x):=\sum_{n\leq x}d_{m}(n)-xP_{m-1}(\log x)\ll_{m,\varepsilon}x^{(m-1)/(2m)+\varepsilon}. 
921: 
922: 
923: 
924: For  m=2 , Hardy proved
965: 
966: There is a parallel degree-two cuspidal problem. For the normalized
967: Hecke eigenvalues  \lambda_{f}(n)  of a holomorphic Hecke newform,
968: Conjecture 1.6 predicts
969: 
970: 
971: 
972: 
973:  \sum_{n\leq x}\lambda_{f}(n)\ll_{f,\varepsilon}x^{1/4+\varepsilon}. 
974: 
975: 
976: 
977: In the newform setting treated by Wu,
1002: 
1003: As a higher-degree example, let  \pi  be a  \mathrm{GL}_{3} 
1004: Hecke–Maass cusp form and let  f  be a  \mathrm{GL}_{2}  holomorphic
1005: or Maass cusp form. Under the Ramanujan–Petersson conjecture,
1006: Lin and Sun prove
1007: 
1008: 
1009: 
1010: 
1011:  \sum_{r^{2}n\leq x}\lambda_{\pi}(r,n)\lambda_{f}(n)\ll_{\pi,f,\varepsilon}x^{5/7-1/364+\varepsilon}; 
1012: 
1013: 
1014: 
1015: see [17, Corollary 1.4]. This saves a power over the general
1016: Friedlander–Iwaniec exponent  5/7 , while
1017: Conjecture 1.6 predicts the exponent  5/12 .
1018: 
1019: 
1020: 
1021: 
1022: 1.6. Organiztion
1023: 
1024: 
1025: 
1026: 
1464: 
1465: 
1466: 
1467: 3. The zeta-product datum and the sharp conjecture
1468: 
1469: 
1470: 
1471: 3.1. Friedlander–Iwaniec normalization
1472: 
1473: 
1474: 
1475: 
1476: As in [6], we begin with coefficient bounds

## 376118 Bang-Jensen–DeVos–Mütze conjecture on strong tournaments in semicomplete digraphs
291: 
292: 
293: 
294: Inspired by this result, Jackson and Thomassen made the following conjecture for the case of vertex-connectivity. A digraph  D=(V,A)  is  \bm{k} -strong if it has at least  k+1  vertices and remains strong after the deletion of any subset of  k-1  vertices.
295: 
296: 
297: 
298: Conjecture 1.1.
299: 
300: 
301: 
302: [11]
303: Every  2k -strong digraph has a spanning  k -strong oriented subdigraph.
304: 
305: 
306: 
307: 
308: 
309: For  k=1  this follows from a result of Boesch and Tindell on strong orientations of mixed graphs [3] but the conjecture is open even for  k=2 , except for symmetric digraphs where Thomassen proved the conjecture [12]. For  k\geq 3 , Garamvölgyi et al. [6] show that such a bound exists: every  320k^{2} -connected undirected graph admits a  k -strong orientation. This result applies to symmetric digraphs but does not extend to arbitrary digraphs.
310: 
311: 
312: 
313: 
314: While  2k -edge-connectivity is clearly necessary in Theorem 1.1, implying that  2k -arc-connectivity is best possible already for symmetric digraphs, the only lower bound on the arc-connectivity that holds for all digraphs having a  k -arc-strong orientation is  k , since the digraph may already be oriented. Thus, it is interesting to consider when  2k -arc-connectivity is really necessary.
315: 
316: 
317: 
318: Remark 1.1.
394: 
395: 
396: 
397: Theorem 1.3 also provides support to the following conjecture, by showing that the claim holds when we replace vertex-connectivity by arc-connectivity. A digraph is  k -strong if it has at least  k+1  vertices and remains strongly connected after the deletion of any subset of size  k-1  of its vertices.
398: 
399: 
400: 
401: Conjecture 1.2.
402: 
403: 
404: 
405: [2]
406: Every  (2k-1) -strong semicomplete digraph on at least  2k+1  vertices contains a spanning  k -strong tournament.
407: 
408: 
409: 
410: 

## 376125 Fixed-degree NP-completeness conjecture for non-synchronizing colorings
255:  w\in\Sigma^{*}  such that  |\delta_{\ell}(Q,w)|=1 ; any such word is called a
256: reset (or synchronizing) word.
257: Synchronizing automata have been extensively studied, largely motivated by the
258: celebrated Černý conjecture, which asserts that every synchronizing
259: automaton with  n  states admits a reset word of length at most  (n-1)^{2} 
260: (see [12]).
261: Over the years, this conjecture has stimulated a vast literature on
262: synchronizing automata, including algorithms for computing short reset words,
263: proofs of the conjecture for important classes of automata, and connections
264: with coding theory, symbolic dynamics, and the Road Coloring Problem; see, for
265: instance,
266: [3, 8, 15, 16, 24, Ro18Adv, SteinbEJC, Steinb, Trah, 31, 32, 14, 10, 9].
267: For a recent survey of the classes of automata for which the Černý
268: conjecture is known to hold, see [33]. Besides the Černý conjecture, synchronization has also been extensively studied from the perspective of permutation groups through the theory of synchronizing groups. This line of research, developed by Araújo, Cameron, Steinberg and collaborators, has revealed deep connections between automata, permutation groups, graph endomorphisms and algebraic combinatorics; see, for instance,
269: [7, 5, 6].
270: 
271: 
272: 
273: 
274: The present paper approaches synchronization from a graph-theoretic viewpoint by regarding an automaton as a coloring of a  k -out graph. This viewpoint is also natural from symbolic dynamics, since a coloring is precisely a complete right-resolving edge-labeling, and therefore determines a right-resolving presentation of a sofic shift; see, for instance, [27]. This perspective lies at the origin of the Road Coloring Problem of Adler, Goodwyn, and Weiss [2], which asked whether every primitive  k -out graph admits at least one synchronizing coloring. Trahtman’s theorem answers this affirmatively [31]: primitivity (strong connectivity and aperiodicity) is exactly the right unlabeled condition guaranteeing the existence of a synchronizing labeling. See also Volkov’s survey [34]. In this paper we study a different aspect of the same setting. Rather than asking for the existence of some synchronizing coloring, we ask to what extent synchronization is forced by the unlabeled directed skeleton itself. From the symbolic-dynamical viewpoint, each coloring  \ell  yields a deterministic presentation  (G,\ell) , equivalently a  1 –block factor of the edge shift of  G , and varying  \ell  amounts to varying the symbolic coding of the same underlying Markov shift. This suggests measuring how typical synchronization is among all such codings. Let  \mathcal{C}(G)  denote the set of all colorings of  G . Following [21], we define the synchronizing ratio
275: 
276: 
277: 
280: 
281: 
282: 
283: The main protagonists of this paper are the totally synchronizing graphs introduced in [21]: we say that  G  is totally synchronizing if  \mathrm{SynRatio}(G)=1 , that is, if every coloring of  G  is synchronizing. This is an extremal robustness property: synchronization is not a consequence of a special choice of labels, but an invariant of the underlying directed graph. The study of synchronizing ratios suggests that total synchronization should be far from exceptional. In [21], Gusev and Szykuła propose two complementary conjectures. The first predicts a uniform lower bound for primitive  k -out graphs  \mathrm{SynRatio}(G)\ \geq\ \frac{k-1}{k},  up to a single explicit small exception. The second predicts that for each fixed  k\geq 2 , a random primitive  k -out graph on  n  vertices is totally synchronizing with probability tending to  1  as  n\to\infty . In this sense, totally synchronizing graphs should represent the typical behaviour, while graphs supporting many non-synchronizing colorings should be rare. Somewhat paradoxically, despite this apparent abundance, a satisfactory structural characterization of totally synchronizing graphs seems out of reach at present. Beyond sufficient criteria (for instance those based on Perron–Frobenius data in [20]), there is currently no general description in purely graph-theoretic terms for the class of totally synchronizing graphs.
284: 
285: 
286: 
287: 
288: In this paper we continue the study of totally synchronizing  k -out graphs from a graph-theoretic viewpoint.
289: We focus on two kinds of structure already present in the unlabeled graph: symmetries and quotients.
290: The symmetry part gives graph-level obstructions to total synchronization.
291: Our first main result shows that if  G  is strongly connected and totally synchronizing, then  \Aut(G)  contains no semiregular element (Theorem 3.9).
292: As an immediate consequence, if  G  is strongly connected and  |\Aut(G)|  is divisible by a prime  p>k , then  G  is not totally synchronizing (Corollary 3.11).
1265: 
1266: 
1267: 
1268: It is interesting to note the connection with a classical conjecture of Marušič [28], also called the Polycirculant Conjecture, which asserts that every finite vertex-transitive (di)graph admits a nontrivial semiregular automorphism. This conjecture imposes vertex-transitivity on the structure of the automorphism group. However, it does not apply in our setting, since totally synchronizing graphs are never vertex-transitive. In a private communication and in a conference talk [29], Gusev and Pribavkina observed the following.
1269: 
1270: 
1271: 
1272: Proposition 3.12.
1273: 
1274: 
1275: 
1276: Let  G  be a strongly connected  k -out graph. If  \End(G)  is vertex transitive on  V(G) , then  G  is not totally synchronizing.
1277: 
2420: 
2421: 
2422: so the expected number of vertices with in-degree  0  is  \sim ne^{-k} , and therefore  G  fails to be strongly connected with high
2423: probability as  n\to\infty . Moreover, if a  k -out digraph  G  is not strongly connected, then it is automatically nontrivially lumpable. Therefore, conditioning on strong connectivity is natural when studying typical total simplicity. We formulate the following conjecture.
2424: 
2425: 
2426: 
2427: Conjecture 4.6.
2428: 
2429: 
2430: 
2431: Fix  k\geq 2 . Let  G  be a uniformly random  k -out graph on  n  vertices, and write  \mathrm{SCC}  for the event that  G 
2432: is strongly connected. Then
2433: 
2434: 
2435: 
2436: 
3060: 
3061: 
3062: 
3063: Conjecture 5.7 ([22]).
3064: 
3065: 
3066: 
3067: The counting problem  G\mapsto\#\mathrm{NSC}(G)  is #P-complete on the class of primitive  k -out graphs. Moreover, this remains #P-complete for fixed out-degree  k , already for  k=2 .
3068: 
3069: 
3070: 
3071: 
3072: 
3073: We were not able to prove Conjecture 5.7, but we can relate  \#\mathrm{NSC}  to a classical counting problem on regular bipartite simple graphs. In a  k -regular bipartite simple graph, a decomposition of the edge set into  k  perfect matchings is the same object as a proper edge- k -coloring; such decompositions are also
3074: known as  1 -factorizations. Exact counting of  1 -factorizations is widely believed to be computationally hard, and the precise complexity
3075: status of counting edge- k -colorings of bipartite graphs (equivalently,  1 -factorizations in the  k -regular case) is currently open [23]. Our contribution here is a
3076: tight reduction showing that, on prime-size strongly connected Eulerian graphs, counting non-synchronizing colorings
3077: is essentially the same as counting permutation colorings, and the latter coincides with counting labeled
3078:  1 -factorizations of the associated bipartite graph.
3079: 
3080: 
3081: 
3082: 
3245: 
3246: 
3247: 
3248: This paper is dedicated to the memory of the late Elena Pribavkina, whose work on synchronizing automata, the Černý conjecture, and totally synchronizing digraphs influenced the present study.
3249: 
3250: The authors are members of the National Research Group GNSAGA
3251: (Gruppo Nazionale per le Strutture Algebriche, Geometriche e le loro
3252: Applicazioni) of INdAM.
3253: 
3254: 
3255: 
3256: 
3257: References
3412: [14]
3413: H. Don (2015)
3414: 
3415: The Černý conjecture and 1-contracting automata.
3416: 
3417: Electronic Journal of Combinatorics 23, pp. 3.
3418: 
3419: Cited by: §1.
3420: 
3421: 
3422: [15]
3423: L. Dubuc (1998)
3424: 
3425: Sur les automates circulaires et la conjecture de Černý.
3426: 
3427: RAIRO-Theor. Inf. Appl. 32 (1-3), pp. 21–34.
3428: 
3429: External Links: Document
3430: 
3431: Cited by: §1.
3432: 
3433: 
3434: [16]
3517: 
3518: External Links: Link
3519: 
3520: Cited by: Conjecture 5.7.
3521: 
3522: 
3523: [23]
3524: L. Hong and I. Miklós (2023)
3525: 
3526: A markov chain on the solution space of edge colorings of bipartite graphs.
3527: 
3528: Discrete Applied Mathematics 332, pp. 7–22.
3529: 
3643: [33]
3644: M. V. Volkov (2025)
3645: 
3646: List of results on the Černý conjecture and reset thresholds for synchronizing automata.
3647: 
3648: External Links: 2508.15655,
3649: Link
3650: 
3651: Cited by: §1.
3652: 
3653: 
3654: [34]
3655: M.V. Volkov (2008)
3656: 
3657: Synchronizing automata and the Černý conjecture.
3658: 
3659: In Language and Automata Theory and Applications (LATA 2008),
3660: 
3661: Lecture Notes in Computer Science, Vol. 5196, pp. 11–27.
3662: 
3663: External Links: Document
3664: 
3665: Cited by: §1.
3666: 

## 376134 Akiyama–Watanabe–Albertson–Hass conjecture for bipartite planar graphs
213: Abstract
214:     
215: 
216: A feedback vertex set of a graph is a set of vertices whose deletion leaves a forest. In 2016, Dross, Montassier, and Pinlou conjectured that every planar graph  G  of girth at least  g  admits a feedback vertex set of size at most  e(G)/g . In this note, we confirm this conjecture by connecting this problem with signed graphs. The frustration index of a signed graph  (G,\Sigma)  is defined as the minimum number of negative edges among all signatures on  G  that are switching-equivalent to  \Sigma . Equivalently, it is the minimum number of edges whose deletion results in a balanced subgraph of  (G,\Sigma) . We show that the minimum size of a feedback vertex set of a planar graph is bounded above by the maximum frustration index over all signatures of the graph, and thereby provide a tight upper bound on the size of the minimum feedback vertex set, which resolves the conjecture of Dross, Montassier, and Pinlou (2016).
217:   
218: 
219: 
220: 
221: 
222: Keywords: Frustration index, feedback vertex set, planar graph,  T -join, ear decomposition.
223: 
224: 
225: 
237: 
238: 
239: 
240: For a given graph  G  and an integer  k , deciding whether  \mathrm{fvs}(G)\leq k  is NP-complete [18]. For any graph  G , we use  v(G)  and  e(G)  to denote its number of vertices and edges, respectively. Various results concern structural upper bounds on  \mathrm{fvs}(G)  for different graph classes. For planar graphs, a well-known conjecture of Albertson and Berman [2] states that every planar graph  G  has a feedback vertex set of size at most  \frac{v(G)}{2} .
241: 
242: 
243: 
244: Conjecture 1.1 (Albertson and Berman [2]).
245: 
246: 
247: 
248: Every planar graph  G  satisfies  \mathrm{fvs}(G)\leq\frac{v(G)}{2} .
249: 
250: 
251: 
252: 
253: 
254: This conjecture, if true, would be tight as witnessed by  K_{4} . Despite considerable effort, the best known general upper bound is  \mathrm{fvs}(G)\leq\frac{3v(G)}{5} , a consequence of Borodin’s result [6] that every planar graph admits an acyclic  5 -coloring. For triangle-free planar graphs, further improvements were obtained by Salavatipour [21], proving that  \mathrm{fvs}(G)\leq\frac{15v(G)-24}{32} , and Dross, Montassier, and Pinlou [10] showed that  \mathrm{fvs}(G)\leq\frac{5v(G)-7}{11} , and Le [17] improved it to  \mathrm{fvs}(G)\leq\frac{4v(G)}{9} . In the setting of triangle‑free planar graphs and even more so for bipartite planar graphs, the following conjecture naturally arises independently by Akiyama and Watanabe[1], and Albertson and Hass.
255: 
256: 
257: 
258: Conjecture 1.2 (Akiyama and Watanabe [1], and Albertson and Hass [3]).
259: 
260: 
261: 
262: Every bipartite planar graph  G  satisfies that  \mathrm{fvs}(G)\leq\frac{3v(G)}{8} .
263: 
264: 
265: 
266: 
267: 
268: For bipartite graphs, Alon [4] gave an upper bound  \mathrm{fvs}(G)\leq\left(\frac{1}{2}-e^{-bd^{2}}\right)v(G) , where  b  is a constant and  d  is the upper bound of the average degree of  G . This bound was subsequently improved by Conlon, Fox, and Sudakov [7] to  \mathrm{fvs}(G)\leq\left(\frac{1}{2}-(2^{7}d^{2})^{-4d}\right)v(G) . Meanwhile, Alon, Mubayi, and Thomas [5] proved that every triangle-free graph  G  satisfies  \mathrm{fvs}(G)\leq\frac{e(G)}{4} . The current best bound for Conjecture 1.2 is  \mathrm{fvs}(G)\leq\frac{3v(G)-3}{7} , due to Wang, Xie, and Yu [23].
269: 
270: 
271: 
272: 
273: More generally, planar graphs of large girth are also considered. For a connected planar graph  G  of girth at least  g , it is easy to see that  \mathrm{fvs}(G)<\frac{2e(G)}{g} . Dross, Montassier, and Pinlou [9] provided a non-trivial bound of  \mathrm{fvs}(G)\leq\frac{4e(G)}{3g} , and proposed the following conjecture.
274: 
275: 
276: 
277: Conjecture 1.3 (Dross, Montassier, and Pinlou [9]).
278: 
279: 
280: 
281: Every planar graph  G  of girth at least  g  satisfies  \mathrm{fvs}(G)\leq\frac{e(G)}{g} .
282: 
283: 
284: 
285: 
286: 
287: A corresponding vertex-based bound of  \mathrm{fvs}(G)\leq\frac{v(G)-2}{g-2}  can be derived from Euler’s formula for planar graphs together with the girth condition, that is,  e(G)\leq\frac{g(v(G)-2)}{g-2} .
288: Conjecture 1.3 was subsequently confirmed in the case  g=5  by Kelly and Liu [14]. More precisely, they proved that every connected planar graph of girth at least  5  satisfies  \mathrm{fvs}(G)\leq\frac{2e(G)-v(G)+2}{7}, 
289: which implies both  \mathrm{fvs}(G)\leq\frac{e(G)}{5}  and  \mathrm{fvs}(G)\leq\frac{v(G)-2}{3} . Tang and Diao [22] proved that every connected outerplanar graph  G  of girth  g  satisfies
290:  \mathrm{fvs}(G)\leq\frac{e(G)}{g}, 
291: with equality if and only if  G  is a cycle of length  g . Ma and Ren [19] proved that for  g\geq 8 , if a planar graph  G  has girth at least  2(g-4)^{2}+6 , then  \mathrm{fvs}(G)\leq\frac{e(G)}{g} ; they also established the following bounds:  \mathrm{fvs}(G)\leq\frac{3v(G)-6}{8}  for planar graphs of girth at least  6 , and  \mathrm{fvs}(G)\leq\frac{3v(G)-6}{10} 
292: for planar graphs of girth at least  8 . Most recently, Dreyer, Pinlou, and Valicov [8] investigated an analogue of the problem for planar digraphs with prescribed digirth, and obtained the upper bound  \mathrm{fvs}(D)\leq\frac{v(D)-2}{g-2}  for every planar digraph  D  of digirth  g\geq 3 .
293: 
294: 
295: 
296: 
297: In this note, we confirm Conjecture 1.3. The main result is stated as follows.
298: 
299: 
300: 
301: Theorem 1.4.
302: 
303: 
304: 
305: Let  G  be a planar graph of girth at least  g  and with  b  bridges. Then
306: 
840: [2]
841: 
842: M. O. Albertson and D. M. Berman.
843: A conjecture on planar graphs.
844: In: J. A. Bondy and U. S. R. Murty (eds.),
845: Graph Theory and Related Topics,
846: Academic Press, New York, 1979, p. 357.
847: 
848: 
849:       
850: 
851: [3]
852: 

## 376135 Dross–Montassier–Pinlou conjecture on feedback vertex sets in large-girth planar graphs
213: Abstract
214:     
215: 
216: A feedback vertex set of a graph is a set of vertices whose deletion leaves a forest. In 2016, Dross, Montassier, and Pinlou conjectured that every planar graph  G  of girth at least  g  admits a feedback vertex set of size at most  e(G)/g . In this note, we confirm this conjecture by connecting this problem with signed graphs. The frustration index of a signed graph  (G,\Sigma)  is defined as the minimum number of negative edges among all signatures on  G  that are switching-equivalent to  \Sigma . Equivalently, it is the minimum number of edges whose deletion results in a balanced subgraph of  (G,\Sigma) . We show that the minimum size of a feedback vertex set of a planar graph is bounded above by the maximum frustration index over all signatures of the graph, and thereby provide a tight upper bound on the size of the minimum feedback vertex set, which resolves the conjecture of Dross, Montassier, and Pinlou (2016).
217:   
218: 
219: 
220: 
221: 
222: Keywords: Frustration index, feedback vertex set, planar graph,  T -join, ear decomposition.
223: 
224: 
225: 
237: 
238: 
239: 
240: For a given graph  G  and an integer  k , deciding whether  \mathrm{fvs}(G)\leq k  is NP-complete [18]. For any graph  G , we use  v(G)  and  e(G)  to denote its number of vertices and edges, respectively. Various results concern structural upper bounds on  \mathrm{fvs}(G)  for different graph classes. For planar graphs, a well-known conjecture of Albertson and Berman [2] states that every planar graph  G  has a feedback vertex set of size at most  \frac{v(G)}{2} .
241: 
242: 
243: 
244: Conjecture 1.1 (Albertson and Berman [2]).
245: 
246: 
247: 
248: Every planar graph  G  satisfies  \mathrm{fvs}(G)\leq\frac{v(G)}{2} .
249: 
250: 
251: 
252: 
253: 
254: This conjecture, if true, would be tight as witnessed by  K_{4} . Despite considerable effort, the best known general upper bound is  \mathrm{fvs}(G)\leq\frac{3v(G)}{5} , a consequence of Borodin’s result [6] that every planar graph admits an acyclic  5 -coloring. For triangle-free planar graphs, further improvements were obtained by Salavatipour [21], proving that  \mathrm{fvs}(G)\leq\frac{15v(G)-24}{32} , and Dross, Montassier, and Pinlou [10] showed that  \mathrm{fvs}(G)\leq\frac{5v(G)-7}{11} , and Le [17] improved it to  \mathrm{fvs}(G)\leq\frac{4v(G)}{9} . In the setting of triangle‑free planar graphs and even more so for bipartite planar graphs, the following conjecture naturally arises independently by Akiyama and Watanabe[1], and Albertson and Hass.
255: 
256: 
257: 
258: Conjecture 1.2 (Akiyama and Watanabe [1], and Albertson and Hass [3]).
259: 
260: 
261: 
262: Every bipartite planar graph  G  satisfies that  \mathrm{fvs}(G)\leq\frac{3v(G)}{8} .
263: 
264: 
265: 
266: 
267: 
268: For bipartite graphs, Alon [4] gave an upper bound  \mathrm{fvs}(G)\leq\left(\frac{1}{2}-e^{-bd^{2}}\right)v(G) , where  b  is a constant and  d  is the upper bound of the average degree of  G . This bound was subsequently improved by Conlon, Fox, and Sudakov [7] to  \mathrm{fvs}(G)\leq\left(\frac{1}{2}-(2^{7}d^{2})^{-4d}\right)v(G) . Meanwhile, Alon, Mubayi, and Thomas [5] proved that every triangle-free graph  G  satisfies  \mathrm{fvs}(G)\leq\frac{e(G)}{4} . The current best bound for Conjecture 1.2 is  \mathrm{fvs}(G)\leq\frac{3v(G)-3}{7} , due to Wang, Xie, and Yu [23].
269: 
270: 
271: 
272: 
273: More generally, planar graphs of large girth are also considered. For a connected planar graph  G  of girth at least  g , it is easy to see that  \mathrm{fvs}(G)<\frac{2e(G)}{g} . Dross, Montassier, and Pinlou [9] provided a non-trivial bound of  \mathrm{fvs}(G)\leq\frac{4e(G)}{3g} , and proposed the following conjecture.
274: 
275: 
276: 
277: Conjecture 1.3 (Dross, Montassier, and Pinlou [9]).
278: 
279: 
280: 
281: Every planar graph  G  of girth at least  g  satisfies  \mathrm{fvs}(G)\leq\frac{e(G)}{g} .
282: 
283: 
284: 
285: 
286: 
287: A corresponding vertex-based bound of  \mathrm{fvs}(G)\leq\frac{v(G)-2}{g-2}  can be derived from Euler’s formula for planar graphs together with the girth condition, that is,  e(G)\leq\frac{g(v(G)-2)}{g-2} .
288: Conjecture 1.3 was subsequently confirmed in the case  g=5  by Kelly and Liu [14]. More precisely, they proved that every connected planar graph of girth at least  5  satisfies  \mathrm{fvs}(G)\leq\frac{2e(G)-v(G)+2}{7}, 
289: which implies both  \mathrm{fvs}(G)\leq\frac{e(G)}{5}  and  \mathrm{fvs}(G)\leq\frac{v(G)-2}{3} . Tang and Diao [22] proved that every connected outerplanar graph  G  of girth  g  satisfies
290:  \mathrm{fvs}(G)\leq\frac{e(G)}{g}, 
291: with equality if and only if  G  is a cycle of length  g . Ma and Ren [19] proved that for  g\geq 8 , if a planar graph  G  has girth at least  2(g-4)^{2}+6 , then  \mathrm{fvs}(G)\leq\frac{e(G)}{g} ; they also established the following bounds:  \mathrm{fvs}(G)\leq\frac{3v(G)-6}{8}  for planar graphs of girth at least  6 , and  \mathrm{fvs}(G)\leq\frac{3v(G)-6}{10} 
292: for planar graphs of girth at least  8 . Most recently, Dreyer, Pinlou, and Valicov [8] investigated an analogue of the problem for planar digraphs with prescribed digirth, and obtained the upper bound  \mathrm{fvs}(D)\leq\frac{v(D)-2}{g-2}  for every planar digraph  D  of digirth  g\geq 3 .
293: 
294: 
295: 
296: 
297: In this note, we confirm Conjecture 1.3. The main result is stated as follows.
298: 
299: 
300: 
301: Theorem 1.4.
302: 
303: 
304: 
305: Let  G  be a planar graph of girth at least  g  and with  b  bridges. Then
306: 
840: [2]
841: 
842: M. O. Albertson and D. M. Berman.
843: A conjecture on planar graphs.
844: In: J. A. Bondy and U. S. R. Murty (eds.),
845: Graph Theory and Related Topics,
846: Academic Press, New York, 1979, p. 357.
847: 
848: 
849:       
850: 
851: [3]
852: 

## 376146 Yau's pinching problem for sectional and normalized scalar curvature
251: 
252: 
253: 
254: Conjecture 1.1 (Yau’s pinching problem).
255: 
256: 
257: 
258: Let  (M^{n},g)  be a closed, simply connected Riemannian manifold of dimension  n\geq 4 . If
259: 
260: 
261: 
262: 
263:  K_{\min}>\frac{n-1}{n+2}S_{0}, 
279: 
280: 
281: 
282: so  \mathbb{CP}^{n/2}  lies exactly at the endpoint. Gu and Xu proved the sphere conclusion under the stronger coefficient  n(n-1)/(n^{2}-n+6) , [GX12]. Li recently improved that coefficient to  n(n-1)/(n^{2}-n+12) , cf. [Li26]. In dimension  4 , Yau’s conjecture was first proved by Costa and Ribeiro Jr. under a weaker curvature assumption [CR14]. Li’s strict coefficient agrees with Yau’s hence recover the dimension  4  case. For every dimension  n\geq 5 , Li’s coefficient is larger than Yau’s.
283: 
284: 
285: 
286: 
287: Our argument belongs to the Bochner tradition for harmonic two-forms, beginning with the classical curvature term estimate of Gallot and Meyer [GM75]. Micallef and Wang obtained strong two-form consequences from nonnegative isotropic curvature [MW93], see also Seaman [Sea93]; modern algebraic treatments of Weitzenböck curvature terms include [Lab15], [BM22], [PW21], [NPW23]. Wan assumed an inequality involving Ricci and sectional curvatures [Wan14]. Ni and Wilking’s generalized Berger inequality for pinched flag curvature supplies the four-frame estimate used below, [NW10]. Their flag-curvature pinching is not an additional hypothesis of our theorem; only the pointwise algebraic estimate extracted from it is used.
288: 
289: 
290: 
291: 
292: Motivated by Yau’s conjecture, we consider the dimension-dependent constant:
293: 
294: 
295: 
296: 
297:  \beta_{n}=\begin{cases}\dfrac{n-1}{n+2},&n\ \text{even},\\[10.0pt]
298: \dfrac{n(n-3)}{n^{2}-6},&n\ \text{odd}.\end{cases} 
299: 
300: 
301: 

## 376188 Conjectured improved upper bound for the Heilbronn triangle problem
217: Combined with a previous result of Cohen, the author, and Zakharov, this solves the minimal distance problem.
218:     
219: 
220: The same construction also comes with an unexpected finite field consequence: for every  \varepsilon>0 , there exists a set of primes  q  of positive relative density for which  \mathbb{F}_{q}^{2}  contains an induced point-line matching of size  \gtrsim_{\varepsilon}q^{3/2-\varepsilon} . This disproves a conjecture of Hunter, the author, Verstraëte and Zhang.
221:   
222: 
223: 
224: 
225: 1. Introduction
226: 
227: 
228: 
229: 
413: 
414: 
415: 
416: When  q  is a square, the Hermitian unital gives an induced matching of size  q^{3/2} , showing that this estimate is sharp up, to lower-order terms. See for example [12] for a more elaborate discussion. For fields of prime order  q , the situation is significantly more mysterious. In [12, Theorem 1.2], Hunter–Pohoata–Verstraëte–Zhang used (5) to prove that  \operatorname{IM}(2,q)\gtrsim q^{1.2334\ldots}  holds for all primes  q , thereby establishing a separation between this problem and the closely related problem of determining the size of the largest clique in the Paley graph of prime order  q . Furthermore, in [12, Conjecture 10.2], the authors also subsequently conjectured that  \operatorname{IM}(2,q)\leq q^{3/2-c}  must hold for some absolute constant  c>0 , for all sufficiently large primes  q .
417: 
418: 
419: 
420: 
421: Using the construction behind Theorem 1.1, we can show that this conjecture is false, as originally stated.
422: 
423: 
424: 
425: Theorem 1.3.
426: 
427: 
428: 
429: For every  \varepsilon>0 , there is a set  \mathcal{Q}_{\varepsilon}  of rational
430: primes having positive relative density among the primes such that,
1537: 
1538: 
1539: 
1540: discussed in Section 1, discards a substantial amount of geometry. In this spirit, we would like to take the opportunity to formally state the following conjecture:
1541: 
1542: 
1543: 
1544: Conjecture 6.1.
1545: 
1546: 
1547: 
1548: There exists an absolute constant  c>0  such that
1549: 
1550: 
1551: 
1552: 
1553:  \Delta_{\mathrm{H}}(n)\lesssim n^{-7/6-c}. 
1614: 
1615: N. Alon, T. F. Bloom, W. T. Gowers, D. Litt, W. Sawin, A. Shankar,
1616: J. Tsimerman, V. Wang, and M. Matchett Wood,
1617: Remarks on the disproof of the unit distance conjecture,
1618: arXiv:2605.20695, 2026.
1619: 
1620: 
1621:       
1622: 
1623: [2]
1624: 
1625: R. Beigel and W. Gasarch,
1626: Square-difference-free sets of size
1653: [5]
1654: 
1655: T. F. Bloom, W. Sawin, C. Schildkraut, and D. Zhelezov,
1656: The sum–product conjecture is false for real numbers,
1657: arXiv:2605.28781, 2026.
1658: 
1659: 
1660:       
1661: 
1662: [6]
1663: 
1664: A. Cohen, C. Pohoata, and D. Zakharov,
1665: A new upper bound for the Heilbronn triangle problem,

## 376195 Andrews' local-minimum conjecture for coefficients of $v_1(q)$
1: 
2: 
3: 
4: Exceptional Sign Pairs in Oscillatory Asymptotics and Conjectures of Andrews
5: 
6: 
7: 
8:  
9: 
10:   // Restore the saved color scheme preference, or
11:   // enact the browser preference if "automatic", 
12:   // without expecting DOM load to have completed.
13:   //
176: 
177: 
178: 
179: Exceptional Sign Pairs in Oscillatory Asymptotics and Conjectures of Andrews
180: 
181: 
182: 
183: Jayashree Kalita
184: 
185: Address: Department of Mathematics,
186: Vanderbilt University, Nashville, Tennessee, United States
187: 
188: Email address: jayashree.kalita@vanderbilt.edu
197: Recent work of Kundu, Storzer, Wang, and the author established that the coefficients of these  q -series are alternating in sign except in a density-zero set.
198: We prove here that the exceptional indices where the alternating sign pattern fails occur infinitely often in a structured manner.
199: More precisely, we show that there exist infinitely many pairs of consecutive coefficients having the same sign, and that the magnitude of at least one coefficient in each pair is a local minimum of the sequence of absolute values of the coefficients.
200: Together with earlier results, this completes the resolution of Andrews’ conjectures and their analogs for all the  q -series in his original study.
201:   
202: 
203: 
204: 
205: 1. Introduction
206: 
207: 
208: 
209: 
241: 
242: 
243: 
244: Based on numerical evidence, Andrews made six conjectures on the coefficients of these  q -series.
245: His first two conjectures addressed the series  \sigma(q)  and stated that
246: 
247: 
248: 
249: 
250:  \limsup_{n\to\infty}\mathinner{\!\left\lvert S(n)\right\rvert}=\infty\text{ and }S(n)=0\text{ for infinitely many }n. 
251: 
252: 
253: 
254: Andrews–Dyson–Hickerson [1] famously proved these two conjectures, uncovering a remarkable connection between the coefficients of  \sigma(q)  and the arithmetic of  \mathbb{Q}(\sqrt{6}) .
255: This example has since influenced a large body of work, including Cohen’s [5] construction of a related Maaß wave form, Zwegers’ [13] theory of mock Maaß theta functions, Zagier’s [12] theory of quantum modular forms, and more recently, the work of Li–Roehrig [10].
256: 
257: 
258: 
259: 
260: For the  q -series  v_{1}(q),v_{2}(q),v_{3}(q),\text{ and }v_{4}(q) , Andrews observed what he described as “great sign regularity.”
261: More precisely, Andrews made the following conjectures for  v_{1}(q) .
262: He stated that Conjecture 3 [3] and appropriate analogs of Conjectures 4–6 [3] hold for  v_{2}(q),v_{3}(q),\text{ and }v_{4}(q)  as well.
263: 
264: 
265: 
266: Conjecture.
267: 
268: 
269: 
270: (Conjecture 3 [3])
271: We have that  \mathinner{\!\left\lvert V_{1}(n)\right\rvert}\to\infty  as  n\to\infty .
272: 
273: 
274: 
275: 
276: Conjecture.
277: 
278: 
279: 
280: (Conjecture 4 [3])
281: For almost all  n ,  V_{1}(n),V_{1}(n+1),V_{1}(n+2),\text{ and }V_{1}(n+3)  are two positive and two negative numbers.
282: 
283: 
284: 
285: 
286: Conjecture.
287: 
288: 
289: 
290: (Conjecture 5 [3])
291: For  k\geq 5 , there is an infinite sequence  N_{5}=293,N_{6}=410,   N_{7}=545,N_{8}=702,\ldots,N_{k}\geq 10k^{2},\ldots  such that  V_{1}(N_{k}),V_{1}(N_{k}+1),V_{1}(N_{k}+2)  all have the same sign.
292: 
293: 
294: 
295: 
296: Conjecture.
297: 
298: 
299: 
300: (Conjecture 6 [3]) With reference to Conjecture 5 [3], the numbers  \mathinner{\!\left\lvert V_{1}(N_{k})\right\rvert},   \mathinner{\!\left\lvert V_{1}(N_{k}+1)\right\rvert},\mathinner{\!\left\lvert V_{1}(N_{k}+2)\right\rvert}  contain a local minimum of the sequence  (\,\mathinner{\!\left\lvert V_{1}(n)\right\rvert})_{n\geq 0} .
301: 
302: 
303: 
304: 
305: 
306: Conjectures 3 (specifically, a refined density-one version) and 4 were proved for  v_{1}(q)  by Folsom–Males–Rolen–Storzer [7], and their analogs for  v_{2}(q),v_{3}(q),\text{ and }v_{4}(q)  were proved by Kundu, Storzer, Wang, and the author [8].
307: Both works relied on establishing precise asymptotic formulas for the underlying coefficients. More precisely, the later work established the following theorem.
308: 
309: 
310: 
311: Theorem.
312: 
313: 
314: 
315: (Theorem A [8])
391: 
392: 
393: 
394: While Conjectures 3 and 4 describe the prevailing growth and sign regularity of the coefficients, Conjectures 5 and 6 concern the exceptional behavior that occurs within this regular pattern.
395: These latter conjectures remained substantially less understood until very recently.
396: Folsom–Males–Rolen–Storzer [7, Section 6] gave a conditional explanation of Conjectures 5 and 6, contingent on deep unresolved irrationality questions.
397: Bachraoui [6] subsequently provided an unconditional proof of these conjectures for  v_{1}(q)  by analyzing the asymptotic formula for the coefficients  V_{1}(n)  derived in [7].
398: The aim of the present paper is to prove the analogs of Conjectures 5 and 6 for  v_{2}(q),v_{3}(q),\text{ and }v_{4}(q) , and more generally to establish an exceptional sign pair phenomenon for a broad class of integer sequences with prescribed oscillatory asymptotics.
399: This completes the resolution of all of Andrews’ conjectures and their analogs for these five  q -series.
400: 
401: 
402: 
403: 
404: 
405: 
406: 
407: 
408: 
571: 
572: 
573: 
574: With these conjectures and their analogs resolved, it is natural to ask whether these  q -series reflect a deeper automorphic structure, a question that we leave for future work.
575: 
576: 
577: 
578: 
579: The rest of the paper is organized as follows. In Section 2, we prove a uniform separation theorem which provides the key ingredient for proving the existence of infinitely many exceptional sign pairs. Section 3 is devoted to establishing several lemmas on the behavior of the oscillatory term in the asymptotic expansion of  V(n)  as given in (1).
580: Finally, in Section 4, we prove our general exceptional sign pair theorem, Theorem 7, and then specialize it to the  q -series  v_{2}(q),v_{3}(q),  and  v_{4}(q)  to obtain Theorem 1.
581: 
582: 
583: 
1713: [3]
1714: G. E. Andrews (1986)
1715: 
1716: Questions and conjectures in partition theory.
1717: 
1718: Amer. Math. Monthly 93 (9), pp. 708–711.
1719: 
1720: Cited by: §1,
1721: §1,
1722: Conjecture,
1723: Conjecture,
1724: Conjecture,
1725: Conjecture.
1726: 
1727: 
1728: [4]
1729: G. E. Andrews (1986)
1730: 
1731: Ramanujan’s “lost” notebook. V. Euler’s partition identity.
1732: 
1733: Adv. Math. 61 (2), pp. 156–164.
1734: 
1753: [6]
1754: M. El Bachraoui (2026)
1755: 
1756: Proofs for Andrews’ Conjectures 5 and 6 on  v_{1}(q) .
1757: 
1758: Note: arXiv:2604.08013
1759: 
1760: External Links: 2604.08013,
1761: Link
1762: 
1763: Cited by: §1,
1764: §1,
1765: §2,
1769: [7]
1770: A. Folsom, J. Males, L. Rolen, and M. Storzer (2026)
1771: 
1772: Oscillating asymptotics and conjectures of Andrews.
1773: 
1774: Math. Ann. 395 (4), pp. Art. 83, 1–48.
1775: 
1776: External Links: Document,
1777: Link
1778: 
1779: Cited by: §1,
1780: §1.
1781: 
1783: [8]
1784: J. Kalita, D. Kundu, M. Storzer, and X. Wang (2026)
1785: 
1786: On a conjecture of Andrews and almost alternating sign patterns.
1787: 
1788: Note: arXiv:2607.01210
1789: 
1790: Cited by: §1,
1791: §1,
1792: §4,
1793: Theorem,
1794: Theorem.
1795: 

## 376214 Fidkowski's conjecture on invertible phases entangled by QCAs
711: 
712: 
713: 
714: Although  Y  is often neglected in the field theory context, where it is just a gravitational topological response, the operation  Y  cannot be ignored on the lattice. Indeed, we will see that  Y  can indicate that the operations  S,T  mix with nontrivial QCA. Using the conjectures in Ref. [31], we indicate in which cases the properties of  Y  indicate that  S  and  T  mix with a nontrivial QCA. In particular, we will use the conjecture
715: 
716: 
717: 
718: Conjecture 2.1.
719: 
720: 
721: 
722: From Ref. [31]:  Y  is a nontrivial QCA if the invertible phase it entangles has a nontrivial partition function on some orientable manifold.
723: 
724: 
725: 
726: 
727: 
893: 
894: 
895: 
896:  T -protected phase; conjectured trivial QCA
897: 
898: 
899: 
900: Table 1: Key examples of modular relations with  Y  belonging in three different families: (1) Pontryagin/gravitational instanton counterterms, (2) Arf-Brown-Kervaire invariants, (3) Stiefel-Whitney counterterms. All  b,B  gauge fields are  2 -form gauge fields,  c,C  are  3 -form gauge fields, and  d,D  are  4 -form gauge fields.  p_{i}  are the Pontryagin classes,  \nu_{i}  are the Wu classes, and  w_{i}  are the Stiefel-Whitney classes. We have omitted the cup products to simplify the notation.
901: 
902: 
903: 
904: 2.1 General proof of projective  \mathrm{SL}(2,\mathbb{Z}_{N})  relations
905: 
1077: 
1078: 
1079: 
1080: In the following, we will show that the three classes of gravitational topological responses described above can be written as Gauss sums, and obtain the corresponding  S  and  T  operations. Using Conjecture 2.1, we will indicate which  \mathrm{SL}(2,\mathbb{Z}_{N})  relations involve  S  and  T  mixing with nontrivial QCA via  Y .
1081: 
1082: 
1083: 
1084: 2.2.1 Class (1):  \mathbb{Z}_{N}  symmetry and gravitational Pontryagin topological responses
1085: 
1086: 
1087: 
1088: 
1089: Here we first review the class of  \mathrm{SL}(2,\mathbb{Z}_{N})  relations with  Y  that performs stacking with gravitational Pontryagin counterterms. In 3+1d, this type of  Y  can be written as a Gauss sum as (e.g. Refs. [49, 22, 2])
1136: 
1137: 
1138: 
1139: When  Y\neq 1 , it defines a state that requires a nontrivial QCA [42, 44]. This comes from the incompatibility of a 2+1d boundary topological order with nonzero chiral central charge mod 8 with a commuting projector realization [42]. This is also compatible with Conjecture 2.1: such  Y  take nontrivial value on orientable manifolds.
1140: 
1141: 
1142: Generalization to  4k  spacetime dimension
1143: 
1144: 
1145: 
1146: 
1147: When the spatial dimension is  (4k+3) , we can define  S,T  operations with a choice of orientation for  \mathbb{Z}_{N}  internal  (2k-1) -form symmetry.
1148: We will focus on even  N  in the following.
1364: 
1365: 
1366: 
1367:  Y=(-1)^{\int\nu_{4}^{2}}  where  \nu_{4}  is the fourth Wu class: This 7+1d phase is a higher dimensional analog of the 3-fermion Walker Wang phase [31]. It is equivalent to four copies of the 7+1d analog of the chiral semion Walker-Wang theory  \sum_{b}e^{\frac{i\pi}{2}\int q_{\rho_{4}}(b)}  where  \rho_{4}  is the Wu structure  d\rho_{4}=\nu_{5}  covered in class (1)/(2). On orientable manifolds,  (-1)^{\int\nu_{4}^{2}}=(-1)^{\int w_{4}^{2}+w_{2}^{4}}  since on these manifolds,  \nu_{2}=w_{2}^{2}+w_{4} . Actually, the theories  (-1)^{\int w_{2}^{4}}  and  (-1)^{\int w_{4}^{2}}  are individually nontrivial on orientable manifolds:  (-1)^{\int w_{2}^{4}}  is nontrivial on  \mathbb{CP}^{4}  while  (-1)^{\int w_{4}^{2}}  is nontrivial on  \mathbb{CP}^{2}\times\mathbb{CP}^{2} . Therefore, although Ref. [31] only specifies the combination of these two states, they should actually individually give nontrivial QCA according to Conjecture 2.1. It is straightforward to obtain quadratic forms giving the corresponding  S,T : for  w_{2}^{4}  we use  q(B,C)=\pi(B\cup C+B\cup w_{2}^{2}+C\cup w_{2}^{2})  and for  w_{4}^{2}  we use  q(B,C)=\pi(B\cup C+B\cup w_{4}+C\cup w_{4})  where  B,C  are both  \mathbb{Z}_{2}   4 -form gauge fields.  (-1)^{\int w_{2}^{4}}  can actually be written as a Gauss sum in two different ways: we can also choose the quadratic form  q(B,C)=\pi(B\cup C+B\cup w_{2}+C\cup w_{2}^{3})  for 6-form  B  and 2-form  C .
1368: 
1369: 
1370: • 
1371: 
1372: 
1373: 
1374:  Y=(-1)^{\int w_{2}^{3}} : This is an example of an invertible phase (protected by time-reversal symmetry) that is trivial on every orientable manifold,33
1375:                       3
1376:                       
1378:                       
1379:                     This follows from  \pi\int w_{2}^{3}=\pi\int Sq^{2}(w_{2}^{2})=\pi\int Sq^{1}w_{2}\cup Sq^{1}w_{2}=\pi\int w_{1}\cup w_{2}\cup(w_{3}+w_{1}\cup w_{2})  which is trivial on orientable manifolds.
1380: In fact, there is no nontrivial 5+1d topological terms from Stiefel-Whitney classes that take nontrivial value on orientable 6-manifolds due to the relations  w_{2}\cup w_{4}=0,w_{3}^{2}=0,w_{6}=0  for orientable 6-manifolds  w_{1}=0  (see e.g. Ref. [95]).
1381:  so would not give a nontrivial QCA according to Conjecture 2.1. It is a simple example of an action that is not naively a pairing, but by splitting it into  w_{2}  and  w_{2}^{2}  we can get a quadratic form  q(B,C)=\pi(B\cup C+B\cup w_{2}+C\cup w_{2}^{2}) . The resulting  S  corresponds to gauging  \mathbb{Z}_{2}   1 -form and  3 -form symmetries.
1382: 
1383: 
1384: 
1385: 
1386: 
1387: 
1388: It will be particularly useful when  T  can be written entirely in terms of background gauge fields  \{B_{i}\}  rather than explicitly in terms of Stiefel-Whitney classes. This turns out to be the case for the first three examples above; in Sec. 4.2, we show that  Y  in these cases can be written as  \sum_{\{b_{i}\}}(-1)^{\int q(\{b_{i}\})}  where  q(\{b_{i}\})  is a quadratic form involving symmetry gauge fields only. This allows for efficient implementation of the action of the QCA on product states to get invertible states with these gravitational topological responses. Otherwise, it is unclear how to obtain couplings between gauge fields and Stiefel-Whitney classes via local unitaries on the lattice.
1389: 
1390: 
1963: 
1964: 
1965: 
1966: In this section, we will show how to implement all of the steps discussed in previous sections in lattice models. In the context of lattice models, it is of particular interest to distinguish states entangled from a product state by FDQC vs QCA. Here we must be careful with terminology: when  Y  is a gravitational term that takes a nontrivial value on some orientable manifold, it corresponds to a QCA according to Conjecture 2.1 from Ref. [31]. However, on the lattice, two QCAs are equivalent if they differ by a FDQC. According to this definition, the QCA producing  Y  is equivalent to that producing i.e.  YT^{-1} . The important aspect is that the QCA is implemented on the lattice by a sequence of  S  and  T  operations, where  T  is a FDQC and  S  is implemented by an FDQC + measurement + error correction.
1967: 
1968: 
1969: 
1970: 
1971: For a simple example that clarifies what we mean, consider the Stiefel-Whitney term  Y=(-1)^{\int\nu_{2}^{2}}=\sum_{b_{1},b_{2}}(-1)^{\int b_{1}^{2}+b_{2}^{2}+b_{1}\cup b_{2}} . On the lattice, one might think that this would be implemented by entangling  (-1)^{\int b_{1}^{2}+b_{2}^{2}+b_{1}\cup b_{2}}  via a finite depth circuit similar to the cluster state entangler, and then measuring the  b_{1}  and  b_{2}  degrees of freedom to decouple them from the theory. But on the lattice, this would produce a trivial state with all of the degrees of freedom measured out. Indeed, the above is not an  ST  operation; it is really an  \epsilon_{0}ST  operation. While the first step is indeed a circuit, the second step is not quite gauging because it does not introduce new gauge field degrees of freedom.
1972: 
1973: 
1974: 
1975: 
2548: 
2549: 
2550: 
2551: For  Y=(-1)^{\int w_{2}^{4}} , which is conjectured to be a nontrivial QCA, the naive way to write  Y  as a Gauss sum is as  Y=\sum_{A,B}(-1)^{\int AB+Aw_{2}+Bw_{2}^{3}}  for  A  a  6 -form gauge field and  B  and  2 -form gauge field (we can also write it similarly in terms of two  4 -form gauge fields by splitting  w_{2}^{4}  into two factors of  w_{2}^{2} ). Another way to write  Y  as a Gauss sum is as  \sum_{A,B}(-1)^{\int AB+\mathrm{Sq}^{2}A+B^{4}}  because the sum over  A  sets  B=w_{2} . This Gauss sum uses  T  written entirely in terms of background gauge fields, defined by a quadratic form with the same polarization as  AB+Aw_{2}+Bw_{2}^{3} , so forms a projective  \mathrm{SL}(2,\mathbb{Z}_{2})  with the same  S  as for  AB+Aw_{2}+Bw_{2}^{3} .
2552: 
2553: 
2554: 
2555: However, a general Stiefel-Whitney counterterm  Y  may not be of the form  \sum_{\{b_{i}\}}(-1)^{\int q(\{b_{i}\})}  for any quadratic form  q(\{b_{i}\})  involving symmetry gauge fields. We will now show that for all gravitational terms  Y , one can in principle obtain the corresponding action concretely in a lattice model (up to a FDQC) using an  S\tilde{T}  operation where  S  is gauging an abelian finite higher form symmetry (implemented by a FDQC, measurement, and error correction) and  \tilde{T}  is a more general FDQC, not necessarily the exponential of a quadratic form. For  \tilde{T}  that is not the exponential of a quadratic form, it may not participate in a  \mathrm{SL}(2,\mathbb{Z}_{2})  relation, but it can still be implemented by a FDQC.
2556: 
2557: 
2558: 
2559: 
2560: Refs. [18, 31] obtained for a general action of the form  (-1)^{\int w_{i}\cdots w_{j}}  a formulation in terms of symmetry gauge fields. To do so, one starts with
3086: 
3087: 
3088: 
3089: which describes the three fermion Walker Wang model, which has gapped boundary given by the three fermion anyon theory. This time-reversal SPT is order two, so  Y_{\rho_{2}}  is order eight, consistent with the conjectured Witt group classification of QCAs [81, 44].
3090: 
3091: 
3092: 
3093: 
3094: We note that while the invertible phase and ground state requires time-reversal symmetry to be stable against perturbations, the corresponding QCA does not. While the ground states of two models differing by a gravitational topological response may be local unitary related to each other in the absence of symmetry, due to QCA obstructions there may not exist such an interpolation between their parent Hamiltonians. Specifically, if  H=U_{QCA}H_{X}U_{QCA}^{\dagger}  where  U_{QCA}  is a nontrivial QCA and  H_{X}  is a trivial paramagnet Hamiltonian, additional conjugation by any FDQC  U_{FDQC}  should not change the QCA class of  H . The corresponding ground states may have emergent time-reversal symmetry  U_{FDQC}\cdot K .
3095: 
3096: 
3097: 
3098: 
3212: 
3213: 
3214: 
3215: We use in this work Conjecture 2.1 from Ref. [31]. It would be interesting to see if this conjecture can be proven rigorously on the lattice, perhaps using incompatibility of certain topological responses to commuting projector realizations. In 3+1d, the standard argument for nontriviality of QCA is based on the incompatibility of Witt nontrivial 2+1d boundary topological orders to commuting projector realizations. By Witt nontrivial, we mean there is no gapped boundary to the vacuum [42, 44, 80]. It would be interesting if incompatibilities in higher dimensions can also be related to a generalized notion of Witt class.
3216: 
3217: 
3218: 
3219: Concrete implementation of gravitational Stiefel-Whitney terms in lattice models
3220: 
3221: 
3222: 
3223: 
3224: In this work we gave a schematic construction for lattice models whose ground states carry nontrivial gravitational Stiefel-Whitney terms, building off of Ref. [18, 31]. We used steps involving gauging of finite invertible higher form symmetries and operations that we argue to be implementable by FDQCs. We leave to future work a more microscopic description of these FDQCs.
5244: Cited by: 2nd item,
5245: 3rd item,
5246: §2.2.2,
5247: Conjecture 2.1,
5248: §2,
5249: 2nd item,
5250: §4.2,
5251: §4,
5252: §6,
5253: §6.
5254: 
5255: 
5256: [32]

## 376223 Prime affine direction conjecture for additive codes
198: Abstract
199:     
200: 
201: An additive  (n,k,d)_{q^{m}/q} -code is a  \mathrm{GF}(q) -linear subspace of  \mathrm{GF}(q^{m})^{n}  of  \mathrm{GF}(q) -dimension  km  with minimum Hamming distance  d . We first extend the Alderson–Bruen–Silverman (ABS) model of linear codes to the additive setting: a code of length  n  with  q^{km}  words over an alphabet of size  q^{m}  admits an ABS model if and only if it is equivalent to a nondegenerate additive code. We then ask whether an additive code that admits an extension must admit an additive extension. For linear codes ( m=1 ) this is a theorem of Alderson and Gács. We characterize the additive codes admitting no additive extension as those whose associated projective system of flats is complete, and we prove that the answer to the question above is again affirmative for  (n,2,d)_{9/3} -,  (n,2,d)_{4/2} -, and  (n,3,d)_{4/2} -codes. In contrast with the linear case, we show that the answer is negative in general. Scattered linear sets yield, for each square  q , extendable additive  (n,2,d)_{q^{2}/q} -codes admitting no additive extension. Further, a different method yields an extendable additive  (30,2,24)_{8/2} -code with no additive extension. Consequently, for properly additive codes, completeness of the associated projective system does not imply maximality of the code. We conjecture that extendable  (n,2,d)_{p^{2}/p} -codes,  p  prime, always admit additive extensions.
202:   
203: 
204: 
205: 
206: 
207: Keywords: additive codes, code extensions, maximal codes, projective systems, directions in affine spaces, scattered linear sets
208: 
209: 
210: 
291: 
292: 
293: 
294: In Section 8 we examine the prime case, and conjecture
295: (Conjecture 8.1) that every extendable additive  (n,2,d)_{p^{2}/p} -code,  p  prime, admits an additive extension.
296: 
297: 
298: 
299: 
300: Even over prime fields, the parallel with linear theory does not hold in general once  m\geq 3 . In Section 7 we construct a counterexample (see Theorem 7.7).
301: 
302: 
303: 
304: 
1704: 
1705: 
1706: 
1707: For  m=2  the construction of Section 6 rests on the existence of a suitable scattered linear set, which exists precisely because  \mathrm{GF}(q)  there has a proper subfield, while the example of Section 7 has  m=3 . For  m=2  over a prime field neither method is available, and we conjecture:
1708: 
1709: 
1710: 
1711: Conjecture 8.1.
1712: 
1713: 
1714: 
1715: Let  p  be a prime.
1716: 
1717: 
1718: (i) 
1719: 
1720: 
1734: 
1735: 
1736: 
1737: Part (i) holds for  p=2,3  by Lemma 4.1 and Proposition 4.4 (Section 4). A naive nonexhaustive computer search found no counterexample for  p=5 . A natural approach to Conjecture 8.1 is through the theory of directions and Rédei type blocking sets. For a set  T  of  p^{2}  points of  \mathrm{AG}(4,\,p) ,  D(T)  contains no line of  \mathrm{PG}(3,\,p)  if and only if the set  B=\Pi\setminus D(T)  of undetermined directions meets every line of  \mathrm{PG}(3,\,p) . Projecting  T  from an undetermined direction  [u]\in B  yields a set of  p^{2}  points of  \mathrm{AG}(3,\,p) , a set of Rédei size, where the structure theorem of Storme and Sziklai [28] (the directions determined by a set of  q^{2}  points of  \mathrm{AG}(3,\,q)  form a union of full lines) and the prime-field direction theorems [16, 11] apply; see [29] for a related higher-dimensional direction problem.
1738: 
1739: 
1740: 
1741: Remark 8.2.
1742: 
1743: 
1744: 
1745: Conjecture 8.1(i) splits into two cases that perhaps provide insight into why primality may be key. Let  T  be a putative counterexample and let  B=\Pi\setminus D(T)  be its set of undetermined directions, so that  B  meets every line of  \Pi .
1746: 
1747: 
1748: 
1749: 
1750: Suppose first that  B  contains a line  \ell . Then no difference of points of  T  lies in  \ell , so the projection of  \mathrm{AG}(4,\,p)  along  \ell  is injective on  T , hence bijective onto  \mathrm{AG}(2,\,p) . In suitable coordinates  \mathrm{GF}(p)^{4}=\mathrm{GF}(p)^{2}\times\mathrm{GF}(p)^{2}  we have  T=\{(x,f(x)):x\in\mathrm{GF}(p)^{2}\}  for an arbitrary function  f:\mathrm{GF}(p)^{2}\to\mathrm{GF}(p)^{2} , with  \ell=\mathrm{PG}(0\times\mathrm{GF}(p)^{2}) . A line of  \Pi  contained in  D(T)  must avoid  B\supseteq\ell , and the lines of  \Pi  disjoint from  \ell  are precisely the sets  \mathrm{PG}(\mathrm{graph}(A)) , where  A:\mathrm{GF}(p)^{2}\to\mathrm{GF}(p)^{2}  is linear and  \mathrm{graph}(A)=\{(v,Av):v\in\mathrm{GF}(p)^{2}\}\leq\mathrm{GF}(p)^{4}  (a  2 -dimensional subspace meets  0\times\mathrm{GF}(p)^{2}  trivially exactly when it is such a graph). Moreover  [(v,Av)]\in D(T)  if and only if  f-A  identifies two points of some affine line of direction  v . This case of Conjecture 8.1(i) is therefore the statement: for every  f:\mathrm{GF}(p)^{2}\to\mathrm{GF}(p)^{2}  there is a linear map  A  such that  f-A  is non-injective on some line of every parallel class of  \mathrm{AG}(2,\,p) . This is a direction problem for vector-valued functions, and the prime-field slope theorems bear on it directly. For every affine line  \ell^{\prime}  of the domain and every linear functional  \lambda  on the codomain, the graph of  \lambda\circ(f-A)|_{\ell^{\prime}}  is a set of  p  points of  \mathrm{AG}(2,\,p) , which by Rédei–Megyesi [26] and its refinements [16, 11] is affine or determines at least  (p+3)/2  slopes; see [14] for functions of several variables. The subfield-linear maps occupying the exceptional middle range of the slope theorem of [11] are precisely the source of the counterexamples of Section 6, where  T=U  is the graph of the  \mathrm{GF}(q_{0}) -linear map  (x,y)\mapsto(x^{q_{0}},y^{q_{0}}) . Over prime fields that range is empty.
1751: 
1752: 
1753: 
1754: 
1755: If instead  B  contains no line, then  B  is a blocking set of  \mathrm{PG}(3,\,p)  with respect to lines containing no full line, so the equality case of the Bose–Burton theorem (a plane) is excluded and  |B|\geq p^{2}+p+2 . Moreover, projecting  T  from any  [u]\in B  yields  p^{2}  points of  \mathrm{AG}(3,\,p)  determining all of their directions, since an undetermined direction of the projected set corresponds to a line of  \Pi  through  [u]  contained in  B .
1756: 
1757: 
1758: 
1759: 
1768: 
1769: 
1770: 
1771: For  m=1  (linear codes) extendability always implies additive (linear) extendability [6]. For  m=2  the same holds for  q\in\{2,3\}  when  k=2  (Section 4) and for  (q,k)=(2,3)  (Section 5), while for every square  q  it does not (Section 6); we conjecture that it holds for all primes (Conjecture 8.1). For  m\geq 3  it does not hold even over the prime field:  (q,m,k)=(2,3,2)  (Section 7). We collect the main open questions.
1772: 
1773: 
1774: 
1775: Problem 9.1.
1776: 
1777: 
1778: 
1779: Prove or disprove Conjecture 8.1. More generally, settle the case  m=2 ,  k\geq 3 : the first instance  (q,k)=(2,3)  is Theorem 5.5, and the scattered obstruction is unavailable for  k\geq 3  (see the closing remark of Section 8); the cases  q>2  and  k\geq 4  remain open.
1780: 
1781: 
1782: 
1783: 
1784: Problem 9.2.
1785: 
1786: 
1787: 
1788: Extend Theorem 6.6 to non-square, non-prime  q . Further, determine the minimum length of an extendable, additively maximal additive  (n,2,d)_{q^{2}/q} -code for square  q : is  n=112  optimal for  q=4 ? (Any sub-multiset of the external lines whose set of maximal-fold points still meets every line of  \Pi  yields a shorter example.)

## 376236 Catalan classification conjecture for extremal even-intersecting lattice-path families
215: 
216:     
217: 
218: and construct families showing that  M_{\mathrm{odd}}(n)=\Theta(n^{2}) . Finally, we construct at least  C_{n}  distinct extremal even-intersecting families, where  C_{n}  is the  n th Catalan number, and conjecture that these are all the extremal families.
219:   
220: 
221: 
222: 
223: 1 Introduction
224: 
225: 
226: 
227: 
1126: 
1127: 
1128: 
1129: Conjecture 4.1.
1130: 
1131: 
1132: 
1133: There are exactly  C_{n}  families of size  2^{n}  in which every two distinct paths have an even number of common edges.
1134: 
1135: 
1136: 
1137: 
1138: 
1139: The conjecture has been verified for  n\leq 5 . If true in general, it would give another combinatorial interpretation of the Catalan numbers.
1140: 
1141: 
1142: 
1143: 
1144: This notion can be explored further for modular intersection results and generalisations to paths from  (0,0)  to  (m,n) .
1145: 
1146: 
1147: 
1148: 

## 376237 Wegner's conjecture on the 2-distance chromatic number of planar graphs
202: 
203: The square of a graph  G  is the graph obtained from  G  after adding an edge between any two vertices of distance  2 . A  k -irregular graph is a graph with maximum degree  k  such that vertices of degree  k  are not adjacent.
204: A list assignment of a graph is a function  L  that assigns to each vertex a list of permissible colors.
205: The graph is said to be  L -colorable if there exists a proper coloring  f  such that  f(v)\in L(v)  for every vertex  v . A graph  G  is called  k -choosable if it is  L -colorable for every list assignment where each list has exactly  k  colors. The list chromatic number of  G , denoted by  \chi_{l}(G) , is the smallest integer  k  for which  G  is  k -choosable. Cranston and Kim [6] showed that  \chi_{l}(G^{2})\leq 8  for all subcubic graphs except the Petersen Graph. Moreover, Cranston and Kim [6] conjectured that for graphs with maximum degree  k  and maximum clique size  w(G^{2})\leq k^{2}-1 , we have  \chi_{l}(G^{2})\leq k^{2}-1 . We prove that for a 4-irregular graph  G , we have  \chi_{l}(G^{2})\leq 11 . Moreover, we provide an example to show that this bound is sharp.
206:   
207: 
208: 
209: 
210: 
211: Keywords: List coloring, irregular, square of a graph.
212: 
213: 
214: 
245: 
246: 
247: 
248: Several papers have studied Wegner’s conjecture [17] regarding the  2 -distance chromatic number of planar graphs. Wegner conjectured the following:
249: 
250: 
251: 
252: Conjecture 1.
253: 
254: 
255: 
256: (Wegner [17]) If  G  is a planar graph with maximum degree  \Delta , then
257:  \chi_{2}(G)\leq 7  if  \Delta=3 ,  \chi_{2}(G)\leq\Delta+5  if  4\leq\Delta\leq 7  and  \chi_{2}(G)\leq\lfloor\frac{3\Delta}{2}\rfloor+1  if  \Delta\geq 8 .
258: 
259: 
260: 
261: 
262: 
263: This conjecture remains largely open. Thomassen [15] proved it for planar graphs with maximum degree  \Delta=3 . For larger values of  \Delta , several upper bounds on  \chi_{2}(G)  have been established. In particular, Agnarsson and Halldórsson [1] proved that
264:  \chi_{2}(G)\leq\left\lfloor\frac{9\Delta}{5}\right\rfloor+2 
265: for planar graphs with  \Delta\geq 749 , and this was later improved by Borodin et al. [3] to
266:  \chi_{2}(G)\leq\left\lceil\frac{9\Delta}{5}\right\rceil+1 
267: for  \Delta\geq 47 . More recently, Bousquet [4] proved that  \chi_{2}(G)\leq 2\Delta+7  for  \Delta\geq 9  and  \chi_{2}(G)\leq 21  for  \Delta\leq 6 . For planar graphs with  \Delta\leq 5 , Zhu and Bu [18] proved that  \chi_{2}(G)\leq 20 , and this bound was subsequently reduced to  19 ,  18 ,  17 , and finally  16  by Chen [5], Aoki [2], Zou et al. [19], and Zakir Deniz [8], respectively. Further results on the  2 -distance chromatic number of planar graphs can be found in [13, 14, 16, 18].
268: 
269: 
270: 
271: Conjecture 2.
272: 
273: 
274: 
275: (Cranston [6])
276: Let  G  be a graph with maximum degree  k  and  w(G^{2})\leq k^{2}-1 . Then, we have  \chi_{l}(G^{2})\leq k^{2}-1 .
277: 
278: 
279: 
280: 

## 376249 Depth-six classification conjecture for unramified multiple mixed values
195: 7.2 The height one family  V^{\mathfrak{m}}_{0}(d) 
196: 
197: 
198: 8 Some general conjectures
199: 
200: References
201: 
202: 
203: 
204: 
205: 
206: 
207:   
229: such values are actually in level one, namely, expressible in terms of multiple zeta values. To solve this completely is
230: beyond our current knowledge since it calls for new ideas from transcendental number theory. However, much progress has been
231: made on the motivic level. Previously, using the descent theory developed by Brown et al. we have tackled this problem for a
232: few special classes of MMVs with regular parity patterns among the summation indices, including Hoffman’s multiple  t -values, Kaneko and Tsumura’s multiple  T -values, and our own multiple  S -values. In this paper, we turn to the general case and determine completely all the unramified motivic MMVs of depth less than four as well as a few families of unbounded depths. At the end of the paper, we will present some general conjectures to describe the unramified MMVs at all depths greater than three.
233: 
234: 
235: 
236: 
237: Keywords: (motivic) multiple zeta values, (motivic) Euler sums, (motivic) multiple mixed values, unramifiedness.
238: 
239: 
240: 
241: 
272: 
273: and they exhibit a remarkably rich structure of  \mathbb{Q} -linear relations that continues to captivate researchers. We refer to
274:  \dep({\boldsymbol{\sl{s}}})=d  as the depth and  |{\boldsymbol{\sl{s}}}|=s_{1}+\cdots+s_{d}  as the weight. Despite its substantial progress driven by the theory
275: of mixed Tate motives over  \mathbb{Q} , as developed by Deligne, Goncharov, Brown, and others, the celebrated conjectures of Zagier
276: and Hoffman concerning the  \mathbb{Q} -vector space spanned by MZVs remain open.
277: 
278: 
279: 
280: 
281: A key turning point has been the geometric realization of MZVs as iterated integrals on  \mathbb{P}^{1}\setminus\{0,1,\infty\} ,
282: which has proved indispensable for uncovering their motivic origin:
283: 
284: 
477: 
478: Previous work has applied this machinery successfully to special classes of MMVs. For Hoffman’s multiple  t -values, Murakami
479: [15] and Charlton [6] have identified several families of unramified MtVs, including all MtVs
480: with components at least 2. More such families can be found in the authors’ related work [19]. There, the authors have derived necessary and sufficient conditions for unramifiedness of the motivic MSVs and MTVs when the depth is less than four, partially confirming a conjecture of Kaneko and Tsumura.
481: Tsumura.
482: 
483: 
484: 
485: 
486: 1.5 Main results
487: 
488: 
489: 
490: 
491: In this paper, we turn to the general setting of multiple mixed values (MMVs). Our goal is three-fold: first, to determine
492: completely all unramified motivic MMVs in depth less than four; second, to identify several new families of unramified MMVs of
493: unbounded depth; third, to present some general conjectures on all possible unramified motivic MMVs in large depths.
494: 
495: 
496: 
497: 
498: Specifically, building on the descent theory established in prior works, we provide:
499: 
500: 
501: 
502: 
521: 
522: 
523: 
524: Explicit identities (conditional on an analytic conjecture in one case) expressing each motivic value in a height one
525: family, with  d  members in every even depth  d , as a  \mathbb{Q} -linear combination of motivic MZVs (see
526: Theorem 7.5 and 7.12).
527: 
528: 
529: (4) 
530: 
531: 
532: 
533: Conjectures 8.2-8.6 on all possible unramified motivic MMVs in arbitrary
534: depths, based on our extensive numerical experiment.
535: 
536: 
537: 
538: 
539: 
540: 
541: These results represent a significant step toward understanding the general MMV landscape. The classification theorems
542: establish, under Grothendieck’s period conjecture, complete characterizations of unramifiedness for low-depth cases,
543: confirming and extending conjectures of Kaneko and Tsumura and others.
544: 
545: 
546: 
547: 
548: 1.6 Outline of the Paper
549: 
550: 
551: 
552: 
558: provide all the necessary key steps for the other three patterns. Section 6 constructs two infinite unramified families of
559: arbitrary depth  \geq 2  and almost extremal height while Section 7 provides one more unramified family but with height equal to one. Moreover, in every even depth  d  we determine  d  such unramified height one motivic MMVs with their explicit
560: expressions in terms of motivic MZVs with one exception (where the expression is only conjectural). Finally, Section 8
561: discusses open problems and conjectures suggested by our results and extensive numerical experiments, including potential
562: generalizations and connections to the ramification theory of more general variations of MZVs such as the alternating MMVs
563: [18] and multiple Clausen values and multiple Glaishers values at level three [4].
564: 
565: 
566: 
567: 
568: 
569: 2 Notation and the motivic setup
570: 
2955: 
2956: In this section, we will prove that that  V_{j}(d)  ( j=\emptyset,0  or  1<j<d ) are unramified by finding their explicit
2957: expressions except for  V_{0}(d)  for which the expression is only conjectural. Using this information we then lift these
2958: expressions to the motivic version. For  V_{0}^{\mathfrak{m}}(d)  we can actually prove it is unramified without assuming the conjectured
2959: formula. In fact, the conjectured expression of  V_{0}(d)  would imply the explicit expression of  V_{0}^{\mathfrak{m}}(d)  in terms of
2960: motivic MZVs.
2961: 
2962: 
2963: 
2964: 7.1 The height one families  V^{\mathfrak{m}}_{j}(d) ,  j\neq 0 
2965: 
2966: 
2967: 
2968: 
3768: 
3769: 
3770: 
3771: We first remark that from numerical computation the following conjecture must be true.
3772: 
3773: 
3774: 
3775: Conjecture 7.7.
3776: 
3777: 
3778: 
3779: For all positive integers  d\geq 3  we have
3780: 
3781: 
3782: 
3783: 
3784:  \zeta^{\sharp}(2,1_{d-3},\overline{2})=\displaystyle\frac{1}{2}\zeta(d+1)-2\displaystyle\sum_{m+n=d+1,2|n}\zeta(m,n). 
3792: 
3793: 
3794: 
3795: Assuming Conjecture 7.7, we have
3796: 
3797: 
3798: 
3799: 
3800:  V_{0}(d)=\displaystyle\frac{1}{2}\zeta^{\star}(1,d)-\displaystyle\frac{1}{4}\zeta(d+1)+\displaystyle\sum_{m+n=d+1,2|n}\zeta(m,n). 
3801: 
3802: (7.22)
3803: 
3804: 
3862: 
3863: 
3864: 
3865: Hence, (7.22) holds if we assume Conjecture 7.7.
3866: ∎
3867: 
3868: 
3869: 
3870: 
3871: 
3872: We can now lift Theorem 7.8 to is motivic version.
3873: First, we need some preliminary lemmas.
3874: 
4090: 
4091: 
4092: For all even positive integers  d  the motivic MMV  V_{0}^{\mathfrak{m}}(d)  is unramified. Moreover,
4093: assuming Conjecture 7.7, we have
4094: 
4095: 
4096: 
4097: 
4098:  V_{0}^{\mathfrak{m}}(d)=\displaystyle\frac{1}{2}\zeta^{{\mathfrak{m}},\star}(1,d)-\displaystyle\frac{1}{4}\zeta^{\mathfrak{m}}(d+1)+\displaystyle\sum_{m+n=d+1,2|n}\zeta^{\mathfrak{m}}(m,n). 
4099: 
4100: 
4101: 
4102: 
4269: 
4270: 
4271: 
4272: 8 Some general conjectures
4273: 
4274: 
4275: 
4276: 
4277: In Section 4, we have determined all depth three unramified motivic MMVs. To conveniently describe our
4278: findings for large depth, we call the largest component of an index  {\boldsymbol{\sl{s}}}\in\mathbb{N}^{d}  its width, denoted by  \wth({\boldsymbol{\sl{s}}}) .
4279: The following fact is useful when we study MZVs and MTVs both of which satisfy the duality relation.
4280: 
4281: 
4315: 
4316: 
4317: 
4318: We start with a conjecture concerning the MTVs. Recall that Kaneko and Tsumura [13] conjectured that if an MTV  T({\boldsymbol{\sl{s}}})  is unramified then either  \dep({\boldsymbol{\sl{s}}})\leq 3  or  \dep({\boldsymbol{\sl{s}}}^{*}) . This motivates us the following using Lemma 8.1.
4319: 
4320: 
4321: 
4322: Conjecture 8.2.
4323: 
4324: 
4325: 
4326: A wide MTV of depth at least 4 is ramified.
4327: A slender MTV is unramified if and only if it has the shape  T(1_{2k},3,1_{2l},2)  or  T(1_{2k},3)  for some
4328:  k,l\in\mathbb{N}\cup\{0\} .
4329: A narrow MTV is unramified if and only if it has the shape  T(1_{k},2)  or  T(2,1_{2k+1},2)  for some  k\in\mathbb{N}\cup\{0\} , or
4330:  T(2,1_{k},2,1_{l})  for some  k,l\in\mathbb{N}\cup\{0\}  with  k+l  odd, or
4331:  T(1_{2k+1},2,1_{2l},2,1_{2m+1})  for some  k,l,m\in\mathbb{N}\cup\{0\} .
4339: 
4340: By duality,  T(1_{2k},3,1_{2l},2)=T(2l+2,1,2k+2) ,  T(1_{2k},3)=T(1,2k+2) ,
4341:  T(1_{k},2)=T(k+2) ,  T(2,1_{2k+1},2)=T(2k+3,2) , and  T(1_{2k+1},2,1_{2l},2,1_{2m+1},2)=T(2m+3,2l+2,2k+3)  are all unramified
4342: by [19, Theorem 1.2]. This conjecture implies that if the depths of an MTV and its dual are both at least 4 then
4343: it is ramified, which was first conjectured by Kaneko and Tsumura [13].
4344: 
4345: 
4346: 
4347: 
4348: 
4349: From numerical evidence, we propose the following conjectures.
4350: 
4351: 
4352: 
4353: Conjecture 8.4.
4354: 
4355: 
4356: 
4357: In depth  4 , the following list should exhaust all wide or slender unramified MMVs that are not MZVs nor MtVs:
4358: 
4359: 
4360: 
4361: 
4362: 
4412: 
4413: 
4414: 
4415: The unramified non-MTV MMVs in Conjecture 8.4 all have the following property: if there is only one odd
4416: signature then it must correspond to a unit component, otherwise all the non-unit components must have odd signature while
4417: all the unit components have even signature.
4418: 
4419: 
4420: 
4421: 
4422: In [19], we found that  S(2,1_{3},4)  is unramified. We believe this is truly special.
4423: 
4424: 
4425: 
4426: Conjecture 8.5.
4427: 
4428: 
4429: 
4430: In depth  5 ,  S(2,1_{3},4)  is only unramified wide MMV that is not an MZV nor an MtV. An unramified slender or narrow
4431: MMVs
4432: must be either MZV, or MtV, or in the family of Theorems 6.2 or 6.3, or in the
4433: following list:
4434: 
4435: 
4470: 
4471: 
4472: 
4473: Again, in Conjecture 8.5 all non-MTV MMVs have only one odd signature and it corresponds to a unit
4474: component.
4475: 
4476: 
4477: 
4478: Conjecture 8.6.
4479: 
4480: 
4481: 
4482: Suppose that the depth is at least  6 . Then we have
4483: 
4484: 
4485: (1) 
4486: 
4487: 
4494: 
4495: 
4496: 
4497: All unramified slender MMVs are MZVs or MtVs or the MTVs given in Conjecture 8.2.
4498: 
4499: 
4500: (3) 
4501: 
4502: 
4503: 
4504: All unramified narrow MMVs are MZVs, or MtVs, or the MTVs given in Conjecture 8.2, or
4505: elements in the families given in Theorems 6.2, 6.3 and
4506: 7.5.
4507: 
4508: 
4509: 
4510: 
4511: 
4512: 
4513: 
4587: 
4588: [6]
4589: 
4590: S. Charlton: On motivic multiple  t -values, Saha’s basis conjecture, and generators of alternating MZVs, Math. Ann.
4591: 392 (2025), pp. 1995-2079. https://doi.org/10.1007/s00208-024-02928-3.
4592: 
4593: 
4594:       
4595: 
4596: [7]
4597: 
4598: P. Deligne, Le groupe fondamental de la  {\mathbb{G}}_{m}-{\boldsymbol{\mu}}_{N} , pour
4599:  N=  2, 3, 4, 6 ou 8 (in French),
4682: 
4683: [18]
4684: 
4685: C. Xu, L. Yan and J. Zhao, Alternating multiple mixed values, regularization, parity, and dimension conjecture,
4686: Indagationes Math. 35(6) (2024), pp. 1212–1248. doi.org/10.1016/j.indag.2024.06.001. arxiv.org/2208.09593.
4687: 
4688: 
4689:       
4690: 
4691: [19]
4692: 
4693: C. Xu and J. Zhao, Ramified and unramified motivic multiple  t -,  T - and  S -values. arXiv: 2310.16041
4694: 
4723: 
4724: [23]
4725: 
4726: J. Zhao, On a conjecture of Borwein, Bradley and Broadhurst,
4727: J. Reine Angew. Math. 639 (2010), pp. 223–233.
4728: doi.org/10.1515/crelle.2010.016. (MR 2608196)
4729: 
4730: 
4731:       
4732: 
4733: [24]
4734: 
4735: J. Zhao, Identity Families of multiple harmonic sums and multiple zeta (star) values.

## 376257 Gerbner–Palmer's generalized Turán conjecture for trees
192: Abstract
193:     
194: 
195: Given graphs  H  and  F , the generalized Turán number  \mathrm{ex}(n,H,F)  is the maximum number of copies of  H  in an  n -vertex  F -free graph. Alon and Shikhelman (J. Combin. Theory Ser. B, 2016) initiated the systematic study of generalized Turán problems. Let  T  be a tree on  k  vertices, and write  n=a(k-1)+b , where  0\leq b<k-1 . Recently, Gerbner and Palmer (Electron. J. Combin., 2026) proposed the following conjecture: for every  r\geq 3 , the graph  aK_{k-1}\cup K_{b}  maximizes the number of copies of  K_{r}  among all  n -vertex  T -free graphs. In this paper, we verify their conjecture when  r=k-2  or  r=k-3\geq 5 . More precisely, we show that  \mathrm{ex}(n,K_{r},T)=a\binom{k-1}{r}+\binom{b}{r}  and characterize all extremal graphs.
196:   
197: ††footnotetext: *Corresponding author.††footnotetext: Email addresses: junpengzhou@shu.edu.cn (J. Zhou), xiyingyuan@shu.edu.cn (X. Yuan).
198: 
199: 
200: 
201: Keywords: generalized Turán problem, tree, clique counting, Erdős–Sós conjecture
202: 
203: 
204: 
205: 
206: AMS (2020) subject classifications: 05C35, 05C05
207: 
208: 
209: 
210: 1 Introduction
227: 
228: 
229: 
230: In this paper, we consider the case where  H  is a clique and  F  is a tree. Let  T  be a tree on  k  vertices. The Erdős–Sós conjecture [5] states that  \mathrm{ex}(n,T)\leq(k-2)n/2 . When  k-1  divides  n , the disjoint union of copies of  K_{k-1}  shows that the above bound is sharp. Gerbner, Methuku and Palmer [8] proved that if the Erdős–Sós conjecture holds for  T  and its subtrees, then
231: 
232: 
233: 
234: 
235:  \mathrm{ex}(n,K_{r},T)\leq\frac{n}{k-1}\binom{k-1}{r} 
236: 
237: 
238: 
239: for  3\leq r\leq k-3 . This bound is also sharp when  k-1  divides  n . Letzter [11] determined the order of magnitude of  \mathrm{ex}(n,H,T)  for arbitrary fixed graphs  H  and trees  T .
242: 
243: 
244: Several exact results are known for special trees.
245: When  T  is a star, the result follows from the Gan–Loh–Sudakov conjecture [6], proved by Chase [4] and later given a unified proof by Chao and Dong [3]. When  T  is a path, Luo [12] established the corresponding upper bound. Later, Chakraborti and Chen [2] determined the exact value and characterized all extremal graphs. Furthermore, Gerbner [7] obtained exact results for double stars.
246: 
247: 
248: 
249: 
250: In [9], Gerbner and Palmer observed that for  n=a(k-1)+b  with  0\leq b<k-1 , the natural analogue of the extremal construction above is  aK_{k-1}\cup K_{b} . For  3\leq r\leq k-1 , each copy of  K_{k-1}  contains  \binom{k-1}{r}  copies of  K_{r} . This suggests that the generalized Turán problem may be easier for  r>2  than the classical case  r=2 . Motivated by this observation, they proposed the following conjecture.
251: 
252: 
253: 
254: Conjecture 1.1 (Gerbner and Palmer [9]).
255: 
256: 
257: 
258: Let  r\geq 3  and  T  be a tree on  k  vertices. For  n=a(k-1)+b  with  0\leq b<k-1 ,
259: 
260: 
261: 
262: 
263:  \mathrm{ex}(n,K_{r},T)={\mathcal{N}}\bigl(K_{r},aK_{k-1}\cup K_{b}\bigr)=a\binom{k-1}{r}+\binom{b}{r}. 
268: 
269: 
270: 
271: For  r\geq k , we have  \mathrm{ex}(n,K_{r},T)=0 , since  T\subseteq K_{r} . The case  r=k-1  is also immediate. Indeed, every copy of  K_{k-1}  in a  T -free graph must be a connected component. Otherwise, an edge joining the clique to a vertex outside it would yield a copy of  T . Now we consider the next two cases, namely  r=k-2  and  r=k-3 . In both cases, we verify the conjecture and characterize all extremal graphs.
272: 
273: 
274: 
275: Theorem 1.2.
276: 
277: 
278: 
279: Let  r\geq 3  and  T  be a tree on  k  vertices. For  n=a(k-1)+b  with  0\leq b<k-1 , we have
280: 
737: 
738: 
739: 
740: We have proved Conjecture 1.1 when  r=k-2  or  r=k-3\geq 5 . Combining Theorem 1.2 with the immediate case  r=k-1 , we determine the exact value of  \mathrm{ex}(n,K_{r},T)  for  r\in\{k-3,k-2,k-1\} , where  k\geq 8  is required when  r=k-3 .
741: 
742: 
743: 
744: 
745: The proof for  r=k-3  relies on Lemmas 2.3 and 2.5, both of which require  r\geq 5 , and therefore does not cover the two cases  (k,r)\in\{(6,3),(7,4)\} . In particular, the conclusion of Lemma 2.3 does not extend to the case  (k,r)=(7,4) . Indeed, the graph formed by two copies of  K_{4}  sharing exactly one vertex does not contain the seven-vertex tree obtained by subdividing every edge of  K_{1,3}  once. Note that this graph is not a counterexample to Conjecture 1.1, since it contains only two copies of  K_{4} . It would be interesting to determine whether Conjecture 1.1 holds in these two exceptional cases and for all  3\leq r\leq k-4 .
746: 
747: 
748: 
749: 
750: Funding
751: 
752: 
753: 
754: 
785:       
786: 
787: [3]
788:  T.-W. Chao, Z. Dong, A simple proof of the Gan–Loh–Sudakov conjecture, Electron. J. Combin. 29(3) (2022) #P3.59.
789: 
790: 
791:       
792: 
793: [4]
794:  Z. Chase, The maximum number of triangles in a graph of given maximum degree, Adv. Comb. (2020) 10.
795: 
796: 
797:       

## 376280 Stein's pseudo-semidegree conjecture for long antipaths
222: 
223: An antidirected path is an oriented path in which every vertex sees either just incoming or just outgoing edges.
224: We prove that every oriented graph with minimum semidegree at least  k  contains an antidirected path of length  2k-1 .
225: This confirms a conjecture of Stein.
226:     
227: 
228: Keywords: Antidirected path; minimum semidegree; oriented graph
229:   
230: 
231: 
232: 
233: 1 Introduction
234: 
258: Oriented paths in tournaments (oriented complete graphs) are well studied.
259: A classical result of Rédei [12] states that every tournament contains a directed Hamilton path.
260: Grünbaum [4] proved that all but three tournaments contain a Hamilton antipath.
261: Rosenfeld [13] later conjectured that every tournament on at least  8  vertices contains all oriented Hamilton paths.
262: Thomason [19] proved the conjecture holds for tournaments on at least  2^{128}  vertices.
263: The conjecture was finally settled by Havet and Thomassé [6].
264: 
265: 
266: 
267: 
268: For oriented graphs  G , Jackson [7] proved that there is a directed path of length  2\delta^{0}(G)  or a directed Hamilton cycle.
269: Motivated by this result, Stein [15] proposed the following minimum semidegree condition forcing an oriented graph to contain any given orientation of a path, which can also be viewed as an analogue of Rosenfeld’s conjecture for oriented graphs.
270: 
271: 
272: 
273: Conjecture 1.1 (Stein [15]).
274: 
275: 
276: 
277: Every oriented graph  G  contains all oriented paths of length  2\delta^{0}(G)-1 .
278: 
279: 
280: 
281: 
282: 
283: If the conjecture holds, then it is best possible by considering (disjoint union of) any regular tournaments on  2\delta^{0}(G)-1  vertices.
284: There are various results supporting this conjecture.
285: The directed path case is proved by Jackson [7].
286: Chen, Hou, and Zhou [2] proved the conjecture for oriented paths with one change in direction.
287: For arbitrary orientations, Kelly [9] proved the case when  \delta^{0}(G)\geq 3n/8+o(n)  with  n  large, and Stein and Trujillo-Negrete [17] proved the case when  G  contains no oriented  4 -cycles.
288: 
289: 
290: 
291: 
292: In this paper, we investigate Conjecture 1.1 for antipaths.
293: The minimum pseudo-semidegree  \bar{\delta}^{0}(G)  of a non-empty digraph  G  is the minimum value amongst all non-zero in-degree and out-degree of all its vertices.
294: In other words, the minimum pseudo-semidegree is the maximum  k  such that each vertex has either out-degree  0  or out-degree at least  k , and has either in-degree  0  or in-degree at least  k .
295: If  G  is empty, then  \bar{\delta}^{0}(G)=0 .
296: Clearly,  \bar{\delta}^{0}(G)\geq\delta^{0}(G) .
297: Stein [16] proposed the following conjecture in terms of the minimum pseudo-semidegree condition.
298: 
299: 
300: 
301: Conjecture 1.2 (Stein [16]).
302: 
303: 
304: 
305: Every oriented graph  G  with  \bar{\delta}^{0}(G)\geq k  contains an antipath of length  2k-1 .
306: 
307: 
308: 
309: 
310: 
311: Note that up to isomorphism there is only one antipath of odd length (and two for even length).
312: Clearly, Conjecture 1.2 implies Conjecture 1.1 for antipaths.
313: In fact, the converse is true, by an observation of Stein and Zárate-Guerén (c.f. [18, Proof of Lemma 7.2]).
314: It is easy to see that Conjecture 1.2 holds for  k\leq 2 .
315: When  \delta^{0}(G)  is linear in  n , Stein and Zárate-Guerén [18] showed that Conjecture 1.2 holds asymptotically, that is, when  k=\eta n  and  \delta^{0}(G)\geq k+\varepsilon n .
316: Klimošová and Stein [10] proved that Conjecture 1.2 holds with  \bar{\delta}^{0}(G)\geq(6k-5)/4  instead.
317: The lower bound of  \bar{\delta}^{0}(G)  was later improved by Chen, Hou, and Zhou [1] to  (4k-1)/3 , and by Skokan and Tyomkyn [14] to  (10k-5)/8 .
318: Recently, Grzesik and Skrzypczyk [5] further improved the bound to  \bar{\delta}^{0}(G)>k-1+\sqrt{2k-4}/2 .
319: 
320: 
321: 
322: 
323: In this paper, we confirm Conjecture 1.2 (and so Conjecture 1.1 for antipaths).
324: 
325: 
326: 
327: Theorem 1.3.
328: 
329: 
330: 
331: Every oriented graph  G  with  \bar{\delta}^{0}(G)\geq k  contains an antipath of length  2k-1 .
332: 
1769: 
1770: 
1771: 
1772: The minimum pseudo-semidegree analogue of Conjecture 1.1 is false for other oriented paths.
1773: Indeed, any oriented path that is not antidirected contains a directed path of length  2 .
1774: Consider a complete bipartite graph  G[A,B]  in which every edge is directed from  A  to  B .
1775: Then  \bar{\delta}^{0}(G)=\min\{|A|,|B|\} , which can be arbitrarily large, but  G  does not contain any directed path of length  2 .
1776: 
1777: 
1778: 
1779: 
1780: Conjecture 1.1 is now known to hold for antipaths by Theorem 1.3, directed paths by Jackson [7], and paths with one change in direction by Chen, Hou, and Zhou [2].
1781: All these proofs implement some form of “rotation and extension” argument.
1782: However, we are unsure how to do so for arbitrary oriented paths.
1783: 
1784: 
1785: 
1786: 
1787: Data availability statement.
1788: There are no additional data beyond that contained within the
1789: main manuscript.
1868: 
1869: 
1870: Oriented Hamiltonian paths in tournaments: a proof of Rosenfeld’s
1871: conjecture.
1872: 
1873: 
1874: J. Combin. Theory Ser. B, 78(2):243–273, 2000.
1875: 
1876: 
1877:       
1878: 
1879: [7]
1880: 

## 376300 Universality of the oriented minimum spanning tree limit for positive continuous weights
3384: 
3385: 
3386: 
3387: Conjecture 6.1.
3388: 
3389: 
3390: 
3391: Theorem 1.2 is true for i.i.d. weights  (W_{\vec{e}})_{\vec{e}\in\vec{E}}  with continuous distributions supported in  (0,\infty) .
3392: 
3393: 
3394: 
3395: 
3396: 
3445: 
3446: 
3447: The existence of local limit for item d. was proved in [23] for i.i.d. Exponential (1)  weights, but a more detailed description of the limit is unknown. There is a natural class of  d -regular expanders which converge locally to the infinite  d -regular tree.
3448: A natural question is whether the limit of the MSA in such  d -regular expanders is the same as that of the wired  d -regular tree. We conjecture this is the case.
3449: 
3450: 
3451: 
3452: Conjecture 6.3.
3453: 
3454: 
3455: 
3456: Let  G_{n}  be an expander sequence converging locally to the  d -regular tree. Then the local limit of item c. and d. in Question 6.2 matches.
3457: 
3458: 
3459: 
3460: 
3461: 

## 376305 Frankl–Kupavskii weighted-construction conjecture for the Erdős–Kleitman problem
237: 
238: For integers  n\geq s\geq 2 , let  e(n,s)  be the maximum size of a family  \mathcal{F}\subseteq 2^{[n]}  with no  s  pairwise disjoint members.
239: The problem of determining  e(n,s) , now called the Erdős–Kleitman problem, is closely related to the well-known Erdős matching problem.
240: Frankl and Kupavskii posed a meta-conjecture predicting that the maximum is always attained by a weighted family.
241:     
242: 
243: Fix  m\geq 3 , write  n=ms+c  with  0\leq c<s , and set  \ell=s-c .
244: For  0\leq k\leq m , let  a_{k}=ms-kc-1 .
245: For  A\in\binom{[n]}{a_{k}} , define
246:     
247: 
248: 
249: 
259: 
260: We show that for  1\leq k\leq m-1 , all families  \mathcal{H}^{k}  are uniquely extremal in some ranges of  c .
261: More precisely, we prove that for every  m\geq 3  and every  1\leq k\leq m-1 , there exist constants  \alpha=\alpha(m,k)>0 ,  \beta=\beta(m,k)>0  and an integer  s_{0}=s_{0}(m,k)  such that, for all integers  s\geq s_{0}  and all integers  c  with  0\leq c<s , the only extremal families for  e(n,s)  are the families  \mathcal{H}^{k}(m,s,\ell;A)  with  A\in\binom{[n]}{a_{k}}  whenever  \beta s^{(k-1)/k}\leq c\leq\alpha s^{k/(k+1)} .
262: In particular, this result determines an infinite number of new extremal families for the Erdős–Kleitman problem and verifies the Frankl–Kupavskii meta-conjecture in these ranges.
263: This also provides a quantitative extension of the result of Kupavskii and Sokolov on the extremality of  \mathcal{H}^{1} .
264:   
265: 
266: 
267: 
268: 1 Introduction
269: 
270: 
271: 
289: 
290: 
291: 
292: The Erdős–Kleitman can be seen as the non-uniform counterpart of the well-known Erdős Matching Conjecture [5].
293: For  n\geq rs , the conjecture asserts that
294: 
295: 
296: 
297: 
298:  \max\left\{|\mathcal{G}|:\mathcal{G}\subseteq\binom{[n]}{r}\text{ and }\nu(\mathcal{G})<s\right\}=\max\left\{\binom{rs-1}{r},\binom{n}{r}-\binom{n-s+1}{r}\right\}. 
299: 
300: 
301: 
302: The two terms on the right arise, respectively, from taking all  r -sets on an  (rs-1) -element ground set and from taking all  r -sets that meet a fixed  (s-1) -set.
303: For  r=2 , it is the theorem of Erdős and Gallai [6], while for  s=2 , it reduces to the Erdős–Ko–Rado theorem [7].
304: The conjecture is known for  r=3  by Frankl [9], following earlier work of Łuczak and Mieczkowska [29].
305: For arbitrary  r , Frankl and Kupavskii [14] substantially extended the range in which the family of all  r -sets meeting a fixed  (s-1) -set is extremal. They also established a Hilton–Milner-type stability theorem [13].
306: More recently, Frankl, Lu, Ma and Wu [15] proved the conjecture for  r=4  in the range  n\geq 5(s-1)  when  n  is sufficiently large, using a stability theorem for shifted  4 -uniform families.
307: In a subsequent preprint, Hou, Hu and Liu [16] proved the conjecture for  r=4  and  n\geq 4s  whenever  s\geq 6962 .
308: Nevertheless, the conjecture remains open in general for every  r\geq 4 .
309: Structural theories for perfect and almost-perfect matchings in dense uniform hypergraphs likewise emphasize the role of space and divisibility barriers; see Keevash and Mycroft [22] and the survey of Keevash [18].
310: Matchings also arise naturally through transversals.
311: Keevash, Pokrovskiy, Sudakov and Yepremyan [23] proved that every Steiner triple system of order  n  has a matching of size  n/3-O(\log n/\log\log n) , and Montgomery [30] later improved this bound to at least  (n-4)/3  for all sufficiently large  n .
312: For a systematic account of the correspondence between Latin transversals and matchings in  3 -partite  3 -uniform hypergraphs, see Montgomery [31].
313: 
314: 
315: 
316: 
317: More broadly, the Erdős–Kleitman problem belongs to the study of extremal families in the Boolean cube.
353: 
354: 
355: a contradiction.
356: Frankl and Kupavskii [10] proposed the following meta-conjecture.
357: 
358: 
359: 
360: Conjecture 1.1 (Frankl–Kupavskii [10]).
361: 
362: 
363: 
364: For any integers  n\geq s\geq 2 , the maximum in the definition of  e(n,s)  is attained by a family  \mathcal{F}(w)  for some  w\colon[n]\to\mathbb{R}_{\geq 0}  satisfying  \sum_{i=1}^{n}w(i)<s .
365: 
366: 
367: 
368: 
369: 
377: 
378: 
379: Indeed, if  w_{\mathcal{P}}(i)=2/(m+1)  for  i\leq\ell-1  and  w_{\mathcal{P}}(i)=1/(m+1)  for  i\geq\ell , then  \mathcal{P}(m,s,\ell)=\mathcal{F}(w_{\mathcal{P}})  and  \sum_{i}w_{\mathcal{P}}(i)=s-1/(m+1)<s .
380: Frankl and Kupavskii [10] also posed the following conjecture.
381: 
382: 
383: 
384: Conjecture 1.2 (Frankl–Kupavskii [10]).
385: 
386: 
387: 
388: Suppose that  s\geq 2 ,  m\geq 1  and  n=s(m+1)-\ell  for some  \ell  with  1\leq\ell\leq\lceil s/2\rceil .
389: Then
390: 
391: 
392: 
393: 
399: 
400: 
401: 
402: They also verified Conjecture 1.2 in several ranges.
403: Kupavskii and Sokolov [28] later proved that, for every fixed  m  and every  \varepsilon>0 , the conjecture holds when  s  is sufficiently large and  \ell\leq(1/2-\varepsilon)s .
404: In [2], the authors of this paper showed that, for every fixed  m\geq 3  and all sufficiently large  s ,  \mathcal{P}(m,s,\ell)  is, up to relabelling, the unique extremal family when  1\leq\ell\leq((m+1)/(2m+1)-o(1))s , confirming Conjecture 1.2.
405: 
406: 
407: 
408: 
409: The present paper studies another class of weighted constructions.
410: For  0\leq k\leq m , let  a_{k}=ms-kc-1 .
411: For  A\in\binom{[n]}{a_{k}} , define
412: 
413: 
438:             
439:             
440:           In previous papers,  \mathcal{H}^{0}(m,s,\ell)  and  \mathcal{H}^{1}(m,s,\ell)  are often denoted by  \mathcal{W}(m,s,\ell)  and  \mathcal{Q}(m,s,\ell) , respectively. are the only extremal families for  e(sm+1,s)  when  s  is sufficiently large. For every fixed  m  and  c\geq 2 , there exists  s_{0}=s_{0}(m,c)  such that  \mathcal{H}^{1}(m,s,\ell)  is the unique shifted extremal family for  e(sm+c,s)  when  s\geq s_{0} .
441: They also posed the following conjecture:
442: 
443: 
444: 
445: 
446:  e(n,s)=\max\left\{|\mathcal{H}^{0}(m,s,\ell)|,|\mathcal{H}^{1}(m,s,\ell)|,|\mathcal{H}^{m}(m,s,\ell)|,|\mathcal{P}(m,s,\ell)|\right\}. 
447: 
448: (1.2)
449: 
450: 
451: In [26], they prove the conjecture when  n\leq 3s , which provides evidence for this conjecture.
452: Recently, in [3], the authors of this paper proved that for every  m\geq 3 , there are constants  \beta_{m},\delta_{m}>0  such that  \mathcal{H}^{m}(m,s,\ell;A) 22
453:             2
454:             
455:             
456:             
457:             
458:             
459:             
460:             
461:           In previous papers,  \mathcal{H}^{m}(m,s,\ell;A)  is often denoted by  \mathcal{P}^{\prime}(m,s,\ell;A) . is, up to relabelling, the unique extremal family for  e(sm+c,s)  when  s  is sufficiently large and  \beta_{m}s^{(m-1)/m}\leq c\leq\delta_{m}s .
462: In the same paper [3], the authors also showed that  |\mathcal{H}^{m-1}(m,s,\ell)|  is larger than the sizes of all four candidates in (1.2) for some values of  c , thus disproving this conjecture of Kupavskii and Sokolov.
463: Hence, the families  \mathcal{H}^{k}(m,s,\ell) , for  1\leq k\leq m-1 , are natural extremal candidates for  e(n,s) .
464: 
465: 
466: 
467: 
468: The main contribution of this paper is to confirm the extremality of these families.
469: 
470: 
471: 
500: 
501: 
502: 
503: Together with the known results [2, 3, 26, 27, 28], Theorem 1.3 provides further evidence for Conjecture 1.1, since in all these cases the extremal value is attained by a weighted family.
504: 
505: 
506: 
507: 
508: For a family  \mathcal{F}\subseteq 2^{[n]} , its upward closure  \operatorname{cl}(\mathcal{F})  is  \{G\subseteq[n]:\text{there exists }F\in\mathcal{F}\text{ with }F\subseteq G\} .
509: We say that  \mathcal{F}  is upward closed if  \operatorname{cl}(\mathcal{F})=\mathcal{F} .
510: The proof of Theorem 1.3 proceeds through a reduction to upward closed families with no members of size less than  m .
511: This is the natural setting because  \mathcal{H}^{k}(m,s,\ell;A)  itself contains no set of size below  m .
512: 
538: 
539: 
540: Theorem 1.3 suggests that, after including all the families  \mathcal{H}^{k} , the known weighted constructions may form a complete list of extremal families.
541: We therefore propose the following conjecture.
542: 
543: 
544: 
545: Conjecture 1.4.
546: 
547: 
548: 
549: For every  n  and  s  with  n=sm+c=s(m+1)-\ell , we have
550: 
551: 
552: 
553: 
554:  e(n,s)=\max\left\{|\mathcal{H}^{0}(m,s,\ell)|,|\mathcal{H}^{1}(m,s,\ell)|,\ldots,|\mathcal{H}^{m}(m,s,\ell)|,|\mathcal{P}(m,s,\ell)|\right\}. 
2945: [2]
2946: 
2947: C. Chi and Y. Wang,
2948: A solution to Frankl and Kupavskii’s conjecture concerning
2949: Erdős–Kleitman matching problem,
2950: arXiv:2605.06389, 2026.
2951: 
2952: 
2953:       
2954: 
2955: [3]
2956: 
2957: C. Chi and Y. Wang,
3054: [14]
3055: 
3056: P. Frankl and A. Kupavskii,
3057: The Erdős Matching Conjecture and concentration inequalities,
3058: J. Combin. Theory Ser. B 157 (2022), 366–400.
3059: 
3060: 
3061:       
3062: 
3063: [15]
3064: 
3065: P. Frankl, H. Lu, J. Ma and Y. Wu,
3066: Towards the Erdős matching conjecture for  4 -uniform hypergraphs: stability and applications,
3067: arXiv:2602.19230, 2026.
3068: 
3069: 
3070:       
3071: 
3072: [16]
3073: 
3074: J. Hou, C. Hu and X. Liu,
3075: A finite-board reduction for the Erdős Matching Conjecture and the  4 -uniform case via exact certificates,
3076: arXiv:2605.26060, 2026.
3077: 
3078: 
3079:       
3080: 
3081: [17]
3082: 
3083: P. Keevash,
3084: Shadows and intersections: stability and new proofs,
3136: [23]
3137: 
3138: P. Keevash, A. Pokrovskiy, B. Sudakov and L. Yepremyan,
3139: New bounds for Ryser’s conjecture and related problems,
3140: Trans. Amer. Math. Soc. Ser. B 9 (2022), 288–321.
3141: 
3142: 
3143:       
3144: 
3145: [24]
3146: 
3147: P. Keevash and B. Sudakov,
3148: Set systems with restricted cross-intersections and the minimum rank of inclusion matrices,
3199: [30]
3200: 
3201: R. Montgomery,
3202: A proof of the Ryser–Brualdi–Stein conjecture for large even  n ,
3203: arXiv:2310.19779, 2023.
3204: 
3205: 
3206:       
3207: 
3208: [31]
3209: 
3210: R. Montgomery,
3211: Transversals in Latin squares,

## 376334 Pokrovskiy–Sudakov cycle Ramsey goodness conjecture
211: 
212: Simply put, expanders are graphs with good connectivity properties yet comparatively few edges. Over the last fifty years, expanders have played an important role in a host of areas in computer science and mathematics, from error-correcting codes and efficient communication networks to problems in extremal graph theory. For an overview of many applications of expanders, we recommend the brief introduction by Sarnak [109], the survey of Hoory, Linial and Wigderson [55] covering many applications in computer science and mathematics, the survey by Lubotzky [83] on further applications in mathematics, and the survey by Krivelevich [70] on applications in graph theory.
213: The idea of expanders was first introduced by Bassalygo and Pinsker [6] in 1973. That expanders exist, e.g. that an  n -vertex graph can have relatively strong connection properties yet only  O(n)  edges, was originally shown by Pinsker [100] using essentially a probabilistic argument.
214: The first explicit examples were given by Margulis [88] and by Gabber and Galil [46]. This survey will concentrate on recent advances in extremal graph theory using a weak form of expansion known as sublinear expansion, which has seen the resolution of a range of long-standing conjectures and other advances. Throughout, we will supress the
215: more technical details, and happily refer the reader to the recent extensive survey on sublinear expansion by Letzter [78] for more specialist details.
216: 
217: 
218: 
219: 
220: In graph theory, the appearance and use of expanders can roughly be divided into the following four (overlapping) categories:
221: 
222: 
223: 
324: An important class of problems in extremal graph theory asks how many edges a graph on a fixed vertex set must have before the graph necessarily has a particular property of interest. When this property of a graph  G  is the containment of a copy of another graph  H  as a subgraph (i.e., edges and vertices can be deleted from  G  to make it isomorphic to  H ), this is known as a Turán problem. The answer has long been known exactly whenever
325:  H  is the complete graph  K_{n}  (which has  n  vertices and every possible edge) due to Turán [119], who generalised the earlier result of Mantel [87] for  n=3 . More generally, when  H  is not bipartite, the
326: asymptotic behaviour of the Turán number  \mathrm{ex}(n,H) , the maximum number of edges an  n -vertex graph can have yet contain no copy of  H  is a well-known consequence of the Erdős-Stone theorem [42]. When  H  is bipartite,  \mathrm{ex}(n,H)  is known to be  o(n^{2})  (from the Erdős-Stone theorem), but determining the correct asymptotic behaviour here is extremely difficult.
327: For every bipartite graph  H  containing at least one cycle, it is known there is some  \varepsilon>0  such that  n^{1+\varepsilon}\leq\mathrm{ex}(n,H)\leq n^{2-\varepsilon}  (see, for example, [4]). Not only is determining the correct power of  n  for any such graph  H  a very difficult problem, finding a wide variety of graphs with different exponents is a fascinating problem. This is the subject of the ‘rational exponents conjecture’ of Erdős and Simonovits (see, e.g., [36]), which says that for each rational  \alpha\in(1,2)  there is some graph  H  for which  \mathrm{ex}(n,H)=\Theta(n^{\alpha}) . An overview of progress on this problem can be found in the recent work of Conlon and Janzer [26], but subdivisions play an important role here as subdividing edges of  H  should reduce  \mathrm{ex}(n,H)  if bipartiteness is maintained. Subdivided graphs are good candidates, then, for graphs with different exponents in the asymptotics of their Turán number, as seen for example in the work of Jiang and Qiu [62].
328: 
329: 
330: 
331: 
332: If an  n -vertex graph has  n^{1+o(1)}  edges then we cannot infer from its number of edges that it contains a copy of any fixed subgraph. In this sparse regime, we may still expect to find some structure in the graph. For example, any  n -vertex graph with  n  edges must contain some cycle, and, thus, a subdivision of  K_{3} . In such a sparse regime, instead of directly bounding the number of edges we often instead equivalently bound the average degree of a graph, that is, the average number of edges adjacent to the vertices of the graph. Any graph with average degree at least 2 thus contains a subdivision of  K_{3} . In 1967, Mader [84] proved that, more generally, for each  t\geq 3 , any graph with sufficiently large average degree (depending only on  t ) must contain a subdivision of  K_{t} .
333: Therefore, we can define  d(t)  as the smallest  d  such that every graph with average degree more than  d  has a  K_{t} -subdivision.
334: Mader’s work showed that  d(t)=O(2^{3t}) , but Mader [84], and Erdős and Hajnal [41], independently conjectured that  d(t)=O(t^{2}) .
335: In 1994, Bollobás and Thomason [10] proved this conjecture, very shortly before Komlós and Szemerédi [68] improved some of their then-recent work [67] showing  d(t)=t^{2+o(1)}  to give a rather different proof, so that we have the following result.
336: 
337: 
338: 
339: Theorem 2.1.
340: 
341: 
342: 
343:  d(t)=\Theta(t^{2}) .
344: 
352: 
353: 
354: 
355: Conjecture 2.2.
356: 
357: 
358: 
359:  d(t)=\left(\frac{9}{64}+o(1)\right)t^{2} .
360: 
361: 
362: 
363: 
364: 
441: 
442: 
443: 
444: Relevant to us is a variation of the extremal problem for minors, introduced by Fiorini, Joret, Theis and Wood [45]. For each fixed graph  H , they conjectured that any  n -vertex graph with average degree only slightly above that required to guarantee an  H -minor must have moreover an  H -minor with only  O(\log n)  vertices.
445: In the influential work of Shapira and Sudakov [110] mentioned above, it was shown using sublinear expansion that such a minor exists with only  O(\log n\log\log n)  vertices. Subsequently, the conjecture was proved in full by Montgomery [91], who also showed some analogous results for subdivisions.
446: 
447: 
448: 
449: 
450: Another topic important in the recent development of tools involving sublinear expansion concerns a conjecture of Mader on subdivisions from 1999. Recall from Section 2 that some average degree condition of  O(t^{2})  is known to force the existence of a  K_{t} -subdivision. Mader [86] conjectured that an average degree condition only linear in  t  is sufficient to force the existence of a  K_{t} -subdivision in any graph which has no cycles of length 4. (Roughly speaking, this would say that extremal examples for  K_{t} -subdivision-free graphs contain some dense structures, which can be avoided with such a  C_{4} -free condition.)
451: Following bounds of Kühn and Osthus [73], and a related result of Balogh, Liu and Sharifzadeh [5] for graphs with no cycles of length 6, Mader’s conjecture was proved in 2017 by Liu and Montgomery [80]. All of these results use sublinear expansion, where the improvements require many new ideas so that paths can be found while reserving structures to facilitate later constructions (details of which can be found in the papers themselves, as well as to some extent in the survey by Letzter [78]).
452: 
453: 
454: 
455: 
456: 5 Cycle lengths.
457: 
458: 
459: 
460: 
461: The discussion of Turán numbers in Section 2 implies we cannot expect an  n -vertex graph with  n^{1+o(1)}  edges to necessarily have a cycle of any fixed length. However, we can still expect to be able to say something more generally about its cycle lengths. For any graph  G , the cycle length set  \mathcal{C}(G)  of  G  (also known as its cycle spectrum) is the set of integers  k  such that  G  contains a cycle of length  k .
462: In 1966, Erdős and Hajnal [40] considered the harmonic sum of the cycle lengths of a graph  G  as a measure of the density of  \mathcal{C}(G) . In particular, they asked whether the sum  \sum_{\ell\in\mathcal{C}(G)}\ell^{-1}  can be made arbitrarily large by imposing a bound on the chromatic number  \chi(G)  of a graph  G  (i.e., the minimum number of colours required to colour the vertices of  G  so that every edge is between vertices of different colours). Later, Erdős [30] wrote that they felt this should be possible even by imposing a bound only on the average degree of a graph, and this was confirmed in 1984 by Gyárfás, Komlós and Szemerédi [51], who showed that any graph  G  with average degree  d  satisfies  \sum_{\ell\in\mathcal{C}(G)}\ell^{-1}=\Omega(\log d) .
463: In work discussed further below, Liu and Montgomery [81] used sublinear expansion to improve this bound to  \sum_{\ell\in\mathcal{C}(G)}\ell^{-1}\geq(1/2-o(1))\log d .
464: As anticipated by Erdős [30], the constant  1/2  is unimprovable here, as if  G  is the complete bipartite graph with  d  vertices in each class, then  G  has average degree  d  while  \mathcal{C}(G)  contains only every even number from  4  to  2d , so that  \sum_{\ell\in\mathcal{C}(G)}\ell^{-1}=(1/2+o(1))\log d . Erdős [36] later conjectured something even stronger: that  \sum_{\ell\in\mathcal{C}(G)}\ell^{-1}  is minimised over all graphs with average degree at least  d  by exactly this complete bipartite graph. That this is true when  d  is sufficiently large is shown in forthcoming work of Milojević, Montgomery, Pokrovskiy and Sudakov.
465: 
466: 
467: 
468: 
469: It requires many edges to guarantee a cycle of some fixed length. Given instead a sequence  \ell_{1},\ell_{2},\dots  of possible lengths, might we need far fewer edges to guarantee a cycle with length in this sequence?
470: In 1977, Bollobás [7] showed that this is possible for infinite arithmetic progressions containing even numbers, confirming a conjecture of Burr and Erdős [35].
471: We say that a sequence  \ell_{1},\ell_{2},\ldots  is unavoidable with high average degree if there is some  d  such that any graph with average degree at least  d  contains a cycle with length in  \ell_{1},\ell_{2},\ldots . In these words, Bollobás’s result is that any infinite arithmetic progression containing even numbers is unavoidable with high average degree. Note that any sequence which is unavoidable with high average degree must trivially contain infinitely many even numbers, as complete bipartite graphs have very large average degree yet no odd length cycle.
472: 
473: 
474: 
475: 
476: In 2005, Verstraëte [122] confirmed a conjecture of Erdős by showing that there is some sequence of vanishing density which is unavoidable with large average degree. A few years later, Sudakov and Verstraëte [114] were able to show that many sparse sequences are unavoidable under the imposition of an average degree condition that grows extremely slowly in the number of vertices. Recently, using sublinear expansion, Liu and Montgomery [81] showed that many sparse sequences are unavoidable with high average degree (i.e., a condition independent of the number of edges in a graph).
477: In particular, this answered a question of Erdős [32] by confirming that sufficiently large average degree is enough to guarantee a cycle whose length is a power of 2. On this particular question, Erdős and Gyárfás
478: (see, for example, [37]) conjectured that minimum degree 3 should be enough for this, but later thought this may be too strong. Certainly, if the answer to the following question is positive then confirming it would require very substantial new ideas.
479: 
480: 
481: 
482: Question 5.1.
483: 
484: 
485: 
486: Does every graph with minimum degree at least 3 contain a cycle of length  2^{k}  for some  k\geq 2 ?
487: 
512: 
513: 
514: 
515: Conjecture 5.2.
516: 
517: 
518: 
519: For each  \varepsilon>0 , there exists some  d_{0}  such that, for every  d\geq d_{0} , every  d -regular  (\varepsilon,d) -expander contains a Hamilton cycle.
520: 
521: 
522: 
523: 
524: 
525: Even in graphs with a much stronger expansion condition (along the lines of Definition 1.1 with large constance  \alpha ), it is difficult to show that Hamilton cycles exist, as was the subject of an influential conjecture of Krivelevich and Sudakov [71] from 2003. This conjecture states that, when  d  is sufficiently large, every  d -regular expander graph contains a Hamilton cycle, using a definition of expansion via the spectral properties of a graph. After a long line of research, this was recently confirmed by Draganić, Montgomery, Munhá Correia, Pokrovskiy and Sudakov [29]. Using Definition 1.1, the more general result of [29] says that there is some constant  C>0  such that any  n -vertex  C -expander, in which moreover any two disjoint vertex sets with size at least  n/C  have an edge between them, contains a Hamilton cycle.
526: 
527: 
528: 
529: 
530: We conclude this section with a discussion of an interesting problem on cycle length sets where it seems likely the developing techniques involving sublinear expansion will have some import.
531: The following problem of Erdős and Faudree (see, for example, [38]) concerns the number of sets which are realisable as the cycle length set of an  n -vertex graph. Letting  f(n)  be the number of subsets  A\subset\{3,\ldots,n\}  for which there is some  n -vertex graph  G  with  \mathcal{C}(G)=A . What bounds can we achieve on  f(n) ? In addition to the trivial upper bound  f(n)\leq 2^{n-2} , a construction of Faudree shows that  f(n)\geq 2^{n/2} . Erdős and Faudree asked in particular whether  f(n)=o(2^{n})  and  f(n)=\omega(2^{n/2}) . In 2004,
532: Verstraëte [121] showed that the answer to the first question is yes, by showing that  f(n)\leq 2^{n-n^{0.1-o(1)}} .
533: As it seems likely that  f(n)=O(2^{n/2}) , answering the second question is potentially extremely difficult, requiring a deep structural result. Very recently, Nenadov [97] optimised several components of Verstraëte’s argument to show that  f(n)\leq 2^{n-n^{0.5-o(1)}} . The argument requires a structural characterisation of certain classes of graphs, in which the cycle length sets of sparse graphs are particularly relevant. Thus, using sublinear expansion to push these methods further is a promising possibility.
534: 
552: 
553: 
554: 
555: Noting that Walecki’s result decomposes Eulerian complete graphs into as few cycles as possible, a natural question is whether every  n -vertex Eulerian graph has a decomposition into  O(n)  cycles. The following conjecture of Erdős and Gallai [33] from 1966 is easily seen to be equivalent to this.
556: 
557: 
558: 
559: Conjecture 6.1.
560: 
561: 
562: 
563: Every  n -vertex graph has a decomposition into  O(n)  cycles and edges.
564: 
565: 
566: 
567: 
568: 
569: Erdős later observed that a construction of Gallai can be improved to show that at least  (3/2-o(1))n  cycles and edges may be needed to decompose an  n  vertex graph. That Conjecture 6.1 remains open is in stark contrast to the corresponding case for decompositions into cycles and paths. Here, thanks to an old result of Lovász [82], we have the exactly tight bound that any  n -vertex graph can be decomposed into at most  \lceil n/2\rceil  cycles and paths. This follows by an elegant inductive argument, and the lack of a corresponding argument for Conjecture 6.1 indicates it would be a much deeper structural result if true.
570: 
571: 
572: 
573: 
574: When making Conjecture 6.1, Erdős and Gallai [33] observed that every  n -vertex graph has a decomposition into  O(n\log n)  cycles and edges. Such a decomposition can be found by simply iteratively removing a longest cycle from the graph until no cycles (and hence at most  n-1  edges) remain. A simple undergraduate exercise is that any graph with average degree at least  d\geq 2  has a cycle with length at least  d/2 . (See also the optimal bounds on this problem in the Erdős-Gallai theorem [47].) Tracking, then, the average degree of a graph as longest cycles are removed, it will take the removal of  O(n)  cycles for the average degree to drop at least by half, at any stage, and thus after the removal of  O(n\log n)  cycles there will be no more cycles to remove.
575: 
576: 
577: 
578: 
579: Conjecture 6.1 may be considered a stout problem. Despite its inclusion in many of Erdős’s problem collections, the simple bound of  O(n\log n)  stood as the state-of-the-art for almost 50 years. Finally, in 2014, Conlon, Fox and Sudakov [24] showed that  O(n\log\log n)  cycles and edges suffice to decompose any  n -vertex graph.
580: A decade later, Bucić and Montgomery [15] reduced this bound further to  O(n\log^{*}n) , where  \log^{*}n  is the iterated logarithm function, i.e., the least  k  such that the  k -fold logarithm of  n ,  \log(\log(\ldots\log(n))) , is at most  1 .
581: 
582: 
583: 
584: 
585: The improvements in [24, 15] rely on expansion as a key tool. From Lovász’s result quoted above, we know any  n -vertex graph decomposes into  O(n)  cycles and paths. The basic approach of Conlon, Fox and Sudakov [24] is to set aside vertices independently at random with some small probability, before decomposing the edges not containing any reserved vertex into few cycles and paths. After edge-disjointly joining up the paths into cycles if possible (using the reserved vertices), the argument is then iterated on the edges not covered by cycles so far. If any graph with average degree  d  can be decomposed into  O(n)  cycles and a graph of leftover edges of average degree at most (say)  d^{9/10} , then within  O(\log\log n)  iterations no cycles will remain, achieving a decomposition into  O(n\log\log n)  cycles and  O(n)  edges.
586: This outline is significantly simplified, and making it work is a difficult task, but essentially Conlon, Fox and Sudakov [24] were able to show that it works in graphs satisfying a strong expansion condition. The expansion condition had to be strong enough that some expansion condition involving only the reserved vertices is likely to hold, strong enough that the paths from the decomposition into cycles and paths can be joined up into cycles using the inherited expansion conditions. Notably, the proof in [24] uses that not only does any graph with enough edges contain an expander, but all except very few of the edges can be decomposed into expanders.
587: 
588: 
589: 
590: 
591: The work of Bucić and Montgomery [15] very roughly followed the outline used by Conlon, Fox and Sudakov, but used sublinear expansion in place of the stronger expansion conditions. This introduces a raft of complications and requires many more ideas, in particular in using sublinear expansion in combination with the random selection of vertices, a difficult proposition made easier by ideas of Tomon [118] (from work mentioned below).
592: If Conjecture 6.1 is true, then sublinear expansion may prove useful to prove it, but this appears to be very difficult. Indeed, any reasonable proof that works through a ‘memoryless’ iterative decomposition presumably will at best give a bound of the form  O(n\log^{*}n) . Altering cycles found in earlier iterations to reduce the number of cycles used, or decomposing the graph in one step, seems to require a deeper structural understanding of which graphs are difficult to decompose into few cycles.
593: 
594: 
595: 
596: 
597: 7 Cycles with additional properties.
598: 
599: 
600: 
601: 
605: 
606: 
607: 
608: The first of these questions was answered fairly promptly by Bollobás [8], who showed that any  n -vertex graph without two edge-disjoint cycles  S_{1}  and  S_{2}  such that  V(S_{1})\subset V(S_{2})  (i.e., such that  S_{1}  and  S_{2}  are nested) must have  O(n)  edges. In 1996, Chen, Erdős and Staton [22] then confirmed a conjecture of Bollobás by generalising this result: for each fixed  k , any  n -vertex graph without  k  edge-disjoint cycles  S_{1},\dots,S_{k}  with  V(S_{1})\subset\dots\subset V(S_{k})  has  O(n)  edges.
609: 
610: 
611: 
612: a)         
613: b)  
614:        
615: c)  
616: Figure 6: a) Nested cycles, b) nested cycles with no geometric crossing, and c) two cycles nested with each other.
617: 
618: 
619: 
620: 
621: In the second question, two edge-disjoint cycles  S_{1},S_{2}  are nested with no geometric crossings if  V(S_{1})\subset V(S_{2})  and they can be drawn together in the plane without crossing edges. In 2022, Fernández, Kim, Kim and Liu [49] used sublinear expansion to answer this question, showing that any  n -vertex graph with no pair of nested cycles with no geometric crossings must have  O(n)  edges. Interestingly, as the proof takes a shortest cycle in a sublinear expander as the ‘inner’ cycle, the methods seem limited to finding only two such cycles, leaving the following natural conjecture open.
622: 
623: 
624: 
625: Conjecture 7.1.
626: 
627: 
628: 
629: For every  k , there is some  g(k)  such that any graph with average degree at least  g(k)  has  k  nested cycles with no geometric crossings.
630: 
631: 
632: 
633: 
634: 
683: 
684: 
685: The most interesting open extremal problem on rainbow cycles is the Turán-style problem for a cycle of any length. Raised as a question by
686: Keevash, Mubayi, Sudakov and Verstraëte [64], we phrase this as the following conjecture.
687: 
688: 
689: 
690: Conjecture 8.1.
691: 
692: 
693: 
694: Every properly-coloured  n -vertex graph with no rainbow cycle has  O(n\log n)  edges.
695: 
696: 
697: 
698: 
699: 
700: This problem has interesting applications to coding theory and to additive combinatorics, for a discussion of which see the survey Sudakov [113, Section 2.1].
701: If true, Conjecture 8.1 is correct up to a constant multiple, as seen by the following example of Keevash, Mubayi, Sudakov and Verstraëte [64].
702: Let  H  be the graph whose vertex set is the power set of  [k]=\{1,\dots,k\} ,  \mathcal{P}([k]) , where between sets  A  and  B  with  A\triangle B=\{i\}  we put an edge with colour  i . Thus,  H  has  n:=2^{k}  vertices, and  {kn}/2  edges, and is properly coloured. Walking around a cycle in  H  starting with a vertex  A\subset[k] , we add or remove an element corresponding to the colour of that edge. Thus, as this walk ends back at  A , the number of edges of each colour in the cycle must be even. In particular, then,  H  contains no rainbow cycle, but has  n  vertices and  \Theta(n\log n)  edges.
703: 
704: 
705: 
706: a)  
707:        
708: b)  
709:        
710: c)  
713: 
714: 
715: 
716: From the initial bound towards Conjecture 8.1 given by Keevash, Mubayi, Sudakov and Verstraëte [64], there has since been a steady string of improvements. Until recently, the best result was independently shown by Janzer and Sudakov [59] and Kim, Lee, Liu and Tran [66], who showed that any properly-coloured graph without an  n -vertex cycle has  O(n\log^{2}n)  edges using an homomorphism counting approach introduced by Janzer [57]. Previously, Das, Lee and Sudakov [27] had given a bound of the form  n^{1+o(1)}  using some expansion ideas. With sublinear expansion it is easy to find paths between vertices, but for bounds towards Conjecture 8.1 we need methods capable of finding rainbow paths.
717: This was achieved very effectively in a beautiful paper of Alon, Bucić, Sauermann, Zakharov and Zamir [2], who showed that every properly-coloured  n -vertex graph without a rainbow cycle has  O(n\log n\log\log n)  edges.
718: The authors of [2] express some doubts over the veracity of Conjecture 8.1, and it may be that their bound (or something inbetween) is instead the truth. While sublinear expansion may be a crucial tool if further improvements can be made, it is notable that the bound in [2] matches the best bound on the length of a path that can be found between arbitrary vertex pairs using sublinear expansion (see the relevant discussion in Section 3).
719: 
720: 
721: 
722: 
723: A natural generalisation of Conjecture 8.1 is to consider the problem for subdivisions of complete graphs more generally, for which the following may be true.
724: 
725: 
726: 
727: Conjecture 8.2.
728: 
729: 
730: 
731: For each  k\geq 3 , every properly-coloured  n -vertex graph with no rainbow  K_{k} -subdivision has  O(n\log n)  edges.
732: 
733: 
734: 
735: 
736: 
737: After an initial bound by Jiang, Methuku and Yepremyan [61], the first result showing that every properly-coloured  n -vertex graph with no rainbow  K_{k} -subdivision has  n\log^{O(1)}n  edges was given by Jiang, Letzter, Methuku and Yepremyan [60]. Currently, the best known bound is one of Wang [124] of the form  n(\log n)^{2+o(1)} , proved by optimising a more general argument of Tomon [118] to this particular setting.
738: While homomorphism counting approaches give some effective bounds towards Conjecture 8.1, the additional structure required to find rainbow subdivisions more generally seem beyond them and instead all the results towards Conjecture 8.2 mentioned here follow using expansion in some form. As can be expected, for the state-of-the-art bound of  n(\log n)^{2+o(1)}  by Wang [124], sublinear expansion is used. While a cursory look at the progress by Alon, Bucić, Sauermann, Zakharov and Zamir [2] towards Conjecture 8.1 might suggest a similar bound of  O(n\log n\log\log n)  can be achieved towards Conjecture 8.2, this appears actually to be a very substantial problem. The bound in [2] follows using a subtle and very clever argument using random selections of the colours which does not seem to be amenable to constructing rainbow subdivisions more generally. This context in particular makes giving a bound of say the form  n\log^{1+o(1)}n  towards Conjecture 8.2 a fascinating problem.
739: 
740: 
741: 
742: 
743: 9 Cycles in Ramsey theory.
744: 
745: 
746: 
747: 
753: 
754: 
755: 
756: As it nears the end of its first century, the study of Ramsey numbers of graphs has broadened into a rich and extensive area. Away from the central goal of improving bounds on Ramsey numbers for complete graphs  R(K_{s},K_{t}) , when one of the graphs  G  or  H  is sparse then we may aim to give better bounds on  R(G,H) . For example, a classic result of Chvátal, Rödl, Szemerédi and Trotter [23] states that if an  n -vertex graph  G  has bounded maximum degree, then  R(G,G)=O(n) , while much later Lee [77] confirmed the Burr-Erdős conjecture by showing this holds more widely for graphs  G  with bounded degeneracy.
757: 
758: 
759: 
760: 
761: Very few Ramsey numbers are known exactly. The value of  R(G,G)  has long been known when  G  is a path due to Gerencsér and Gyárfás [48],
762: when  G  is a star (i.e., a graph with a single central vertex which is contained in every edge) due to
763: Harary [52], and when  G  is a cycle, due to work by Bondy and Erdős [11], Faudree and Schelp [44], and Rosta [107]. Much more recently,  R(G,G)  has been determined when  G  contains no cycles (i.e., is a tree) and has no very large vertex degrees, by
764: Montgomery, Pavez-Signé and Yan [95].
765: 
786: 
787: 
788: 
789: Given these results, attention has turned to qualitative concerns. In 1978, Erdős, Faudree, Rousseau and Schelp [39] made the following conjecture for the Ramsey numbers of cycles versus complete graphs.
790: 
791: 
792: 
793: Conjecture 9.1.
794: 
795: 
796: 
797: If  n\geq m\geq 3 , then  R(C_{n},K_{m})=(n-1)(m-1)+1 .
798: 
799: 
800: 
801: 
802: 
803: Nikiforov [98] showed that this conjecture holds if  n\geq 4m+2 . Perhaps surprisingly, though Conjecture 9.1 remains open, it turns out to be true much more broadly when  m  is large. Indeed,
804: Keevash, Long and Skokan [63] showed that  R(C_{n},K_{m})=(n-1)(m-1)+1  holds if  n=\Omega\left(\frac{\log m}{\log\log m}\right) .
805: For the Ramsey numbers of cycles  G  versus graphs  H  more generally, the following conjecture of Pokrovskiy and Sudakov [103] (often, but not always, stronger than a related conjecture of Allen, Brightwell and Skokan [1]) is appealing.
806: 
807: 
808: 
809: Conjecture 9.2.
810: 
811: 
812: 
813: There exists  C>0  such that if  G  is an  n -vertex cycle and  n\geq C|H|  then  R(C_{n},H)=(\chi(H)-1)(n-1)+\sigma(H) .
814: 
815: 
816: 
817: 
818: 
819: A corresponding version of Conjecture 9.2 when  G  is a path was shown by Pokrovskiy and Sudakov [102] and when  G  is a bounded-degree tree by Montgomery, Pavez-Signé and Yan [94]. The best result towards Conjecture 9.2 is one by Haslegrave, Hyde, Kim and Liu [53], who showed that it holds when  n\geq C|H|\log^{4}\chi(H) .
820: The proof in [53] uses sublinear expansion techniques to find a cycle of length  n  when the graph of red edges satisfies certain expansion properties, using some ideas from the work of Liu and Montgomery [81] discussed above.
821: Technical barriers from these methods seem to make it hard to make substantial improvements, and a proof of Conjecture 9.2 would be very interesting, as would be a proof of the remaining unknown cases of Conjecture 9.1.
822: 
823: 
824: 
825: 
826: 10 Expansion in auxiliary graphs.
827: 
828: 
829: 
830: 
852: 
853: 
854: 
855: It is hard to determine whether or not a Latin square has a full transversal, as can be seen in the Hall-Paige conjecture from the 1950’s concerning only the very specific case when the Latin square is the Cayley table of a group. The conjecture was eventually proved by a combination of work by Wilcox, Bray and Evans which relied on the classification of finite simple groups (see the survey by Wanless [125] for more on this). The natural extremal question for transversals in Latin squares more widely is: how large a partial transversal must there be in any Latin square of order  n ? Towards this, the following combination of conjectures by Ryser [108] and Brualdi (see [14]), related to some further conjectures by Stein [112], has become the main conjecture in the area, known as the Ryser-Brualdi-Stein conjecture.
856: 
857: 
858: 
859: Conjecture 10.1.
860: 
861: 
862: 
863: Every Latin square of order  n  has a partial transversal with  n-1  cells and, if  n  is odd, a full transversal.
864: 
865: 
866: 
867: 
868: 
1088: M. Bucić and R. Montgomery.
1089: 
1090: 
1091: Towards the Erdős-Gallai cycle decomposition conjecture.
1092: 
1093: 
1094: Advances in Mathematics, 437:109434, 2024.
1095: 
1096: 
1097:       
1098: 
1099: [16]
1100: 
1179: G. Chen, P. Erdős, and W. Staton.
1180: 
1181: 
1182: Proof of a conjecture of Bollobás on nested cycles.
1183: 
1184: 
1185: J. Combin. Theory Ser. B, 66:38–43, 1996.
1186: 
1187: 
1188:       
1189: 
1190: [23]
1191: 
1754: P. Keevash, A. Pokrovskiy, B. Sudakov, and L. Yepremyan.
1755: 
1756: 
1757: New bounds for Ryser’s conjecture and related problems.
1758: 
1759: 
1760: Transactions of the American Mathematical Society, Series B,
1761: 9(8):288–321, 2022.
1762: 
1763: 
1764:       
1765: 
1766: [66]
1957: H. Liu and R. Montgomery.
1958: 
1959: 
1960: A proof of Mader’s conjecture on large clique subdivisions in
1961:  C_{4} -free graphs.
1962: 
1963: 
1964: J. London Math. Soc., 95:203–222, 2017.
1965: 
1966: 
1967:       
1968: 
1969: [81]
2116: R. Montgomery.
2117: 
2118: 
2119: A proof of the Ryser-Brualdi-Stein conjecture for large even  n .
2120: 
2121: 
2122: arXiv:2310.19779, 2023.
2123: 
2124: 
2125:       
2126: 
2127: [93]
2128: 

## 376380 Sedlar–Škrekovski's mixed metric dimension conjecture
191:     
192: 
193: We show that for a  2 -connected graph  G  which is not a cycle, the mixed metric dimension of  G  is at most  2c(G) , where  c(G)  is the cyclomatic number of  G .
194: As an immediate application, we prove a conjecture
195: proposed by Sedlar and Škrekovski (2021).
196:     
197: 
198: Keywords: Mixed metric dimension; Cyclomatic number;  2 -connected graph
199:     
200: 
201: 2020 MSC: 05C12; 05C38
202:   
203: ††
276: 
277: 
278: In [12],
279: Sedlar and Škrekovski obtained the exact value of the mixed metric dimension of a unicyclic graph and they proposed the following conjecture:
280: 
281: 
282: 
283: Conjecture 1.1
284: 
285: 
286: 
287: ([12, Conjecture 13])
288: Let  G  be a connected graph which is not a cycle.
289: Then  {\rm dim_{m}}(G)\leq\ell(G)+2c(G) .
290: 
291: 
292: 
293: 
294: 
295: Conjecture 1.1 holds for trees and  3 -connected graphs, see [12].
296: In [11], the authors showed that Conjecture 1.1 holds for all Theta graphs. Recently, Chakraborty, Foucaud, and Hakanen [2] proved that Conjecture 1.1 holds for a connected graph which is not a tree such that  \ell(G)\geq 1 , and a connected graph  G  with  \ell(G)=0  and has a cut-vertex.
297: In [5], the authors gave some graphs satisfying Conjecture 1.1.
298: In this paper, we will prove the following theorem:
299: 
300: 
301: 
302: Theorem 1.2
303: 
304: 
305: 
306: Let  G  be a  2 -connected graph which is not a cycle.
317: 
318: 
319: 
320: As an immediate application of Theorem 1.2, we confirm Conjecture 1.1.
321: 
322: 
323: 
324: 
325: 2 Preliminaries
326: 
327: 
328: 
329: 
855: 
856: 
857: 
858: In this section, we will show Theorem 1.2 and confirm Conjecture 1.1. We begin by citing three known results.
859: 
860: 
861: 
862: Theorem 3.1
863: 
864: 
865: 
866: ([2, Corollary 16])
867: Let  G  be a connected graph which is not a tree such that  \ell(G)\geq 1 . Then  {\rm dim_{m}}(G)\leq\ell(G)+2c(G) .
985: 
986: Note that a  2 -connected graph has no leaves.
987: Now, combining Theorems 3.1, 3.2, 3.3, and 1.2,
988: we conclude that Conjecture 1.1 holds for any connected graph which is not a cycle. Namely, Conjecture 1.1 is valid.
989: 
990: 
991: 
992: 
993: Conflict of interest
994: 
995: 
996: 
997: 

## 376392 Frankl's quadratic-threshold conjecture for critical intersecting hypergraphs
204: 
205: Let  k>t\geq 1  be integers and set  d=k-t . A  k -uniform hypergraph  \mathcal{F}  is called  t -intersecting if any two edges intersect in at least  t  vertices, and is called  t -critical if its minimum  t -transversal has size  k . Frankl proved that, for  k\geq d^{4} ,
206:  |\mathcal{F}|\leq\binom{k+d}{d}, 
207: with equality only for the complete  k -graph on  k+d  vertices, and conjectured that the same conclusion should hold when  k>cd^{2}  for some constant  c . In this paper we confirm this conjecture for  c=30 . The proof relies on Frankl’s fixed-edge decomposition and Füredi’s pseudo-sunflower method.
208:   
209: 
210: 
211: 
212: 
213: AMS Classification: 05C65; 05D05
214: 
215: 
216: 
321: 
322: 
323: 
324: Furthermore, Frankl [4] stated that the threshold in Theorem 1.1 can be improved to  k>2d^{3.5}  with some efforts, and he proposed the following conjecture.
325: 
326: 
327: 
328: Conjecture 1.3 (Frankl [4]).
329: 
330: 
331: 
332: There exists a constant  c  such that for  k>cd^{2} ,
333: 
334: 
335: 
336: 
337:  m(k,k-d)=\binom{k+d}{d}. 
343: 
344: 
345: In this paper, we confirm
346: Conjecture 1.3 for  c=30 , and we also characterize the extremal graphs.
347: 
348: 
349: 
350: Theorem 1.4.
351: 
352: 
353: 
354: For positive integers  d  and  k\geq 30d^{2} ,
355: 
369: 
370: 
371: 
372: While we have confirmed Frankl’s Conjecture 1.3 for  c=30 , the exact threshold is still unknown. We believe it will be of great interest to find it.
373: 
374: 
375: 
376: 
377: 
378: This paper is organized as follows. In Section 2, we introduce our tools, including Füredi’s pseudo-sunflower method and Frankl’s fixed-edge decomposition. In Section 3, we prove our main result.
379: 
380: 
381: 
1512: 
1513: [6]
1514: 
1515: P. Frankl, K. Ota, and N. Tokushige, Covers in uniform intersecting families and a counterexample to a conjecture of Lovász, J. Combin. Theory Ser. A 74 (1996), 33–42.
1516: 
1517: 
1518:       
1519: 
1520: [7]
1521: 
1522: Z. Füredi,
1523: On maximal intersecting families of finite sets,
1524: J. Combin. Theory Ser. A 28 (1980), 282–289.

## 376405 Conjecture on invariant sums of squared side areas for cyclic polygons

## 376406 Bridgeland stability conjecture for the Kuznetsov component of a singular cubic sevenfold
SOURCE UNREAD

## 376562 The open O(1) loop-model largest-component conjecture
204: loop model at  n=1 .
205: Based on exact results for finite-size systems, sums involving
206: the wavefunction components, and in some cases the largest component
207: itself, are conjectured to be directly related to
208: the total number of alternating sign matrices
209: and plane partitions in certain symmetry classes.
210:   
211: 
212: 
213: 
214: 
215: Very recently Razumov and Stroganov [1] have made some remarkable conjectures
216: in which the number of  n\times n  alternating sign matrices appear in certain
217: properties of the ground state
218: wavefunction of the antiferromagnetic XXZ Heisenberg chain
219: at  \Delta=-\frac{1}{2}  defined on an odd number of sites  L .
220: At this point, the ground state energy of the XXZ hamiltonian
221: 
222: 
223: 
224: 
256: Normalise the groundstate wavefunction such that the smallest
257: nonzero entry is unity.
258: Then based on explorations on finite systems of size  L=2n+1 ,
259: Razumov and Stroganov have made the following conjectures (among others)
260: 
261: 
262: 
263: 
264: Conjecture (Razumov and Stroganov [1])
265: The largest element of the groundstate
266: wavefunction is given by  A_{n} , where
267: 
268: 
269: 
270: 
271:  A_{n}=\prod_{j=0}^{n-1}\frac{(3j+1)!}{(n+j)!}. 
272: 
273: (4)
276: 
277: 
278: 
279: Conjecture (Razumov and Stroganov [1])
280: The 1- and 2-sums for the groundstate wavefunction are given by
281: 
282: 
283: 
284: 
285:  \displaystyle S_{2n+1}^{(1)} 
286:  \displaystyle= 
287:  \displaystyle(\sqrt{3})^{n}{\cal N}_{n} 
288: 
341: of interchanging left and right and complex conjugation.
342: Again, based only on exploration of  \psi_{0}  for finite sizes,
343: there are patterns to be observed.
344: Our conjectures are
345: 
346: 
347: 
348: Conjecture 1
349: 
350: 
351: 
352: The 1-sum of the groundstate wavefunction of the twisted XXZ chain at
353:  \Delta=-\frac{1}{2}  is given by
354: 
355: 
356: 
357: 
362: 
363: 
364: 
365: Conjecture 2
366: 
367: 
368: 
369: The 2-sum of the groundstate wavefunction of the twisted XXZ chain at
370:  \Delta=-\frac{1}{2}  is given by
371: 
372: 
373: 
374: 
403: choose the normalisation such that the smallest elements have amplitude
404: 1 and the wavefunction is invariant under the combined transformation
405: of interchanging left and right and complex conjugation.
406: For this case we are led to the following conjectures.11
407:           1
408:           
409:           
410:         In this case
411: we found Sloane’s On-Line Encyclopaedia of Integer Sequences to be most helpful,
412: see http://www.research.att.com/ \sim njas/sequences/.
413: 
414: 
415: 
416: Conjecture 3
417: 
418: 
419: 
420: The 1-sum of the groundstate wavefunction of the quantum invariant XXZ chain at
421:  \Delta=-\frac{1}{2}  is given by
422: 
423: 
424: 
425: 
460: 
461: 
462: 
463: Conjecture 4
464: 
465: 
466: 
467: The 2-sum of the groundstate wavefunction of the quantum invariant XXZ chain at
468:  \Delta=-\frac{1}{2}  is given by
469: 
470: 
471: 
472: 
493: we now see that there is some remarkable structure in the first two  p -sums
494: for the groundstate wavefunction of the antiferromagnetic XXZ chain at
495:  \Delta=-\frac{1}{2} .
496: Presumably the conjectured results can be proved in each case via the
497: Bethe Ansatz form of the wavefunctions, which are known.
498: We hope that our findings will spark further interest in their properties.
499: 
500: 
501: 
502: 
503: Even more remarkable is that the observed structure is related to alternating
504: sign matrices, or rather plane partitions.
505: For the two cases considered here the trivial groundstate energy can be viewed
519:         Note that for the loop models, the  p -sums defined
520: in (3) are over sums smaller than their binomial counterparts in the
521: XXZ chain.
522: Four further conjectures suggest themselves.
523: 
524: 
525: 
526: 
527: 
528:  L 
529:  n 
530:  \psi_{0} 
531: multiplicity
648: 
649: 
650: 
651: Conjecture 5
652: 
653: 
654: 
655: For open boundary conditions, the largest element of the O(1) loop model
656: wavefunction is given by  N_{8}(2n)  for  L=2n  and  A_{\rm v}(2n-1)  for  L=2n-1 .
657: 
658: 
659: 
660: 
661: Conjecture 6
662: 
663: 
664: 
665: The 1-sum of the groundstate wavefunction of the O(1) loop model with
666: open boundary conditions is given by
667: 
668: 
669: 
670: 
683: 
684: 
685: 
686: Conjecture 7
687: 
688: 
689: 
690: For periodic boundary conditions and  L=2n , the largest element of the O(1) loop model
691: wavefunction is given by  A_{n-1} .
692: 
693: 
694: 
695: 
696: Conjecture 8
697: 
698: 
699: 
700: The 1-sum of the groundstate wavefunction of the O(1) loop model with
701: periodic boundary conditions and  L=2n  is given by
702:  S_{2n}^{(1)}=A_{n} .
703: 
704: 
705: 
756: The numbers appearing in the first few groundstate wavefunctions
757: are given in Table 4.
758: Again we have normalised the wavefunctions such that the smallest element is unity.
759: Two further conjectures are
760: 
761: 
762: 
763: Conjecture 9
764: 
765: 
766: 
767: For periodic boundary conditions and  L=2n-1 , the largest element of the
768: O(1) loop model wavefunction is given by  A_{n-1}^{2} .
769: 
770: 
771: 
772: 
773: Conjecture 10
774: 
775: 
776: 
777: The 1-sum of the groundstate wavefunction of the O(1) loop model with
778: periodic boundary conditions and  L=2n-1  is given by
779:  S_{2n-1}^{(1)}={\cal N}_{n}^{2} .
780: 
781: 
782: 
783: 
784: 
785: These are to be compared with those of Razumov and Stroganov [1] given above.
786: An interesting comparison can be made between Conjectures 7 & 9 for
787: periodic boundary conditions with even and odd system sizes.
788: On the one hand, for  L  even, the largest element in the wavefunction is given by
789:  A_{n-1} , which we recall is also equivalent to the total number of descending
790: plane partitions with largest part less than or equal to  n-1 .
791: This quantity is also the number of totally symmetric
792: self-complementary plane partitions in  {\cal B}(2n-2,2n-2,2n-2) ,
793: a cubic box of linear size  2n-2 .
794: On the other hand, for  L  odd, the largest element is given by  A_{n-1}^{2} .
795: However,  A_{n-1}^{2}  is the number
796: of cyclically symmetric self-complementary
797: plane partitions in  {\cal B}(2n-2,2n-2,2n-2)  [5].
798: Further, Conjecture 5 states that for  L  even and open boundaries,
799: the largest element in the wavefunction is given by the
800: number of cyclically symmetric transpose complement plane partions
801: in  {\cal B}(2n,2n,2n) .
802: Such results may be a hint that the underlying relations are more directly
803: with plane partitions rather than alternating sign matrices.
804: 
805: 
806: 
807: 
867: 
868: [5]
869:  D.M. Bressoud, Proofs and Confirmations – The story of
870: the alternating sign matrix conjecture,
871: Cambridge University Press, 1999.
872: 
873: 
874:       
875: 
876: [6]
877: 
878: F.C. Alcaraz, M.N. Barber and M.T. Batchelor, R.J. Baxter and
879: G.R.W. Quispel, Surface exponents of the  XXZ , Ashkin-Teller and Potts

## 376563 The open O(1) loop-model 1-sum conjecture
204: loop model at  n=1 .
205: Based on exact results for finite-size systems, sums involving
206: the wavefunction components, and in some cases the largest component
207: itself, are conjectured to be directly related to
208: the total number of alternating sign matrices
209: and plane partitions in certain symmetry classes.
210:   
211: 
212: 
213: 
214: 
215: Very recently Razumov and Stroganov [1] have made some remarkable conjectures
216: in which the number of  n\times n  alternating sign matrices appear in certain
217: properties of the ground state
218: wavefunction of the antiferromagnetic XXZ Heisenberg chain
219: at  \Delta=-\frac{1}{2}  defined on an odd number of sites  L .
220: At this point, the ground state energy of the XXZ hamiltonian
221: 
222: 
223: 
224: 
256: Normalise the groundstate wavefunction such that the smallest
257: nonzero entry is unity.
258: Then based on explorations on finite systems of size  L=2n+1 ,
259: Razumov and Stroganov have made the following conjectures (among others)
260: 
261: 
262: 
263: 
264: Conjecture (Razumov and Stroganov [1])
265: The largest element of the groundstate
266: wavefunction is given by  A_{n} , where
267: 
268: 
269: 
270: 
271:  A_{n}=\prod_{j=0}^{n-1}\frac{(3j+1)!}{(n+j)!}. 
272: 
273: (4)
276: 
277: 
278: 
279: Conjecture (Razumov and Stroganov [1])
280: The 1- and 2-sums for the groundstate wavefunction are given by
281: 
282: 
283: 
284: 
285:  \displaystyle S_{2n+1}^{(1)} 
286:  \displaystyle= 
287:  \displaystyle(\sqrt{3})^{n}{\cal N}_{n} 
288: 
341: of interchanging left and right and complex conjugation.
342: Again, based only on exploration of  \psi_{0}  for finite sizes,
343: there are patterns to be observed.
344: Our conjectures are
345: 
346: 
347: 
348: Conjecture 1
349: 
350: 
351: 
352: The 1-sum of the groundstate wavefunction of the twisted XXZ chain at
353:  \Delta=-\frac{1}{2}  is given by
354: 
355: 
356: 
357: 
362: 
363: 
364: 
365: Conjecture 2
366: 
367: 
368: 
369: The 2-sum of the groundstate wavefunction of the twisted XXZ chain at
370:  \Delta=-\frac{1}{2}  is given by
371: 
372: 
373: 
374: 
403: choose the normalisation such that the smallest elements have amplitude
404: 1 and the wavefunction is invariant under the combined transformation
405: of interchanging left and right and complex conjugation.
406: For this case we are led to the following conjectures.11
407:           1
408:           
409:           
410:         In this case
411: we found Sloane’s On-Line Encyclopaedia of Integer Sequences to be most helpful,
412: see http://www.research.att.com/ \sim njas/sequences/.
413: 
414: 
415: 
416: Conjecture 3
417: 
418: 
419: 
420: The 1-sum of the groundstate wavefunction of the quantum invariant XXZ chain at
421:  \Delta=-\frac{1}{2}  is given by
422: 
423: 
424: 
425: 
460: 
461: 
462: 
463: Conjecture 4
464: 
465: 
466: 
467: The 2-sum of the groundstate wavefunction of the quantum invariant XXZ chain at
468:  \Delta=-\frac{1}{2}  is given by
469: 
470: 
471: 
472: 
493: we now see that there is some remarkable structure in the first two  p -sums
494: for the groundstate wavefunction of the antiferromagnetic XXZ chain at
495:  \Delta=-\frac{1}{2} .
496: Presumably the conjectured results can be proved in each case via the
497: Bethe Ansatz form of the wavefunctions, which are known.
498: We hope that our findings will spark further interest in their properties.
499: 
500: 
501: 
502: 
503: Even more remarkable is that the observed structure is related to alternating
504: sign matrices, or rather plane partitions.
505: For the two cases considered here the trivial groundstate energy can be viewed
519:         Note that for the loop models, the  p -sums defined
520: in (3) are over sums smaller than their binomial counterparts in the
521: XXZ chain.
522: Four further conjectures suggest themselves.
523: 
524: 
525: 
526: 
527: 
528:  L 
529:  n 
530:  \psi_{0} 
531: multiplicity
648: 
649: 
650: 
651: Conjecture 5
652: 
653: 
654: 
655: For open boundary conditions, the largest element of the O(1) loop model
656: wavefunction is given by  N_{8}(2n)  for  L=2n  and  A_{\rm v}(2n-1)  for  L=2n-1 .
657: 
658: 
659: 
660: 
661: Conjecture 6
662: 
663: 
664: 
665: The 1-sum of the groundstate wavefunction of the O(1) loop model with
666: open boundary conditions is given by
667: 
668: 
669: 
670: 
683: 
684: 
685: 
686: Conjecture 7
687: 
688: 
689: 
690: For periodic boundary conditions and  L=2n , the largest element of the O(1) loop model
691: wavefunction is given by  A_{n-1} .
692: 
693: 
694: 
695: 
696: Conjecture 8
697: 
698: 
699: 
700: The 1-sum of the groundstate wavefunction of the O(1) loop model with
701: periodic boundary conditions and  L=2n  is given by
702:  S_{2n}^{(1)}=A_{n} .
703: 
704: 
705: 
756: The numbers appearing in the first few groundstate wavefunctions
757: are given in Table 4.
758: Again we have normalised the wavefunctions such that the smallest element is unity.
759: Two further conjectures are
760: 
761: 
762: 
763: Conjecture 9
764: 
765: 
766: 
767: For periodic boundary conditions and  L=2n-1 , the largest element of the
768: O(1) loop model wavefunction is given by  A_{n-1}^{2} .
769: 
770: 
771: 
772: 
773: Conjecture 10
774: 
775: 
776: 
777: The 1-sum of the groundstate wavefunction of the O(1) loop model with
778: periodic boundary conditions and  L=2n-1  is given by
779:  S_{2n-1}^{(1)}={\cal N}_{n}^{2} .
780: 
781: 
782: 
783: 
784: 
785: These are to be compared with those of Razumov and Stroganov [1] given above.
786: An interesting comparison can be made between Conjectures 7 & 9 for
787: periodic boundary conditions with even and odd system sizes.
788: On the one hand, for  L  even, the largest element in the wavefunction is given by
789:  A_{n-1} , which we recall is also equivalent to the total number of descending
790: plane partitions with largest part less than or equal to  n-1 .
791: This quantity is also the number of totally symmetric
792: self-complementary plane partitions in  {\cal B}(2n-2,2n-2,2n-2) ,
793: a cubic box of linear size  2n-2 .
794: On the other hand, for  L  odd, the largest element is given by  A_{n-1}^{2} .
795: However,  A_{n-1}^{2}  is the number
796: of cyclically symmetric self-complementary
797: plane partitions in  {\cal B}(2n-2,2n-2,2n-2)  [5].
798: Further, Conjecture 5 states that for  L  even and open boundaries,
799: the largest element in the wavefunction is given by the
800: number of cyclically symmetric transpose complement plane partions
801: in  {\cal B}(2n,2n,2n) .
802: Such results may be a hint that the underlying relations are more directly
803: with plane partitions rather than alternating sign matrices.
804: 
805: 
806: 
807: 
867: 
868: [5]
869:  D.M. Bressoud, Proofs and Confirmations – The story of
870: the alternating sign matrix conjecture,
871: Cambridge University Press, 1999.
872: 
873: 
874:       
875: 
876: [6]
877: 
878: F.C. Alcaraz, M.N. Barber and M.T. Batchelor, R.J. Baxter and
879: G.R.W. Quispel, Surface exponents of the  XXZ , Ashkin-Teller and Potts
