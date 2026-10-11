# I188: exact patch geometry in the rooted state sum

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and `sources/upstream.json`; all OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Neither bookkeeping nor a newly nonempty
restricted source image automatically supplies a substantial finding.

## Focused context and unchanged target

Read all five I187 outputs and the
[finalized parent disposition](i187-frozen-state-survival-parent-disposition.md).
Read the I187 brief and the actual source operations used. The original
E183 hypotheses are exactly I187 analytic Section 1, unchanged:
arbitrary finite connected simple bipartite locally cubic disk $X$,
five degree-two ports in order $(0,2,1,4,3)$ with colors
$(1,1,1,0,1)$; exact thirteen-vertex exterior and attachments there;
simple planar bipartite brace $G$; all eleven complete nonempty survivor
fibres and complete lost $P,D$; internal port-disjoint
$C=(x,a,b,y,d,c,x)$ with chord $xy$,
$A=\{xa,by,dc\}$ and $B=\{ab,yd,cx\}$;
$p\in P$ using exactly $A$ and $q=p\triangle E(C)\in P$.

For every such instance E183 asks for **some perfect matching containing
$A$ whose complement is Hamiltonian of any survivor local type**.
Restate the exact exterior, complete fibres and quantifiers in your
argument, not just this shorthand. No cut-2, fixed-completion,
single-difference-cycle, or local-move prescription. The local-ear
mechanism remains PARKED; do not revive it as a plateau or transfer task.

I187's original technical claims pass parent review without repairs.
Its small-cut proof pays 3-vertex-connectivity and the absence of
separating dual triangles. The source's fixed-second-state cancellation
survives marking. But an arbitrary endpoint mark can fix up to two
cycle orientations, and the generic formula does not align their phases.
The complete frozen/survivor mark also depends on white-tree recovery.
There is no exact-instance phase counterexample, no general surjectivity
claim and no proof of survivor nonvanishing.

## One concrete geometric specialization to investigate

The generic I187 calculation did not use the detailed position of the
two marked black faces around the patch. Determine whether this geometry
actually pays part of the missing phase and recovery information.
The following is a proposed route to check, not a collection of premises.

1. **Prove or reject faciality first.** Are the two four-cycles
   $(x,a,b,y,x)$ and $(x,y,d,c,x)$ actual facial boundaries in the
   specified embedding? A separating four-cycle in a cubic plane graph
   has only four off-cycle incidences. If both sides contain vertices,
   consider the edge boundaries of those interior vertex sets, using
   I187's absence of cuts of size one or two. Deal explicitly with
   chords and with the opposite sides of $xy$. No drawing is a proof.

2. **Pay all dual vertex identifications.** If faciality holds, name the
   dual vertices of those square faces $\ell,r$. Let $o$ be the third
   root of $t_x$, the primal-vertex dual triangle. With
   $t_0=t_x$ and $f_0=(xa)^*$, the roots would be
   $\{o,\ell,r\}$. Let $v$ be the third vertex of $t_y$, and let
   $u,w$ be the remaining vertices of $t_b,t_d$, so the prospective
   black triangles are $(\ell,v,u)$ and $(r,w,v)$.
   Prove every identification, distinctness and nonroot assertion used.
   Dual simplicity and the nonseparating-triangle property may constrain
   accidental identifications. Do not assume arbitrary face names are
   distinct, and retain legitimate parallel incidences if they arise.

3. **Determine the actual marked source cycle.** Every undirected source
   group uses only nonroots and one side of each nonouter black face.
   Does the local structure force the sides $uv$ and $vw$, hence put
   both marked faces on the same source cycle? The I187 endpoint mark is

   $$
   \eta(s)=
   \mathbf1_{\{s(t_b)\in V((by)^*)\}}
   \mathbf1_{\{s(t_d)\in V((dc)^*)\}}.
   $$

   Under the prospective labels this would require $s(t_b)=v$,
   $s(t_d)=w$, giving direction $u\to v\to w$ on that cycle.
   Determine whether that orientation has the same clockwise or
   counterclockwise sign in every group, using the actual outer-root
   sector and planar separation. Do not infer its sign from abstract
   endpoint labels. If identifications change this picture, handle them
   explicitly rather than silently discarding instances.

4. **Use the exact restricted product, not an assumption of positivity.**
   If every group has precisely one consistently fixed cycle and all
   others free, substitute that fact into I187 formulas (13)--(14).
   Prove or reject alignment at the minimum number of free cycles.
   A nonzero sum still needs a retained group, and the source pair
   existence theorem must apply with the paid hypotheses. A bare
   assertion of nonzero coefficient is not a result.

5. **Separate endpoint marking from recovered matching.** For partnered
   forest states that survive this mark, investigate the actual
   white-face tree. For example, is $t_y$ a forced leaf, with the
   $t_b$ spoke as its unique tree incidence, so that $(by)^*$ is
   selected? Account for every spoke that could meet $t_y$.
   Root-edge $xa$ and matching edge $by$, if both established,
   constrain the other square through Hamiltonian connectedness:
   check whether failure to select $dc$ would close a proper four-cycle.
   These are candidate deductions, not a license to identify endpoint
   marking with the two parent-edge tests without proof.

6. **Return to survival honestly.** A nonempty $A$-containing source
   image would remove the previously unpaid image/nonvanishing step for
   the frozen half, but does not show a survivor. Trace the full local
   path type and determine what the exact exterior and complete fibres
   actually add. Try to carry the new geometric constraint through the
   survivor restriction. If it does not control that restriction, report
   the precise remaining implication and do not declare E183 proved.
   No claim that a lost completion has a preimage follows merely from
   finding some frozen-matching image.

This is one bounded examination of a concrete patch-rooted phase
constraint. It is not another generic Fourier reformulation.
If the local geometry fails or only the frozen population is paid,
state that exact outcome. Do not initiate a sequel yourself.
E183 must receive PROVED, REFUTED by a fully hypothesized written
counterexample, or UNRESOLVED. Z184, exchange, (T) and Q164 require
separate implications; technical progress does not resolve them.

## Sources, evidence and exclusive output scope

Use the retained pinned manuscript at
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
SHA-256 `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
Read actual needed statements/operations and record ranges; check the
focused catalogue/companion paths. No recursive history or upstream
truth audit. No external theorem may be invoked unread.

Only these five paths may be written:

- `frontier/iterations/i188-patch-rooted-state.md`
- `frontier/experiments/i188_patch_rooted_state/analytic-attempt.md`
- `frontier/experiments/i188_patch_rooted_state/reading-and-failures.md`
- `frontier/experiments/i188_patch_rooted_state/input-authentication.json`
- `frontier/sources/i188_patch_rooted_state/literature.md`

No research code, graph/state/matching scans or tests, experiments,
historical replay/control rebuild, source copies, snapshots or seals.
Written symbolic proofs about actual hypothetical admissible instances
are allowed. No further agents, ancestor/shared-ledger edits, staging,
commits or publication. Preserve failed written routes and reading limits.

Before proof work authenticate all five I187 anchors:

| Output | SHA-256 |
| --- | --- |
| Report | `6c37f8f35bbbefd181473335a7d1013532d92be70afa17c9717d4508b5d10734` |
| Analytic attempt | `9ba0316f9db9d344b39b3d5637e4474d790696bcd2cdea7016698a611f98468f` |
| Reading/failures | `a62333f9e1cd118ddd9a751b55906fc1303ff02bc361e75b49d3b48cdd9afa6e` |
| Authentication | `8d398bd1811d0bc5939fe7b5899888213138a3a9cb2b5b66202178db91ddefe5` |
| Literature | `686e3c5e5334c4ec0d267488ee7142c1a2ba7b9618da81c20d334a0c72d80947` |

Also hash this brief, finalized I187 disposition and actual additional
inputs. The parent independently checked the proofs and formal formulas;
the inherited 23-stage replay passed in about 8.72 seconds with eight
probes and source positive control. It and the twelve facial/626 matching
controls remain finite and must not be rerun here.
Return detached hashes, full written deductions or gaps, original-target
verdict and source/contribution limits. This is an unsealed proof record.
