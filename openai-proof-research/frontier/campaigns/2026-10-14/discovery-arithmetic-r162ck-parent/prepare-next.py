#!/usr/bin/env python3
"""Prepare a distinct, fully scoped Source173 discovery task."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cl-parent';R=B/'fresh-arithmetic-discovery-r162cl'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cl-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==848 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ck-brief.txt').read_bytes()
assert sha(oldbytes)=='2fbcb2ffa93c027ba6b41420029535b33a8f38936fec6bd44f7e7720ba8d1610'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source172')]
prefix=prefix.replace('Arithmetic discovery r162ck — confirmed finite Euclidean Ramsey classification discovery.','Arithmetic discovery r162cl — confirmed second-neighborhood operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162ck/','fresh-arithmetic-discovery-r162cl/',1).replace('FRESH DISTINCT Source172','FRESH DISTINCT Source173',1).replace('Own r162ck I/O','Own r162cl I/O',1)
instructions="""Read COMPLETE Source173,actual wrapper,ALL includes,figure and bibliography,then strongest relevant primary/companion proofs BEFORE selecting one additional full theorem. The entire finite-oriented-graph second-neighborhood theorem and all stronger reduction,pruning,incompatibility,weighted and directed-cycle operations are PAID at their actual hypotheses. Source truth is stipulated;no audit.

Keep one original graph,weights and exact-distance convention. Classical/source blowups,averaging and duality are paid when compatible. Sustain mathematics;freeze exact full quantifiers only after viable nonroutine feasibility. Parent commissions independent correctness and actual-primary contribution reviews. No self-gates/count,restricted substitute,renamed old target or desired-grade retry. Every older scope remains immutable.

R162CK is CLOSED PREFREEZE/no nominee. The exact original-scale quadratic Ramsey construction of arbitrary finite cardinality is a source/algebraic composition. Its transcendental cross-ratio calculation defeats only specified conjectural necessities in the read public companion snapshot,not the proved five-anchor theorem. Degree-two-map and finite-constant-field comparisons are paid. General secondjet sufficiency/common all-order lifting remains unproved;no actual secondjet-pass/full-tensor-fail example. Quadratic family closes exactly;the cubic test fails already at second order. Complete parent intake records actual primary/companion read extents,late reads,ancestry limits,history0,and unchanged seals. Parent Source173 operative-proof reading:NONE.
R162CJ remains CLOSED PREFREEZE/no nominee. Fixed-positive-surplus prescribed-color cube comparison and conditional-reference compatibility are paid;uniform zero-surplus extension remains unproved. Balanced example defeats a shortcut but has a paid color-flip embedding.
R162CI remains CLOSED PREFREEZE/no nominee. Original iid incident-flag constant-factor endpoint remains unproved;aggregate overlap closes one component only. Repeated-plane,context and retention costs remain uncontrolled.
R162CH remains CLOSED PREFREEZE/no nominee. Same-graph/partition/q elementary unimodality remains unproved;odd-edge quotient and stronger primaries paid;finite examples defeat shortcuts only.
R162CG remains CLOSED PREFREEZE/no nominee. Same-ideal weighted aggregate cancellation remains unproved;the S6 example satisfies that identity and defeats stronger shortcuts.
R162CF remains CLOSED PREFREEZE/no nominee. Product-law transfer and fixed-c tail integration paid;energy-weighted sparse bands and variable-radius algebra uncontrolled.
R162CE remains CLOSED PREFREEZE/no nominee. Local-palette comparisons paid;unrestricted3D pinned endpoint's coupled estimate/profile transfer unproved. No counterexample follows.
R162CD remains CLOSED PREFREEZE/no nominee. One-part-even parity and repair paid;generic tournament/labelled parity bounds unproved. Finite singularity is not generic failure.
R162CC remains CLOSED PREFREEZE/no nominee. Monomial-ratio word planning paid;common integer mixed-expression counting/alignment unproved. Valuation example defeats one template.

R162CB remains CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Its immutable theorem:every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1,admits one finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,cover r,and pairwise intersections1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. No refreeze,repair,renaming or review retry.
R162CA remains CLOSED PREFREEZE/no nominee;all completed same-pattern constructions paid. No exact finite-host equality or additional nonroutine construction closed. All earlier dispositions remain unchanged.

"""
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source173-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[273998,274820] and len(sel['folders'])==1 and len(sel['entries'])==15
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')]
textbytes=sum(e['size'] for e in texts);assert len(blobs)==11 and len(texts)==10
prior=B/'fresh-arithmetic-discovery-r162ck'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[273998,274820),EXACT Source173. Parent used ONE bounded14000-byte window[273998,287998),decoded only173/174numeric-bold titles and ONLY173body;174body/remainder not decoded;third heading only a byte boundary. ONE new family-body screen. No extra title locator,family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
"""
folder=sel['folders'][0];wrapper=next(e for e in blobs if e['path']==folder+'/build/source/main.tex')
section+=folder+'\n'+wrapper['path']+';bytes'+str(wrapper['size'])+';Git blob'+wrapper['sha']+'.\n'
section+='Exactly11blobs15entriesincludingroots,10non-PDFtexts'+str(textbytes)+"""bytes,one compiledPDF. Read actual build/source/main.tex,all6includes(00-introduction,01-reduction,02-pruning,03-incompatibility,04-weighted-consequences,05-directed-cycle-consequences),pruningfigure,references.bib,andREADME. Authenticate every object and follow actual includes;the wrapper alone is not the operative proof. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored oriented-graph,second-neighborhood,weighted-neighborhood,pruning and directed-cycle mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162ce* *arithmetic*r162cl*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162cl*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=173,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=11,canonical_entries=15,canonical_text_objects=10,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body174_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=1,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
