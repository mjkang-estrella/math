#!/usr/bin/env python3
"""Prepare the distinct Source165 round with inherited isolation and scope intact."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162cd-parent'; R=B/'fresh-arithmetic-discovery-r162cd'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cd-brief.txt'
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s): return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}

head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]; checks=[]; legacy=[]
for i,x in enumerate(t['tasks']):
 if i==840 or x.get('status') not in {'running','queued','waiting'}: continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x
  legacy.append(i); continue
 a=(P/x['brief']).read_bytes()
 assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values()); checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]: assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cc-brief.txt').read_bytes()
assert sha(oldbytes)=='4b515eeeadc8550f4a1a9a8b0c57ea8348ac1a10a0faf205c5e8e72c5043a079'
old=oldbytes.decode(); marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1]; assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source164')]
prefix=prefix.replace('Arithmetic discovery r162cc — confirmed finite sums and products operative-proof discovery.','Arithmetic discovery r162cd — confirmed graph crossing-number operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162cc/','fresh-arithmetic-discovery-r162cd/',1).replace('FRESH DISTINCT Source164','FRESH DISTINCT Source165',1).replace('Own r162cc I/O','Own r162cd I/O',1)
instructions="""Read BOTH COMPLETE actual Source165 operative proofs,actual wrappers,ALL mathematical includes,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. Entire Harary-Hill and Zarankiewicz crossing-number formulas for every complete and complete bipartite graph are ALREADY PAID,including optimality among drawings with continuous edge arcs. Credit every stronger actual normalization,local-pairing,interpolation,detector,subspace,intersection and topological operation,not just these headlines. Do not audit stipulated source truth.

Keep ONE actual graph,drawing,edge system,intersection convention and parameter choice throughout. Ordinary,rectilinear,pair,odd,multiple-edge,surface and constrained drawing invariants are different interfaces. Classical deletion averaging,blowups,planarization and crossing consequences are paid at compatible hypotheses. Read primary proofs before declaring compatibility unpaid. Sustain derivation and freeze exact full quantifiers only with a viable additional nonroutine proof. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. Every older scope remains immutable.

R162CC is CLOSED PREFREEZE/no nominee. Broader finite monomial-ratio word planning closes through triangular support and backward protection;noncommutativity is not an unpaid gap. A common integer mixed-expression counting/alignment law remains unproved. The two-row valuation contradiction refutes one template only;restricted positive scales exist. Parent read DERIVATION26208bytes,SOURCE-INTERFACES10445bytes,WORKING4514bytes,READING-LIMITS14824bytes,handoffs/verifier. Author read11canonicaltexts261554bytes,6fullprimarypapers105pages plus11ZKpages,3visuals;8PDFs acquired include a wrong identifier with only12lines read. Versions/access/recoveries/later-mode/ancestry limits and history0 disclosed. Artifact MATCH56payloads58files10dirs,12blobs3trees,5completedpairs;allauthorbytes/modesunchanged. Parent Source165 operative-proof reading:NONE.

R162CB remains CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Its immutable theorem:every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1,admits one finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,cover r,and pairwise intersections1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. No refreeze,repair,renaming or review retry.

"""
instructions+=old[old.index('R162CA is CLOSED'):old.index('R162BJ remains archived')]
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source165-selection.json').read_bytes())
nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[265378,266874] and len(sel['folders'])==2 and len(sel['entries'])==26
blobs=[e for e in sel['entries'] if e['type']=='blob']
textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))
assert len(blobs)==19 and textbytes==111715
prior=B/'fresh-arithmetic-discovery-r162cc'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md']; inputs=[]
for p in direct:
 a=p.read_bytes(); inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[265378,266874),EXACT Source165 and BOTH linked manuscripts. Parent used ONE bounded14000-byte window[265378,279378),decoded only165/166numeric-bold titles and ONLY165body;166body/remainder not decoded;third heading only a byte boundary. ONE new family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
"""
for folder in sel['folders']:
 filename='main.tex' if folder.endswith('/The-crossing-number-of-complete-graphs-September-23-2026') else 'paper.tex'
 w=next(e for e in blobs if e['path']==folder+'/build/'+filename)
 section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+="""Combined19blobs26entriesincludingroots,17non-PDFtexts111715bytes,two compiledPDFs. Read complete-graph main.tex in full,all three figures,README,bibliography;read bipartite paper.tex,all six sections(conclusion,detector,intersections,introduction,normalization,subspaces),both figures,README,bibliography. Do not substitute summaries for operative proof. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored crossing-number,drawing-intersection,local-pairing and topological-detector mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162cd* *arithmetic*r162cd*\n'
missing=rules(old)-rules(text)
if missing: text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162cd*' in brief.decode()
N.mkdir(mode=0o700); R.mkdir(mode=0o700); (N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x); (N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=165,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=19,canonical_entries=26,canonical_text_objects=17,canonical_text_bytes=textbytes,compiled_pdfs=2,new_family_screens=1,body166_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep); print(json.dumps(prep))
