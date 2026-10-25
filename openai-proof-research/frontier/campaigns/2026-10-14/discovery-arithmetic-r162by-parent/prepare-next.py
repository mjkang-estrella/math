#!/usr/bin/env python3
"""Prepare the distinct Source159 round with inherited isolation and scope intact."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162bz-parent'; R=B/'fresh-arithmetic-discovery-r162bz'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bz-brief.txt'
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s): return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}

head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]; checks=[]; legacy=[]
for i,x in enumerate(t['tasks']):
 if i==834 or x.get('status') not in {'running','queued','waiting'}: continue
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
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162by-brief.txt').read_bytes()
assert sha(oldbytes)=='b24292752104bdd934f201a83d95ae4720632773b6338d8bcca75038ec3c3335'
old=oldbytes.decode(); marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1]; assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source158')]
prefix=prefix.replace('Arithmetic discovery r162by — confirmed planar unit-distance coloring operative-proof discovery.','Arithmetic discovery r162bz — confirmed arithmetic-progression operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162by/','fresh-arithmetic-discovery-r162bz/',1).replace('FRESH DISTINCT Source158','FRESH DISTINCT Source159',1).replace('Own r162by I/O','Own r162bz I/O',1)
instructions="""Read the COMPLETE actual Source159 operative proof,actual wrapper,preamble,ALL mathematical sections and foundations,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source results are ALREADY PAID:Erdos's reciprocal-sum assertion and quasipolynomial upper bounds r_k(N)<=C_k N exp(-c_k(log N)^epsilon_k) for every fixed k>=3. Constants depend on k. Credit ALL stronger actual relative,constrained,sampling,cube,shift,transfer,lifting,path,major-arc,return,ascent,active,extraction,iteration and consequence operations,not just the headline. Do not audit stipulated source truth.

Keep ONE actual set,ambient interval/group,arithmetic configuration,majorant and common scale sequence throughout each composition. Density bounds,weighted reciprocal divergence,quantitative supersaturation,constructive extraction,uniformity in k and relative/sparse transfers have distinct quantifiers and costs. Classical dyadic decomposition,Varnavides averaging,compactness,transference and density-increment consequences are paid when their full hypotheses match. Do not repackage an existing source corollary as a contribution. Read operative primary proofs before declaring compatibility unpaid. Sustain mathematical derivation;freeze exact hypotheses,quantifiers and conclusions only with a viable genuinely additional nonroutine proof. Parent commissions separate full correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. All older scopes remain immutable.

R162BY is CLOSED PREFREEZE/no nominee. One hypothetical weak six-coloring yields palette cap3,common edge-avoiding traces,partial forbidden-interval regularization,periodic collar accounting and the qualitative hole-density equivalence,all paid comparisons. Joint treatment of genuine triple palettes or a uniform same-coloring hole-density obstruction as interval width shrinks remains unproved/unfrozen. The angular,half-plane,two-segment and Hausdorff examples refute only specified inferences,not plane six-colorability or every method. Full primary map/index and positive-interval arguments are credited at actual hypotheses. Parent read full DERIVATION32789bytes,SOURCE-INTERFACES9495bytes,WORKING,READING-LIMITS8581bytes,handoffs and verifier;initial aggregate truncation recovered in two complete contiguous windows. Author read15texts225514bytes,5completeprimarypapers80pages,3visuals,history0;version/access/later-mode/ancestry limits disclosed. Artifact MATCH52payloads54files11dirs;16sourceblobs4trees,5primaryPDFs5completedpairs,allauthorbytes/modesunchanged. Parent initial top-level manifest path corrected to actual private/MANIFEST.json without author changes. No mathematical gate/count. Parent Source159 operative-proof reading:NONE.

"""
instructions+=old[old.index('R162BX is CLOSED'):old.index('R162BJ remains archived')]
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source159-selection.json').read_bytes())
nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[259745,260934] and len(sel['folders'])==1 and len(sel['entries'])==36
blobs=[e for e in sel['entries'] if e['type']=='blob']
textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))
assert len(blobs)==30 and textbytes==756340
prior=B/'fresh-arithmetic-discovery-r162by'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md']; inputs=[]
for p in direct:
 a=p.read_bytes(); inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[259745,260934),EXACT Source159 and its linked manuscript. Parent used ONE bounded14000-byte window[259745,273745),decoded only159/160numeric-bold titles and ONLY159body;160body/remainder not decoded;third heading ONLY a byte boundary. An initial alternate heading regex failed and exposed first150 raw bytes of the SAME159 body;corrected pattern reread that same bounded window. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
"""
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex')
 section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+="""Combined30blobs36entriesincludingroots,29non-PDFtexts756340bytes,one compiledPDF. Read actual wrapper,preamble,all twelve sections,all foundations including symbols,shift,counting,constrained,sampling,cube,normalized-cube,transfer,lifting and foundations wrapper,both figure sources,README and references completely. This is substantial operative reading:do not substitute the headline proof for any operative foundation or truncate long files. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored arithmetic-progression,density-increment,reciprocal-sum and relative-counting mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162by* *arithmetic*r162bz*\n'
missing=rules(old)-rules(text)
if missing: text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bz*' in brief.decode()
N.mkdir(mode=0o700); R.mkdir(mode=0o700); (N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x); (N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=159,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=30,canonical_entries=36,canonical_text_objects=29,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body160_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep); print(json.dumps(prep))
