#!/usr/bin/env python3
"""Prepare the distinct Source158 round with inherited isolation and scope intact."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162by-parent'; R=B/'fresh-arithmetic-discovery-r162by'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162by-brief.txt'
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s): return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}

head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]; checks=[]; legacy=[]
for i,x in enumerate(t['tasks']):
 if i==833 or x.get('status') not in {'running','queued','waiting'}: continue
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
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bx-brief.txt').read_bytes()
assert sha(oldbytes)=='37c3213a15d9122c662c36ed3f848a1dc7284cdd4b3cbbcaf0a2a4acb96faff6'
old=oldbytes.decode(); marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1]; assert len(standing.encode())==5570
prefix=old[:old.index('Read ALL THREE complete actual Source157')]
prefix=prefix.replace('Arithmetic discovery r162bx — confirmed graph-coloring and clique-minor operative-proof discovery.','Arithmetic discovery r162by — confirmed planar unit-distance coloring operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bx/','fresh-arithmetic-discovery-r162by/',1).replace('FRESH DISTINCT Source157','FRESH DISTINCT Source158',1).replace('Own r162bx I/O','Own r162by I/O',1)
instructions='''Read the COMPLETE actual Source158 operative proof,actual wrapper,preamble,ALL mathematical sections,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source theorem is ALREADY PAID:every coloring of the Euclidean plane with five colors has a monochromatic unit-distance pair,without regularity assumptions. Credit ALL stronger actual palette,angular,transition,rigidity,spectral,exclusion-continuum,transfer,common-state and compatibility operations,not just the headline. Do not audit stipulated source truth.

Keep ONE actual coloring,Euclidean realization,palette and common geometric constraints throughout each construction. Arbitrary colorings,measurable colorings,finite graphs,compactness witnesses,explicit finite constructions,approximate unit distances and robust forbidden intervals are different conclusions. Classical compactness,finite-witness extraction,scaling,products,rigidity and coloring consequences are paid whenever their hypotheses match;do not relabel them as substantial. Read operative primary proofs before declaring a compatibility unpaid. Sustain mathematical derivation;freeze exact hypotheses,quantifiers and all conclusions only with a viable genuinely additional nonroutine proof. Parent commissions separate full correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. All older scopes remain immutable.

R162BX is CLOSED PREFREEZE/no nominee. Actual-cover constraint-budget connectivity extraction,consistent-cover list transfer,and covariance/fractional-DP/IS-richness compositions are paid. A random-matching cover defeats one fixed coloring order while reversing the order succeeds;this does NOT refute a universal linear correspondence-coloring bound. The uniform linear-cost same-cover small-set deletion argument remains unproved/unfrozen. Parent fully read DERIVATION29799bytes,SOURCE-INTERFACES16623bytes,WORKING,READING-LIMITS12396bytes,handoffs and verifier. Author read57canonicaltexts995207bytes and99primarypages across8PDFs,5complete56pages,3partial43pages,4visualchecks;late Dvorak-Yepremyan/access/transitive limits and history0 are disclosed. Artifact MATCH235payloads237files21dirs,60sourceblobs/12trees,8primaryPDFs/5completedpairs;authorbytes/modes unchanged. Structural164/168 and all earlier scopes remain unchanged. Parent new-source operative-proof reading:NONE;no perfect-isolation claim.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source158-selection.json').read_bytes())
nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[258915,259745] and len(sel['folders'])==1 and len(sel['entries'])==20
blobs=[e for e in sel['entries'] if e['type']=='blob']
textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))
assert len(blobs)==16 and textbytes==225514
prior=B/'fresh-arithmetic-discovery-r162bx'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md']; inputs=[]
for p in direct:
 a=p.read_bytes(); inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[258915,259745),EXACT Source158 and its linked manuscript. Parent used ONE bounded14000-byte window[258915,272915),decoded only158/159numeric-bold titles and ONLY158body;159body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex')
 section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined16blobs20entriesincludingroots,15non-PDFtexts225514bytes,one compiledPDF. Read actual wrapper,preamble,every mathematical include including angular,interfaces,introduction,palettes,rigidity,spectral,transfer and transitions,all three figures and references completely. Do not replace operative reading by theorem summaries. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored planar unit-distance coloring,angular palette,geometric rigidity and spectral transfer mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162by* *arithmetic*r162by*\n'
missing=rules(old)-rules(text)
if missing: text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162by*' in brief.decode()
N.mkdir(mode=0o700); R.mkdir(mode=0o700); (N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x); (N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=158,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=16,canonical_entries=20,canonical_text_objects=15,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body159_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep); print(json.dumps(prep))
