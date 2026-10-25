#!/usr/bin/env python3
"""Prepare one distinct Source152 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bs-parent';R=B/'fresh-arithmetic-discovery-r162bs';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bs-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==827 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162br-brief.txt').read_bytes();assert sha(oldbytes)=='57f503c7dc770ee2a514bbd936ca88b8749490299322f6ad2a81badd127437c6'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source151')].replace('Arithmetic discovery r162br — confirmed C1 homological-entropy counterexample operative-proof discovery.','Arithmetic discovery r162bs — confirmed zero-entropy smooth-model obstruction operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162br/','fresh-arithmetic-discovery-r162bs/',1).replace('FRESH DISTINCT Source151','FRESH DISTINCT Source152',1).replace('Own r162br I/O','Own r162bs I/O',1)
instructions='''Read the COMPLETE actual Source152 operative proof,actual wrapper,preamble,ALL mathematical sections and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:one zero-Kolmogorov-Sinai-entropy ergodic invertible transformation of a standard nonatomic probability space is not measurably conjugate to ANY C-infinity diffeomorphism preserving a strictly positive smooth probability density on ANY compact finite-dimensional manifold. The SAME example excludes all finite dimensions,nonorientable manifolds and smooth boundary. Credit ALL stronger actual stationary/linear/switching/word/process/obstruction proof operations,not only that headline. Do not audit stipulated source truth.

Keep ONE actual probability-preserving system,measure,conjugacy notion,regularity and model class throughout each composition. Products,factors,extensions,changed invariant measures,less regular or vanishing densities,flows and finite-smoothness models require their exact additional compatible interfaces. Standard measurable dynamics,spectral,entropy and smooth-volume consequences are paid when the actual source/primary hypotheses match. Read strongest operative primary proofs before treating a compatibility issue as an unpaid bridge. Sustain mathematical derivation;freeze all hypotheses,quantifiers and conclusions only when a complete genuinely additional nonroutine proof is viable. Parent commissions separate full correctness and actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening old scopes.

R162BR is CLOSED PREFREEZE/no nominee. Its full source homotopy action,periodic-orbit attraction and finite-order invariant-measure dynamics are paid. For each finite integer r,the same prediction-series retuning yields a possibly different Cr map on a fixed seven-dimensional product. Source reset plus a trapping cutoff makes the 100th iterate identically normal-zero near the clock circle;disk attachment,compatible neighborhood retraction,handle thickening and doubling yield one fixed simply connected closed smooth eleven-manifold with separate Cr maps,zero topological entropy and H2 eigenvalue2^100. The earlier smoothing concern is CLOSED as a source/primary/classical comparison. This gives no single C-infinity map,invertibility,prescribed homology,minimal dimension or limiting modulus. None of those alternatives is a frozen diagnostic or impossibility theorem.

Parent read full derivation29702bytes,WORKING,limits15578bytes,handoffs/verifier. Author read8canonicaltexts55396bytes and102distinct mathematical primarypages across9of10acquiredPDFs;6full extracted papers/notes57pages,10renderedpages,with OCR/late-reading/access/transitive limits and history0 disclosed. Artifact MATCH61payloads63files8dirs,allauthorbytes/modesunchanged. R162BQ remains paid/no nominee,its general collision-phase/rank-two recurrence routes unfrozen. R162BP remains paid/no nominee;R162BO/R162BM remain CLOSED correctnessPASS/contributionTECHNICAL,zero count. All old scopes,including continuous entropy-overlap,remain unchanged. Earlier parent filename-navigation limitations remain disclosed;no perfect-isolation claim. Parent source proof reading for this NEW family:NONE.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source152-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[249357,250526] and len(sel['folders'])==1 and len(sel['entries'])==15
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==12 and textbytes==138943
prior=B/'fresh-arithmetic-discovery-r162br';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[249357,250526),EXACT Source152. Parent used ONE bounded14000-byte window[249357,263357),decoded only152/153numeric-bold titles and ONLY152body;153body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex');section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined12blobs15entriesincludingroot,11non-PDFtexts138943bytes,one compiledPDF. Read the actual wrapper,preamble,all seven mathematical sections and references fully;record typography-only handling separately. Authenticate exact bytes;do not guess wrappers or substitute abstracts/metadata for proof. Parent operative-source reading:NONE. lean/docs/152.md,if present,is scoped comparator navigation only;no downstream formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored smooth-model,positive-volume,stationary-process,word-complexity and entropy-obstruction mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162bs*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bs*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=152,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=12,canonical_entries=15,canonical_text_objects=11,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body153_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
