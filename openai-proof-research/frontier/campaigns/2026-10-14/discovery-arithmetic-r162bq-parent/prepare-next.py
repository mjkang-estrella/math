#!/usr/bin/env python3
"""Prepare one distinct Source151 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162br-parent';R=B/'fresh-arithmetic-discovery-r162br';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162br-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==826 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bq-brief.txt').read_bytes();assert sha(oldbytes)=='79e961b0e076175759361345ce2a72540e833245f6da39b07fea81a4765109d0'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read BOTH complete actual Source150')].replace('Arithmetic discovery r162bq — confirmed triangular-billiard weak-mixing operative-proof discovery.','Arithmetic discovery r162br — confirmed C1 homological-entropy counterexample operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bq/','fresh-arithmetic-discovery-r162br/',1).replace('FRESH DISTINCT Source150','FRESH DISTINCT Source151',1).replace('Own r162bq I/O','Own r162br I/O',1)
instructions='''Read the COMPLETE actual Source151 operative proof,actual wrapper,ALL mathematical sections,figure and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:a noninvertible C1 self-map of a compact smooth manifold without boundary has zero topological entropy while the induced action on second real homology has eigenvalue2. This disproves the general C1 self-map homological entropy lower bound. Credit ALL stronger actual construction/clock/orbit/entropy/homology operations,not just that headline;do not audit stipulated source truth.

Keep ONE actual compact manifold,map,regularity class,homological action and entropy notion in every composition. Products,iterates,dimension changes,suspensions,extension to diffeomorphisms,quantitative derivative moduli and prescribed homology require the exact compatible source/primary hypotheses. Do not infer invertibility,C1+alpha or smoothness from C1 construction. Classical topological,dynamical,embedding and smoothing consequences are paid when actual interfaces match. Read operative primary proofs before treating compatibility as an unpaid bridge. Perform sustained mathematics to identify a genuinely additional operation;freeze every hypothesis,quantifier and conclusion only with a viable full nonroutine proof. Parent commissions independent correctness and separate actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening old scopes.

R162BQ is CLOSED PREFREEZE/no nominee. The stronger actual source double proposition and elementary side reflections pay double weak mixing,physical-time parity,Cesaro decorrelation,even-order collision-eigenvalue exclusion and T^(2^r) ergodicity. The full rank-one every-direction width-measure recurrence/perpendicular-orbit composition is paid by the actual Troubetzkoy primary and T^2 ergodicity. One common analytic angular observable's residual arbitrarily slow averages are paid by rational projections,actual finite-time perturbation,Baire and mean ergodic theory. General collision-phase seam transmission/Fourier tails and rank-two recurrence remain unproved,unfrozen sufficient routes,not impossibility results. No new theorem or gate/count.

Parent read full derivation31644bytes,WORKING,limits12875bytes,handoffs/verifier. Author read11canonicaltexts92105bytes and103primarypages(3full papers54pages),with late Vorobets/Troubetzkoy recoveries and incomplete ancestry,history0. Artifact MATCH67payloads69files14dirs;allauthorbytes/modes unchanged. Earlier parent AGENTS filename overrun remains disclosed;no perfect-isolation claim. R162BP remains paid/no nominee;R162BO and R162BM remain CLOSED correctnessPASS/contributionTECHNICAL,zero count. All old scopes,including continuous entropy-overlap,remain unchanged. Parent source proof reading for this NEW family:NONE.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source151-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[248327,249357] and len(sel['folders'])==1 and len(sel['entries'])==12
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==9 and textbytes==55396
prior=B/'fresh-arithmetic-discovery-r162bq';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[248327,249357),EXACT Source151. Parent used ONE bounded14000-byte window[248327,262327),decoded only151/152numeric-bold titles and ONLY151body;152body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/source/main.tex');section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined9blobs12entriesincludingroot,8non-PDFtexts55396bytes,one compiledPDF. Read the operative wrapper and all mathematical sections,clock figure and references fully;record typography-only handling separately. Authenticate exact bytes;do not guess wrappers or substitute abstracts/metadata for proof. Parent operative-source reading:NONE. lean/docs/151.md,if present,is scoped comparator navigation only;no downstream formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored homological-entropy,C1-counterexample,clock/orbit-construction and regularity mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162br*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162br*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=151,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=9,canonical_entries=12,canonical_text_objects=8,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body152_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
