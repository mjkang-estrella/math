#!/usr/bin/env python3
"""Prepare Source147 after closing the same-scope technical candidate."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
N=B/'discovery-arithmetic-r162bn-parent';R=B/'fresh-arithmetic-discovery-r162bn';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bn-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==820 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bm-brief.txt').read_bytes()
assert sha(oldbytes)=='20d0475443c2d73001a13c2b28faaa6fa669759cab78f2123f4fdedad9a9958f'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source146')].replace('Arithmetic discovery r162bm — confirmed standard-map metric-entropy operative-proof discovery.','Arithmetic discovery r162bn — confirmed near-boundary billiard-rigidity operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bm/','fresh-arithmetic-discovery-r162bn/',1).replace('FRESH DISTINCT Source146','FRESH DISTINCT Source147',1).replace('Own r162bm I/O','Own r162bn I/O',1)
instructions='''Read BOTH complete actual Source147 operative proofs,actual wrappers,ALL mathematical includes,figures/references and strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE near-boundary Birkhoff result is ALREADY PAID:for a smooth strictly convex planar billiard with positive curvature,a full grazing annulus continuously foliated by individually invariant essential curves forces an analytic boundary,a jointly analytic collar of smooth strictly convex caustics,and an ellipse. A continuous physical collar of smooth closed convex caustics also forces an ellipse,without transverse differentiability assumed. Read every stronger actual hypothesis-removal,regularity,continuation,geometric and quantitative operation;headlines are not scope boundaries. Do not audit source truth or nominate these conclusions.

Keep ONE actual billiard table,its boundary regularity/positive curvature,reflection law,physical caustic collar and full phase annulus through each construction. Leafwise smoothness,transverse continuity,joint smoothness/analyticity,full collars versus Cantor KAM families,and individually invariant curves versus setwise-preserved families are distinct interfaces. Projective/affine/symplectic coordinate changes do not automatically preserve Euclidean billiard reflection or physical convexity. Charge all norm,parameter,degeneracy,continuation and compactness dependencies. Classical Lazutkin/KAM/normal-form and geometric rigidity compositions are paid wherever their strongest actual hypotheses hold. Read actual primary proofs before calling a compatibility step new.

Perform sustained mathematical derivation after complete operative source and relevant strongest primary reading. Choose ONE genuinely additional operation;freeze every hypothesis,quantifier,regularity,constant and conclusion only when a complete nonroutine proof is viable,then prove the ENTIRE scope. Parent alone commissions correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening older full targets. No history-clearance or worldwide-priority claim.

R162BM is CLOSED:independent full-scope correctness PASS relative to stipulated Source146;independent full-scope contribution TECHNICAL,with its correctness condition discharged. It is NOT the twentieth finding. The unchanged original standard-map normalized-area entropy h_m(f_k)=log(pi*k)+o(1) for the ENTIRE positive real parameter tail is now PAID by the review's complete source/classical reduction. Do not seek another grade,relabel its scope or reopen it. The sufficient reduction keeps ORIGINAL growth arrays,uses elementary one-step mean/second moments and cone bounds,small initial second moments for affinity tests,and retains the initial cap contribution alpha*beta. A SINGLE terminal Cauchy–Schwarz estimate and positive weak-measure subtraction remove at least matching terminal mass. All original bridge,four-point,cancellation,affine leakage/cut,positive local dilation,shape and capped-balance operations apply. No joint compensated multiscale-clock theorem is required. This full reduction,not a failed naive route,pays every frozen conclusion.

Author/read/review limitations stay explicit:all11source texts145989bytes read;12blobs16entries;author BXY read AFTER freeze/BEFORE drafting. Correctness review reads full Mane/errata/BXY;contribution reads four fullpapers pluserrata and Blumenthal sections1–3. Contribution98completepages15images;recursive ancestry incomplete,history0. Parent/bundled contribution artifact MATCH23payloads25files4dirs;all69author files unchanged. These are artifact checks,not grades. All old smooth-spectrum,continuous entropy-overlap and other frozen/prefreeze scopes remain unchanged and closed under their existing dispositions.

'''
older='R162BJ remains archived PREFREEZE/no nominee. Full factorization/primitive-root source and compact same-polynomial binary-precision root-ball comparison are paid;all old scopes and reading limits remain preserved in their immutable records. No new gap was frozen.\n\n'+old[old.index('R162BI remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'Source147-selection.json').read_bytes());nav=json.loads((D/'next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[242223,243744] and len(sel['folders'])==2 and len(sel['entries'])==39
blobs=[e for e in sel['entries'] if e['type']=='blob'];assert len(blobs)==30
assert sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))==601146
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162bm/STATEMENT.md',B/'fresh-arithmetic-discovery-r162bm/private/PROOF.md',B/'arithmetic-r162bm-contribution-r1/private/ASSESSMENT.md',B/'arithmetic-r162bm-contribution-r1/private/READING-LIMITS.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[242223,243744),EXACT Source147 including BOTH manuscripts. Parent used ONE bounded14000-byte window[242223,256223),decoded only147/148 numeric-bold titles and ONLY147body. Source148body/remainder NOT decoded;third heading ONLY a boundary,not a title/body read. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay. Navigation is not exhaustive clearance.

Confirmed canonical folders and actual wrappers from complete-tree metadata:
'''
for f in sel['folders']:
 w=next(e for e in blobs if e['path']==f+'/build/main.tex');section+=f+'\n'+w['path']+'; bytes'+str(w['size'])+'; Git blob'+w['sha']+'.\n'
section+='''Combined30blobs39entriesincludingroots,28textualobjects601146bytes,two compiled PDFs. Read BOTH wrappers and ALL operative sections,figures and references completely. Metadata is not semantic proof reading;do not substitute guessed wrappers or abstracts. Parent operative-source reading:NONE. lean/docs/147.md,if present,is only scoped comparator navigation;no downstream formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored billiard/caustic/invariant-curve,foliation,regularity,continuation and rigidity mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check safe exact membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162bn* *arithmetic*r162bn*\n\n'
text=prefix+instructions+older+section+historical+isolation+extra
missing=rules(old)-rules(text)
if missing:text+='\nAll remaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode()
assert len(brief.decode())<120000,len(brief.decode())
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bn*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=147,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=30,canonical_entries=39,canonical_text_objects=28,canonical_text_bytes=601146,compiled_pdfs=2,new_family_screens=1,body148_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
