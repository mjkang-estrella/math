#!/usr/bin/env python3
"""Prepare one distinct Source150 round, retaining standing rules and guards."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bq-parent';R=B/'fresh-arithmetic-discovery-r162bq';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bq-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==825 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bp-brief.txt').read_bytes();assert sha(oldbytes)=='921251be4c817492b7c97cf248811a4eb13a952e39afb343ed5129da4741df74'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read BOTH complete actual Source149')].replace('Arithmetic discovery r162bp — confirmed weakly-reversible permanence operative-proof discovery.','Arithmetic discovery r162bq — confirmed triangular-billiard weak-mixing operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bp/','fresh-arithmetic-discovery-r162bq/',1).replace('FRESH DISTINCT Source149','FRESH DISTINCT Source150',1).replace('Own r162bp I/O','Own r162bq I/O',1)
instructions='''Read BOTH complete actual Source150 operative proofs,actual wrappers,ALL mathematical sections,figures/references and strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:unit-speed billiard flow in EVERY nondegenerate Euclidean triangle with at least one angle irrational relative to pi is weakly mixing for normalized Liouville measure(area times uniform direction),equivalently its self-product is ergodic. No genericity or Diophantine restriction. The companion's full ergodicity statement,off the null vertex-hitting trajectories,is also paid. Credit ALL stronger actual proof operations,not just catalogue headlines;do not audit their stipulated truth.

Retain ONE actual triangle,phase space,flow,time parameter and invariant measure in every composition. Classical spectral/ergodic/product consequences are paid when their full hypotheses match. Weak mixing does not itself supply mixing,quantitative decay,all-direction assertions,uniformity near rational triangles,or new perturbation stability. Read actual primary proofs before treating any compatibility as an unpaid operation. Develop sustained mathematics and identify a genuinely additional operation;freeze exact hypotheses,quantifiers,constants and conclusions only when a complete nonroutine proof is viable. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening earlier targets.

R162BP is CLOSED PREFREEZE/no nominee. The same-flow pointwise cut-balanced mass-action absorption comparison is paid by source finite affine plateaux/monomial order/square-root descent,primary within-linkage flexibility,cut regrouping,finite near-active compactness and scalar no-downcrossing. Divergent-integral reaction vectors spanning the original stoichiometric space give common classwise finite entry;zero/unbounded locally integrable rates are allowed,entry time depends on the law. The asynchronous gap is CLOSED. A periodic2A<->3A pulse gives blowup before reversal despite equal unit-window rate integrals;this refutes that specific relaxation only. No new frozen target or further review. R162BO and R162BM remain CLOSED correctnessPASS/contributionTECHNICAL,zero count. All old scopes,including continuous entropy-overlap,remain unchanged.

Parent read the complete r162bp derivation20374bytes,WORKING,limits11135bytes,handoffs/verifier. Author read16canonicaltexts110230bytes and93primarypages(3full,2partial),history0. Parent artifact MATCH53payloads55files13dirs;allauthorbytes/modes unchanged. Parent initially displayed protected/neighboring AGENTS filenames in an unnecessary broad search after context restoration;no hit body was read/used. Its manifest-display type error was corrected before verification. No perfect-isolation claim. Parent source proof reading for this NEW family:NONE.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source150-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[246783,248327] and len(sel['folders'])==2 and len(sel['entries'])==19
blobs=[e for e in sel['entries'] if e['type']=='blob'];assert len(blobs)==13 and sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))==92105
prior=B/'fresh-arithmetic-discovery-r162bp';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[246783,248327),EXACT Source150 including BOTH manuscripts. Parent used ONE bounded14000-byte window[246783,260783),decoded only150/151numeric-bold titles and ONLY150body;151body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path'] in {folder+'/build/main.tex',folder+'/build/source/main.tex'});section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined13blobs19entriesincludingroots,11non-PDFtexts92105bytes,two compiledPDFs. Read BOTH operative wrappers and all mathematical sections/figures/references fully;record typography-only handling separately. Authenticate exact bytes;do not guess wrappers or substitute abstracts/metadata for proof. Parent operative-source reading:NONE. lean/docs/150.md,if present,is scoped comparator navigation only;no downstream formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored triangular-billiard,irrational-angle,weak-mixing,eigenfunction,Liouville-flow and spectral mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162bq* *arithmetic*r162bq*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bq*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=150,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=13,canonical_entries=19,canonical_text_objects=11,canonical_text_bytes=92105,compiled_pdfs=2,new_family_screens=1,body151_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
