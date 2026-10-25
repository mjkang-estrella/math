#!/usr/bin/env python3
"""Prepare one distinct Source154 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bu-parent';R=B/'fresh-arithmetic-discovery-r162bu';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bu-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==829 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bt-brief.txt').read_bytes();assert sha(oldbytes)=='0db5fc65b9a3543aa5f436112f07fb112b44d7c5e683238250a95311a8036a3c'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source153')].replace('Arithmetic discovery r162bt — confirmed Bernoulli-convolution arithmetic operative-proof discovery.','Arithmetic discovery r162bu — confirmed pointwise multiple-ergodic-average operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bt/','fresh-arithmetic-discovery-r162bu/',1).replace('FRESH DISTINCT Source153','FRESH DISTINCT Source154',1).replace('Own r162bt I/O','Own r162bu I/O',1)
instructions='''Read ALL FOUR complete actual Source154 operative proofs,actual wrappers,ALL mathematical sections,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:for every invertible bimeasurable mixing probability-preserving transformation,on an arbitrary not-necessarily-standard probability space,and each fixed finite tuple of bounded complex measurable functions,consecutive multiple averages of every finite length converge almost everywhere to the product of their integrals along ALL positive integer averaging lengths,without a mixing rate. The companions' fourfold/triple conclusions and arbitrary pairwise distinct NONZERO integer slopes(including negative)for triples are paid too. Credit ALL stronger actual selected-row,packing,channel,activation,transfer and square proof operations,not just these headlines. Do not audit stipulated source truth.

Retain ONE actual transformation,probability,tuple,averaging sequence and exceptional-set quantifier in each composition. Common full-measure sets,unbounded functions,polynomial slopes,commuting actions,weak-mixing replacement,pointwise variations or selected lengths require their exact compatible source/primary interfaces. Standard spectral/ergodic/tensor/approximation operations are paid when hypotheses match. Read operative primary proofs before calling a compatibility issue an unpaid bridge. Sustain mathematical derivation and identify one genuinely additional nonroutine operation;freeze every hypothesis,quantifier and conclusion only with a viable full proof. Parent commissions independent correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target.

Earlier Analytic159 tensor-square/weak-mixing comparison,arbitrary-selected-length and whole-plane-array/positive-witness gaps remain unchanged;do not reopen or renominate them. This family is distinct from immediately preceding Source153;no exhaustive history clearance is claimed. All prior frozen/PREFREEZE scopes in the standing brief remain immutable.

R162BT is CLOSED PREFREEZE/no nominee. Source Fourier families plus actual primary finite entropy conversion and independent-block information bounds pay a quartic Salem dimension deficit uniform over arbitrary independent nonstationary binary biases,including deterministic coordinates,with law-dependent full-mass sets. Summable coefficient influence,coupling and bounded-difference concentration pay a common thin set for the exact degree31 parameter under small Cesaro mean bias deviation. All-bias degree31 joint predictor control remains unproved,unfrozen;individual Fourier moduli do not order the signed joint moments. No new theorem/gate/count. Older r128 finite-Salem-field sign-sum/projection,sextic and Markov scopes remain unchanged.

Parent read full derivation28195bytes,WORKING,limits12018bytes,handoffs/verifier. Author read8canonicaltexts138436bytes and83physicalprimarypages across4PDFs(including4nonarticlepages),3full extracts74pages,4visualchecks;newer-than-pin input,failed access,late reads and incomplete ancestry are explicit;history0. Artifact MATCH35payloads37files8dirs,allauthorbytes/modesunchanged. R162BS/BR/BQ/BP remain paid/no nominee;R162BO/BM remain CLOSED correctnessPASS/contributionTECHNICAL,zero count. New source proof reading by parent:NONE;prior navigation limitations remain disclosed.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source154-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[251819,254942] and len(sel['folders'])==4 and len(sel['entries'])==62
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==47 and textbytes==629528
prior=B/'fresh-arithmetic-discovery-r162bt';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[251819,254942),EXACT Source154 and ALL FOUR linked manuscripts. Parent used ONE bounded14000-byte window[251819,265819),decoded only154/155numeric-bold titles and ONLY154body;155body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path'] in [folder+'/build/main.tex',folder+'/build/paper/main.tex']);section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined47blobs62entriesincludingroots,43non-PDFtexts629528bytes,four compiledPDFs. Read ALL FOUR actual wrappers and full operative includes/figures/references completely,including the larger triple base/localization proofs;do not confuse metadata authentication with reading. Authenticate exact bytes;no guessed wrappers or abstract-only proof reading. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored multiple-ergodic-average,mixing,selected-row,packing,channel,variation and polynomial-average mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162bu*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bu*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=154,catalogue_extent=sel['catalogue_extent'],canonical_folders=4,canonical_blobs=47,canonical_entries=62,canonical_text_objects=43,canonical_text_bytes=textbytes,compiled_pdfs=4,new_family_screens=1,body155_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
