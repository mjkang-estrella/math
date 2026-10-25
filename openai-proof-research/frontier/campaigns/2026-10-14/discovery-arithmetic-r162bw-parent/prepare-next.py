#!/usr/bin/env python3
"""Prepare one distinct Source157 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bx-parent';R=B/'fresh-arithmetic-discovery-r162bx';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bx-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==832 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bw-brief.txt').read_bytes();assert sha(oldbytes)=='af5758856d447651b2327199a0e17a72fa7a839381f9793626af5567c5bba2be'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source156')].replace('Arithmetic discovery r162bw — confirmed nine-dimensional Borsuk operative-proof discovery.','Arithmetic discovery r162bx — confirmed graph-coloring and clique-minor operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bw/','fresh-arithmetic-discovery-r162bx/',1).replace('FRESH DISTINCT Source156','FRESH DISTINCT Source157',1).replace('Own r162bw I/O','Own r162bx I/O',1)
instructions='''Read ALL THREE complete actual Source157 operative proofs,actual wrappers,preambles,ALL mathematical sections,figures,INPUTS and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source results are ALREADY PAID:arbitrarily large finite simple graphs with independence number at most2 have ordinary fractional chromatic number greater than their Hadwiger number;examples also violate fractional chi_f<=mu+1 for the Colin de Verdiere invariant;every finite nonempty graph obeys chi_list<=C h for one universal integerC. Credit ALL stronger actual geometric/frame-law/moment/realization/collision/common-limit/matrix/measure and density/routing/separability/list-recursion operations,not just these headlines. Do not audit stipulated source truth.

Keep ONE actual graph,matrix,measure,branch-set system and coloring notion in each composition. Chromatic,list and fractional chromatic numbers,Hadwiger number,negative index,matrix rank and the Colin de Verdiere invariant are different interfaces. Retain any Strong-Arnold,well-signedness,corank,connectivity or uniform-parameter hypotheses exactly. Classical blowups,products,minor transfers,concentration and spectral consequences are paid when actual hypotheses match. Read operative primary proofs before declaring compatibility unpaid. Sustain mathematical derivation;freeze all hypotheses,quantifiers and conclusions only with a viable genuinely additional nonroutine proof. Parent commissions separate full correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target.

Structural164's intermediate concentration/list-coloring comparison and unpaid n=t^2 regime remain unchanged. Structural168's fixed-base well-signed block counterexample and unresolved exactly-two-negative/Strong-Arnold variants remain unchanged. Do not reopen or renominate those targets. This family is distinct from immediately preceding Source156;no exhaustive history clearance is claimed. All older scopes are immutable.

R162BW is CLOSED PREFREEZE/no nominee. The exact eleven-cap upper cover of the fixed R4 rank-one projectors gives b(X)=11 with the stipulated source,already a public companion claim. Eight semialgebraic orthogonality colors have full diameter in each class;finite subsets with actual sqrt2 diameter have an eight-part strict cover. Quantitative nets,continuous soft-label threshold and Lipschitz defect estimates are paid;optimal finite margin/defect rates remain unproved/unfrozen. Parent read full derivation23957bytes,WORKING,limits12444bytes,handoffs/verifier. Author read14canonicaltexts64332bytes and83primarypages across7PDFs,3full papers45pages,12visualchecks;failed external certificate access,late/OCR/transitive limits and history0 disclosed. Artifact MATCH66payloads68files10dirs,allauthorbytes/modesunchanged;parent control-message suffix assertion corrected without changing author files. Earlier tiling,ergodic-transfer,Salem/degree31 and entropy scopes unchanged. Parent new-source proof reading:NONE;no perfect-isolation claim.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source157-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[256796,258915] and len(sel['folders'])==3 and len(sel['entries'])==72
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==60 and textbytes==995207
prior=B/'fresh-arithmetic-discovery-r162bw';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[256796,258915),EXACT Source157 and ALL THREE linked manuscripts. Parent used ONE bounded14000-byte window[256796,270796),decoded only157/158numeric-bold titles and ONLY157body;158body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex');section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined60blobs72entriesincludingroots,57non-PDFtexts995207bytes,three compiledPDFs. Read ALL THREE actual wrappers/preambles,every mathematical include including matrix-rank/matrix-trees/frame-laws/asymmetric pieces,INPUTS,figures and references completely. This is substantial operative reading;do not replace it by theorem summaries or omit long sections. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored graph-coloring,clique-minor,Colin-de-Verdiere,matrix-invariant and list-coloring mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162bx*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bx*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=157,catalogue_extent=sel['catalogue_extent'],canonical_folders=3,canonical_blobs=60,canonical_entries=72,canonical_text_objects=57,canonical_text_bytes=textbytes,compiled_pdfs=3,new_family_screens=1,body158_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
