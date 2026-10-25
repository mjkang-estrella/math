#!/usr/bin/env python3
"""Prepare one distinct Source153 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bt-parent';R=B/'fresh-arithmetic-discovery-r162bt';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bt-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==828 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bs-brief.txt').read_bytes();assert sha(oldbytes)=='5acf695b9f3908ff66a209415e536f8bc5a04918ffe1529106c175082c06ef6e'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source152')].replace('Arithmetic discovery r162bs — confirmed zero-entropy smooth-model obstruction operative-proof discovery.','Arithmetic discovery r162bt — confirmed Bernoulli-convolution arithmetic operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bs/','fresh-arithmetic-discovery-r162bt/',1).replace('FRESH DISTINCT Source152','FRESH DISTINCT Source153',1).replace('Own r162bs I/O','Own r162bt I/O',1)
instructions='''Read the COMPLETE actual Source153 operative proof,actual wrapper,ALL mathematical sections,certificates,verification code and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:an infinite one-sided approximation criterion using explicit finite sets of algebraic units classifies singular versus absolutely continuous unbiased Bernoulli convolutions for every lambda in(0,1);reciprocals of EVERY quartic Salem number in(1,2) and the specified non-Pisot root of an explicit degree31 polynomial are singular. The criterion is NOT a finite membership algorithm. Credit ALL stronger actual classification/certificate/non-Pisot/Salem operations,not just these headlines. Do not audit stipulated source truth.

Retain ONE original parameter,law,bias,coefficient sequence,normalization and measure notion in each composition. Singularity,dimension,Fourier decay and absolute continuity are different conclusions. Biased/nonstationary/multicoefficient,parameter-uniform,quantitative or algorithmic conclusions need their exact compatible source/primary interfaces. Read primary proofs before calling compatibility an unpaid bridge. Sustained mathematics must identify one genuinely additional nonroutine operation;freeze every hypothesis,quantifier and conclusion only with a viable full proof. Parent commissions separate correctness and actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target.

The older r128 Salem-field finite-sign-sum comparison and its unrestricted-real-coefficient projection obstruction remain unchanged;do not renominate them or reopen old sextic/Markov targets. This family is distinct from immediately preceding Source152;no exhaustive history clearance is claimed. All earlier scopes in the standing brief remain immutable.

R162BS is CLOSED PREFREEZE/no nominee. Same-measure factor obstruction,partition-uniform conditional-square total variation,two likelihood cuts giving output domination8nu,stationary log-boundary coboundary protection,and fixed Holder/weaker logarithmic derivative-modulus rescaling close as source/primary/classical payments. The general-C1 common-scale derivative/inverse/minor/cell-entropy budget remains unproved,unfrozen. Smooth realizations with singular laws and circularized systems are paid at their actual hypotheses,not identified with the source for free. No theorem or diagnostic selected and no gates/count.

Parent read full derivation37248bytes,WORKING,limits11764bytes,handoffs/verifier. Author read11canonicaltexts138943bytes and167distinct physical primarypages across6PDFs(including1cover),3full extracts68pages,8latevisualchecks,with OCR/access/ancestry limits and history0 disclosed. Artifact MATCH52payloads54files8dirs;allauthorbytes/modesunchanged. R162BR fixed-eleven-manifold finite-regularity comparison remains paid/no nominee,not one smooth or invertible map. R162BQ/BP also remain paid/no nominee;R162BO/BM remain CLOSED correctnessPASS/contributionTECHNICAL,zero count. Parent new-source proof reading:NONE;prior navigation limitations remain disclosed.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source153-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[250526,251819] and len(sel['folders'])==1 and len(sel['entries'])==12
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==9 and textbytes==138436
prior=B/'fresh-arithmetic-discovery-r162bs';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[250526,251819),EXACT Source153. Parent used ONE bounded14000-byte window[250526,264526),decoded only153/154numeric-bold titles and ONLY153body;154body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex');section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined9blobs12entriesincludingroot,8non-PDFtexts138436bytes(including verification/verify_degree31.py),one compiledPDF. Read actual wrapper,classification,certificate,nonpisot,salem,references,README and verification code completely. Authenticate exact bytes;no guessed wrappers or abstract-only proof reading. Running code does not audit stipulated truth or replace mathematical derivation. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored Bernoulli-convolution,algebraic-unit,Salem,one-sided-approximation and measure-classification mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162bt*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bt*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=153,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=9,canonical_entries=12,canonical_text_objects=8,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body154_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
