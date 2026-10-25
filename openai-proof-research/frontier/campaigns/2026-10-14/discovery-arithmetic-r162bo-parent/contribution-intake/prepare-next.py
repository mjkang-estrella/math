#!/usr/bin/env python3
"""Prepare distinct Source149 research after the final technical disposition."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
N=B/'discovery-arithmetic-r162bp-parent';R=B/'fresh-arithmetic-discovery-r162bp';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bp-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==824 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bo-brief.txt').read_bytes();assert sha(oldbytes)=='cf87668efc7c24a5b3df7a66d58843e75720794caa0c69f8102be7a11c6fc7b9'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source148')].replace('Arithmetic discovery r162bo — confirmed entropy-rate dimension operative-proof discovery.','Arithmetic discovery r162bp — confirmed weakly-reversible permanence operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bo/','fresh-arithmetic-discovery-r162bp/',1).replace('FRESH DISTINCT Source148','FRESH DISTINCT Source149',1).replace('Own r162bo I/O','Own r162bp I/O',1)
instructions='''Read BOTH complete actual Source149 operative proofs,actual wrappers,ALL mathematical sections,figures/references and strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:every finite weakly reversible mass-action network with fixed positive rate constants has one common compact convex forward-invariant absorbing set in each positive stoichiometric class,including unbounded classes. The set depends only on network,rates,class;entry time may depend on initial state. All positive trajectories eventually share positive lower and finite upper concentration bounds. The companion's individual global existence,boundedness and persistence are also paid. Credit ALL stronger actual proof operations,not just these headlines. Do not audit source truth or nominate these results.

Track ONE actual network,stoichiometric class,rate vector and flow in every composition. Individual trajectory bounds are not automatically common classwise bounds;the source already pays the latter. Compact initial-set uniform entry,global uniform entry,parameter-family uniformity,nonautonomous or vanishing rates,boundary classes,changed kinetics and reaction-network perturbations require their exact additional interfaces. Standard dissipative-system,convexity,ODE,compactness and entropy/Lyapunov consequences are paid whenever strongest actual hypotheses match. Do not assume complex balance,detailed balance,uniqueness of equilibrium,convergence or bounded stoichiometric classes. Read actual primary proofs before treating compatibility as a new gap.

Perform sustained mathematical derivation after complete source and relevant strongest primary reading. Choose ONE genuinely additional operation;freeze every network/rate/domain hypothesis,quantifier,constant,topology and conclusion only when a complete nonroutine proof is viable,then prove the ENTIRE scope. Parent alone commissions correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening older full targets. No exhaustive-history or worldwide-priority claim.

R162BO is CLOSED correctnessPASS/contributionTECHNICAL at the entire unchanged E(rho)<=H(rho)/3 theorem for countably supported finite-Shannon-entropy real laws,without support/moment bounds,coefficient1/3 optimal. Its correctness is self-contained;the contribution condition is discharged. Do not seek another grade or rename this theorem. Two full classical reductions pay the exact constant and scope. In cumulative-mass coordinates,weighted Cauchy–Schwarz against p+2u and Tonelli give J<=log(1+2T/p)/4;the original endpoint variance decomposition and prefix-mass Jensen give3E<=H. Independently,uniform-noise MMSE with an explicit Gaussian scale mixture of second moment12 plus scalar Gaussian I-MMSE gives the same bound. Finite quantization/local Fatou handle the full countable scope. The known uniform-lattice example pays optimality. The proposed atom-jump potential is not an unpaid operation.

Contribution review read9canonicaltexts,65primary/companionpages and18classicalGSVpages;ancestry incomplete,history0. Initial combined parent display truncation was recovered with complete ASSESSMENT/DERIVATION reads. Model-output supplement provenance and prefreeze mutable-main-to-pin rebinding are explicit. Parent/bundled artifact MATCH26payloads28files3dirs;all60author files/modes unchanged. No count increase. R162BM remains CLOSED correct/technical;R162BN sparse-caustic work remains PREFREEZE/no nominee. All older scopes/dispositions and the continuous entropy-overlap target remain unchanged.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'Source149-selection.json').read_bytes());nav=json.loads((D/'next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[244844,246783] and len(sel['folders'])==2 and len(sel['entries'])==26
blobs=[e for e in sel['entries'] if e['type']=='blob'];assert len(blobs)==18 and sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))==110230
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162bo/STATEMENT.md',B/'fresh-arithmetic-discovery-r162bo/PROOF.md',B/'arithmetic-r162bo-contribution-r1/private/ASSESSMENT.md',B/'arithmetic-r162bo-contribution-r1/private/READING-LIMITS.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[244844,246783),EXACT Source149 including BOTH manuscripts. Parent used ONE bounded14000-byte window[244844,258844),decoded only149/150numeric-bold titles and ONLY149body;150body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay. Navigation is not exhaustive clearance.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path'] in {folder+'/build/main.tex',folder+'/build/paper.tex'});section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined18blobs26entriesincludingroots,16non-PDFtexts110230bytes,two compiledPDFs. Read BOTH operative wrappers and all mathematical sections/figures/references fully;record typography-only handling separately. Authenticate exact bytes;do not guess wrappers or substitute abstracts/metadata for proof. Parent operative-source reading:NONE. lean/docs/149.md,if present,is scoped comparator navigation only;no downstream formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored mass-action,weak reversibility,stoichiometry,permanence,persistence,absorbing-set and rate-family mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162bp* *arithmetic*r162bp*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bp*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=149,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=18,canonical_entries=26,canonical_text_objects=16,canonical_text_bytes=110230,compiled_pdfs=2,new_family_screens=1,body150_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
