#!/usr/bin/env python3
"""Prepare one distinct Source156 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bw-parent';R=B/'fresh-arithmetic-discovery-r162bw';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bw-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==831 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bv-brief.txt').read_bytes();assert sha(oldbytes)=='5c94c30889494021ffe4307821fd7995da1a2c476222404858e5dd495a0abe83'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source155')].replace('Arithmetic discovery r162bv — confirmed three-dimensional translational-tiling operative-proof discovery.','Arithmetic discovery r162bw — confirmed nine-dimensional Borsuk operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bv/','fresh-arithmetic-discovery-r162bw/',1).replace('FRESH DISTINCT Source155','FRESH DISTINCT Source156',1).replace('Own r162bv I/O','Own r162bw I/O',1)
instructions='''Read the COMPLETE actual Source156 operative proof,actual wrapper,preamble,ALL mathematical sections,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:the compact set of rank-one orthogonal projectors onto lines in R^4,with the Frobenius metric and its nine-dimensional affine ambient realization,cannot be covered by ten sets of strictly smaller diameter. Credit ALL stronger actual geometric,topological,six-label,ten-label and extension proof operations,not just this headline. Do not audit stipulated source truth.

Keep ONE actual configuration,metric,diameter,ambient dimension,cover cardinality and covering-set regularity in every composition. Infinite compact and finite configurations,qualitative impossibility and quantitative diameter gap,arbitrary subsets and measurable/open covers require their exact compatible interfaces. Classical compactness,graph-coloring,metric embedding and topological consequences are paid when actual hypotheses match. Read operative primary proofs before calling compatibility an unpaid bridge. Sustain mathematical derivation and identify one genuinely additional nonroutine operation;freeze every hypothesis,quantifier and conclusion only with a viable full proof. Parent commissions independent correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. This family is distinct from immediately preceding Source155;no exhaustive history clearance is claimed. Every older scope remains immutable.

R162BV is CLOSED PREFREEZE/no nominee. One universal source cycle map,valid binary graph/seed encoding,exact conditional-expectation stacking,and actual arbitrary-tiling quotient/connected-shell proofs yield a fully charged deterministic quasipolynomial ordinary-coordinate constructor from explicit domino systems to one connected Z3 tile and the same R3 cube union. Both seed integer components and common activation/extraction are retained. No additional nonroutine operation was identified. A polynomial-size joint cyclic representation remains unproved/unfrozen;independent-prime growth and failed direct noncyclic/prime-power substitutions are costs of those representations,not universal lower bounds. Structural171 forced-period,fibre and approximate-decoding scopes remain untouched.

Parent read full derivation31304bytes,WORKING,limits13989bytes,handoffs/verifier. Author read12canonicaltexts92831bytes and93paperpages plus3illustrations,complete technical text71548bytes and bibliography10323bytes;3full paper extracts61pages,8visualchecks,partial ancestry/late recovery disclosed,history0. Artifact MATCH64payloads66files10dirs;allauthorbytes/modesunchanged. Older ergodic-transfer,Salem/degree31,entropy-overlap and all other scopes remain unchanged;closed technical results remain zero-count. Parent new-source proof reading:NONE;prior navigation limitations remain disclosed.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source156-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[255934,256796] and len(sel['folders'])==1 and len(sel['entries'])==19
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==15 and textbytes==64332
prior=B/'fresh-arithmetic-discovery-r162bv';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[255934,256796),EXACT Source156. Parent used ONE bounded14000-byte window[255934,269934),decoded only156/157numeric-bold titles and ONLY156body;157body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex');section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined15blobs19entriesincludingroot,14non-PDFtexts64332bytes,one compiledPDF. Read actual wrapper,preamble,all seven operative sections,three figures,README and references completely;do not confuse metadata authentication with reading. Authenticate exact bytes;no guessed wrappers or abstract-only proof reading. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored Borsuk,diameter-cover,projector,line-coloring and topological-obstruction mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162bw*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bw*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=156,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=15,canonical_entries=19,canonical_text_objects=14,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body157_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
