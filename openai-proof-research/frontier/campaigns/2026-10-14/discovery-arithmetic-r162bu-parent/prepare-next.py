#!/usr/bin/env python3
"""Prepare one distinct Source155 round, retaining original guards and standing brief."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bv-parent';R=B/'fresh-arithmetic-discovery-r162bv';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bv-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==830 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256'];matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bu-brief.txt').read_bytes();assert sha(oldbytes)=='e979a0e464286695c1a7dfc0a96c3aaaf340ee6d7868d7d4e6efe7f469875412'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read ALL FOUR complete actual Source154')].replace('Arithmetic discovery r162bu — confirmed pointwise multiple-ergodic-average operative-proof discovery.','Arithmetic discovery r162bv — confirmed three-dimensional translational-tiling operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bu/','fresh-arithmetic-discovery-r162bv/',1).replace('FRESH DISTINCT Source154','FRESH DISTINCT Source155',1).replace('Own r162bu I/O','Own r162bv I/O',1)
instructions='''Read the COMPLETE actual Source155 operative proof,actual wrapper,ALL mathematical sections,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source result is ALREADY PAID:one finite translational tile in Z^3 admits tilings but no fully periodic tiling;its unit-cube thickening gives the same counterexample in R^3 even allowing arbitrary real translation vectors. Credit ALL stronger actual word-rule,cyclic-encoding,activation,common-solution,stacking and dimension-three operations,not only the headline. Do not audit stipulated source truth.

Retain ONE actual tile,translation set,ambient group,notion of tiling and period group in every composition. Absence of a full-rank period lattice is not automatically absence of every nonzero period. Connectivity,topology,regularity,robustness,arbitrary real translations or quantitative decoding require their exact compatible source/primary interfaces. Standard product/quotient/lifting/encoding operations are paid when actual hypotheses match. Read operative primary proofs before calling compatibility an unpaid bridge. Sustain mathematical derivation and identify one genuinely additional nonroutine operation;freeze every hypothesis,quantifier and conclusion only with a viable full proof. Parent commissions independent correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target.

Structural171's period-group,stacking,quotient-lifting,connectivity and digit-disagreement comparisons remain unchanged. Its forced-kernel removal,auxiliary-fibre classification and approximate-tiling decoding directions remain unproved/unfrozen;do not reopen or renominate them. This family is distinct from immediately preceding Source154;no exhaustive history clearance is claimed. All earlier scopes in the standing brief are immutable.

R162BU is CLOSED PREFREEZE/no nominee. Actual source mixing product extension,separable tensor algebra and finite-window BFKO lower-density argument pay universal single-target return times with source conull set preceding every target quantifier;L1 target extension is classical. Nilsequence cancellation with the actual Sobolev normalization and general polynomial-target norm convergence,including uniform distinct-degree bounds,are source/actual-primary compositions. General pointwise transfer without mixing rate and the whole-arbitrary-target-array selected-law identity remain unproved,unfrozen sufficient routes. Fixed-shift correlations alone are not the closed proof. No quantitative/nilsystem/norm-only substitute is nominated.

Parent read full derivation25792bytes,WORKING,limits9570bytes,handoffs/verifier. Author read43canonicaltexts629528bytes across4manuscripts and86physicalprimarypages across7PDFs(including1cover),6full extracts59pages,18visualchecks,with partial/transitive/late-recovery limits and history0. Artifact MATCH97payloads99files22dirs;allauthorbytes/modesunchanged. Older Analytic159,Salem/degree31,entropy-overlap and all other scopes remain unchanged;closed technical results remain zero-count. Parent new-source proof reading:NONE;prior navigation limitations remain disclosed.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')];historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source155-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[254942,255934] and len(sel['folders'])==1 and len(sel['entries'])==17
blobs=[e for e in sel['entries'] if e['type']=='blob'];textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'));assert len(blobs)==13 and textbytes==92831
prior=B/'fresh-arithmetic-discovery-r162bu';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[254942,255934),EXACT Source155. Parent used ONE bounded14000-byte window[254942,268942),decoded only155/156numeric-bold titles and ONLY155body;156body/remainder not decoded;third heading ONLY a byte boundary. ONE family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/paper.tex');section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+='''Combined13blobs17entriesincludingroot,12non-PDFtexts92831bytes,one compiledPDF. Read actual wrapper,all seven operative sections,both figures,README and references completely;do not confuse metadata authentication with reading. Authenticate exact bytes;no guessed wrappers or abstract-only proof reading. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored translational-tiling,period-group,word-encoding,activation,stacking and geometric-realization mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162br* *arithmetic*r162bv*\n';missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bv*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=155,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=13,canonical_entries=17,canonical_text_objects=12,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body156_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
