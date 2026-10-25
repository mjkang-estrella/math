#!/usr/bin/env python3
"""Prepare a distinct, fully scoped Source170 discovery task."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162ci-parent';R=B/'fresh-arithmetic-discovery-r162ci'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ci-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==845 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ch-brief.txt').read_bytes()
assert sha(oldbytes)=='e89cae1cb04a3a3c81bdebf0b883e7b4d3cb7bc0e1b443c016ca31c1c41f657f'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source169')]
prefix=prefix.replace('Arithmetic discovery r162ch — confirmed chromatic-quasisymmetric elementary-positivity discovery.','Arithmetic discovery r162ci — confirmed off-diagonal Ramsey logarithmic-exponent discovery.',1).replace('fresh-arithmetic-discovery-r162ch/','fresh-arithmetic-discovery-r162ci/',1).replace('FRESH DISTINCT Source169','FRESH DISTINCT Source170',1).replace('Own r162ch I/O','Own r162ci I/O',1)
instructions="""Read BOTH COMPLETE actual Source170 operative proofs,actual wrappers,ALL mathematical includes,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The full fixed-s logarithmic exponent r(s,t)=t^(s-1)/(log t)^(s-2+o(1)) for every fixed s>=5 is ALREADY PAID,including the s=5 and s>=6 proofs and actual quantifier dependence. Credit every stronger geometry,learning,prediction,marking,entropy,compression and construction operation at its exact hypotheses,not just the headlines. Do not audit stipulated source truth.

Keep ONE original graph/random construction,clique restriction,independent-set parameter and probability law through the full argument. Fixed-s asymptotics,uniform varying-s statements,explicit algorithms,local properties and resilience have different interfaces. Compatible classical probabilistic,entropy,alteration and source operations are paid. Read actual primary proofs before calling compatibility unpaid. Sustain derivation and freeze exact full quantifiers only with a viable additional nonroutine proof. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. All older scopes remain immutable.

R162CH is CLOSED PREFREEZE/no nominee. Full same-graph,same-partition,same-q elementary unimodality remains unproved. Primary pre-Lefschetz transfer,odd-edge positive quotient,acyclic Lefschetz,mutation,Schur hard Lefschetz,abelian whole-path cancellation and marked modular operations are paid. Finite mutation/polynomial/modular examples reject specified shortcuts,not the full graph assertion. Parent read all mathematical/limitation records and the root verifier. Reading,ancestry and mode limits remain explicit;history0. Sealed artifact MATCH,bytes/modes unchanged;no mathematical gates. Parent Source170 operative-proof reading:NONE.

R162CG remains CLOSED PREFREEZE/no nominee. Full same-ideal weighted aggregate cancellation remains unproved. The S6 example satisfies that identity,invalidating only stronger rowwise/unweighted shortcuts;source global edge-image/freeness and primary special cases are paid.
R162CF remains CLOSED PREFREEZE/no nominee. Product-law sampling,hereditary pin bounds and fixed-c tail integration are paid. Energy-weighted sparse bands and variable-radius derivative/discriminant terms remain uncontrolled;the radius-factor example defeats only that shortcut.
R162CE remains CLOSED PREFREEZE/no nominee. Local palettes,radial space,line-plane products and light-line pruning are paid;the unrestricted 3D pinned endpoint's coupled estimate/profile transfer remain unproved. Axis-circle and abstract-colouring examples do not refute it.
R162CD remains CLOSED PREFREEZE/no nominee. Characteristic-two pairing,one-part-even parity and charged repair are paid. Generic tournament nonsingularity/labelled parity-weight bounds remain unproved;finite singularity is not generic failure.
R162CC remains CLOSED PREFREEZE/no nominee. Finite monomial-ratio word planning is paid;common integer mixed-expression counting/alignment remains unproved. The valuation example defeats one template only.

R162CB remains CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Its immutable theorem:every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1,admits one finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,cover r,and pairwise intersections1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. No refreeze,repair,renaming or review retry.
R162CA remains CLOSED PREFREEZE/no nominee;its same-pattern regularity,forest matching,proper-edge,affine/complement and many-color constructions are paid. No exact finite-host equality or additional nonroutine construction closed. All earlier dispositions below remain unchanged.

"""
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source170-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[270748,271973] and len(sel['folders'])==2 and len(sel['entries'])==34
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')]
textbytes=sum(e['size'] for e in texts);assert len(blobs)==28 and len(texts)==26
prior=B/'fresh-arithmetic-discovery-r162ch'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[270748,271973),EXACT Source170 and BOTH manuscripts. Parent used ONE bounded14000-byte window[270748,284748),decoded only170/171numeric-bold titles and ONLY170body;171body/remainder not decoded;third heading only a byte boundary. ONE new family-body screen. No extra title locator,family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
"""
for folder in sel['folders']:
 name='paper.tex' if '/The-Sharp-' in folder else 'main.tex'
 wrapper=next(e for e in blobs if e['path']==folder+'/build/'+name)
 section+=folder+'\n'+wrapper['path']+';bytes'+str(wrapper['size'])+';Git blob'+wrapper['sha']+'.\n'
section+='Exactly28blobs34entriesincludingroots,26non-PDFtexts'+str(textbytes)+"""bytes,two compiledPDFs. Read both full wrappers. The s=5 proof includes introduction,upper-bound,flags-entropy,predictor-statement/setup/geometry/score/completion,compression-local/tree,final-conversion,and references.bib. The s>=6 proof includes all seven numbered sections00-introduction through06-conclusion,figurevalidation,references.tex/bib,andREADME. Authenticate every object and follow actual includes;wrappers alone are not the operative proofs. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored off-diagonal-Ramsey,clique-free-construction,independence,entropy and probabilistic-compression mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162ce* *arithmetic*r162ci*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162ci*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=170,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=28,canonical_entries=34,canonical_text_objects=26,canonical_text_bytes=textbytes,compiled_pdfs=2,new_family_screens=1,body171_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=2,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
