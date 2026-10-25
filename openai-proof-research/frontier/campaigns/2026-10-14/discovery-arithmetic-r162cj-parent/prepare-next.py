#!/usr/bin/env python3
"""Prepare a distinct, fully scoped Source172 discovery task."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162ck-parent';R=B/'fresh-arithmetic-discovery-r162ck'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ck-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==847 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cj-brief.txt').read_bytes()
assert sha(oldbytes)=='610a95106b22dc59959948b99314a0fdb85f8e4d6308a4b349d4d3ffea9256bb'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source171')]
prefix=prefix.replace('Arithmetic discovery r162cj — confirmed hypercube-Ramsey operative-proof discovery.','Arithmetic discovery r162ck — confirmed finite Euclidean Ramsey classification discovery.',1).replace('fresh-arithmetic-discovery-r162cj/','fresh-arithmetic-discovery-r162ck/',1).replace('FRESH DISTINCT Source171','FRESH DISTINCT Source172',1).replace('Own r162cj I/O','Own r162ck I/O',1)
instructions="""Read the COMPLETE actual Source172 operative proof,actual wrapper,ALL mathematical includes,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The full tensor characterization of finite Euclidean Ramsey configurations at their ORIGINAL SCALE is ALREADY PAID,including the stated subtransitive and cyclic-at-most-five-point consequences and non-subtransitive Ramsey examples. Credit all stronger actual tensor,stencil,pair,path,group,synchronization and consequence operations at their exact hypotheses,not just the headline. Do not audit stipulated source truth.

Keep ONE original configuration,coordinate field,distance data and scale through the full argument. Congruent copies,homothetic copies,coloring classes,dimension bounds and algorithms have different interfaces. Compatible classical finite-color,algebraic,tensor and source reductions are paid. Read actual primary proofs before calling compatibility unpaid. Sustain derivation and freeze exact full quantifiers only with a viable additional nonroutine proof. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. All older scopes remain immutable.

R162CJ is CLOSED PREFREEZE/no nominee. Fixed-positive-surplus prescribed-color linear cube embedding closes through source/classical operations. Two conditional parent references apply to the same stream;the uniform reference pays tuple caps/means. That compatibility is CLOSED. Uniform zero-surplus or exact half-density extension remains unproved. The balanced bilinear example rejects one strict-gain shortcut but itself has a paid same-host color-flip embedding. Complete parent intake records source/primary reading and ancestry limits,history0,and unchanged sealed originals. Parent Source172 operative-proof reading:NONE.
R162CI remains CLOSED PREFREEZE/no nominee. Original iid incident-flag graph constant-factor endpoint remains unproved;aggregate overlap closes one component only. Repeated-plane terms,joint context replacement and retention remain uncontrolled.
R162CH remains CLOSED PREFREEZE/no nominee. Same-graph/partition/q elementary unimodality remains unproved. Odd-edge quotient and stronger primary operations are paid;finite examples reject specific shortcuts only.
R162CG remains CLOSED PREFREEZE/no nominee. Same-ideal weighted aggregate cancellation remains unproved. The S6 example satisfies that identity and rejects stronger rowwise/unweighted shortcuts;source and primary special cases are paid.
R162CF remains CLOSED PREFREEZE/no nominee. Product-law transfer and fixed-c tail integration are paid;energy-weighted sparse bands and variable-radius algebra remain uncontrolled.
R162CE remains CLOSED PREFREEZE/no nominee. Local-palette comparisons are paid;the unrestricted 3D pinned endpoint's coupled estimate/profile transfer remain unproved. Neither axis-circle nor abstract-colouring examples refute it.
R162CD remains CLOSED PREFREEZE/no nominee. One-part-even parity and charged repair are paid;generic tournament nonsingularity/labelled parity bounds remain unproved. Finite singularity is not generic failure.
R162CC remains CLOSED PREFREEZE/no nominee. Monomial-ratio word planning is paid;common integer mixed-expression counting/alignment remains unproved. The valuation example defeats one template only.

R162CB remains CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Its immutable theorem:every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1,admits one finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,cover r,and pairwise intersections1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. No refreeze,repair,renaming or review retry.
R162CA remains CLOSED PREFREEZE/no nominee;all its completed same-pattern constructions are paid. No exact finite-host equality or additional nonroutine construction closed. All earlier dispositions below remain unchanged.

"""
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source172-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[272740,273998] and len(sel['folders'])==1 and len(sel['entries'])==16
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')]
textbytes=sum(e['size'] for e in texts);assert len(blobs)==12 and len(texts)==11
prior=B/'fresh-arithmetic-discovery-r162cj'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[272740,273998),EXACT Source172. Parent used ONE bounded14000-byte window[272740,286740),decoded only172/173numeric-bold titles and ONLY172body;173body/remainder not decoded;third heading only a byte boundary. ONE new family-body screen. No extra title locator,family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
"""
folder=sel['folders'][0];wrapper=next(e for e in blobs if e['path']==folder+'/build/main.tex')
section+=folder+'\n'+wrapper['path']+';bytes'+str(wrapper['size'])+';Git blob'+wrapper['sha']+'.\n'
section+='Exactly12blobs16entriesincludingroots,11non-PDFtexts'+str(textbytes)+"""bytes,one compiledPDF. Read full main.tex,all7sectionincludes(01-introduction,02-tensors,03-stencil,04-pairs,05-paths,06-groups,07-consequences),synchronizationfigure,refs.bib,andREADME. Authenticate every object and follow actual includes;the wrapper alone is not the operative proof. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored Euclidean-Ramsey,finite-configuration,tensor-stencil,coordinate-field and group-synchronization mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162ce* *arithmetic*r162ck*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162ck*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=172,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=12,canonical_entries=16,canonical_text_objects=11,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body173_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=1,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
