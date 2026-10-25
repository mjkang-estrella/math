#!/usr/bin/env python3
"""Prepare a distinct, fully scoped Source166 discovery task."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162ce-parent';R=B/'fresh-arithmetic-discovery-r162ce'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ce-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==841 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cd-brief.txt').read_bytes()
assert sha(oldbytes)=='7d00efd032338a25a16b3ba7c8d5df16e33ce316b5bddcc9e96063caf75eb4cb'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read BOTH COMPLETE actual Source165')]
prefix=prefix.replace('Arithmetic discovery r162cd — confirmed graph crossing-number operative-proof discovery.','Arithmetic discovery r162ce — confirmed higher-dimensional distinct-distances discovery.',1).replace('fresh-arithmetic-discovery-r162cd/','fresh-arithmetic-discovery-r162ce/',1).replace('FRESH DISTINCT Source165','FRESH DISTINCT Source166',1).replace('Own r162cd I/O','Own r162ce I/O',1)
instructions="""Read the COMPLETE actual Source166 operative proof,actual wrapper,ALL mathematical includes,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The entire fixed-dimension d>=3 Euclidean distinct-distance lower bound c_d n^(2/d),for every finite set of distinct points without geometric assumptions,is ALREADY PAID. Credit all stronger actual incidence,motion,partition,profile,concentration,depth,secant,approximation and sparse-cone operations at their real hypotheses,not just the headline. Do not audit stipulated source truth.

Keep ONE original point configuration,dimension,metric and distance relation through the entire construction. Distinct distances,unit-distance multiplicities,pinned distances,energy,distance distributions and quantitative stability have different interfaces. Classical Cauchy-Schwarz,averaging,projection,partitioning and source consequences are paid when compatible;read actual primary proofs before claiming compatibility unpaid. Do not merely rename a previous common-scale,overlap or incidence gap. Sustain derivation and freeze exact full quantifiers only with a viable additional nonroutine proof. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. Every older scope remains immutable.

R162CD is CLOSED PREFREEZE/no nominee. Integral cycle pairing and characteristic-two source compatibility pay the one-part-even parity comparison and charged rank-defect repair;universal symmetry compression is weaker than classical triple averaging. Generic detector nonsingularity for every binary tournament or the alternative exact labelled parity Hamming-weight bound remain unproved. Common labels follow conditionally from nonzero determinant products;the finite singular specialization is not a generic counterexample,as the same tournament has invertible specializations. Parent read full DERIVATION23952bytes,SOURCE-INTERFACES9896,WORKING4812,READING-LIMITS11479,handoffs/verifier. Author read17canonicaltexts111715bytes and both proofs,5fullprimaryPDFs90pages4works,3visualchecks;initial-permission/later-full-mode and ancestry/access limits disclosed;history0. Artifact MATCH58payloads60files15dirs,19blobs7trees5primaryPDFs5completedpairs;sealedbytes/modesunchanged. Parent Source166 operative-proof reading:NONE.

R162CC remains CLOSED PREFREEZE/no nominee. Broader finite monomial-ratio word planning,triangular support and backward protection are paid. Common integer mixed-expression counting/alignment remains unproved;the two-row valuation example defeats one template only.

R162CB remains CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Its immutable theorem:every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1,admits one finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,cover r,and pairwise intersections1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. No refreeze,repair,renaming or review retry.

R162CA remains CLOSED PREFREEZE/no nominee. Same-pattern regularity,forest matching,proper-edge cancellation,affine/complement analysis and many-color constructions are paid. No extra nonroutine construction or exact finite-host equality was proved. All intervening PREFREEZE dispositions below remain unchanged;their gaps are not nominees.

"""
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source166-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[266874,267833] and len(sel['folders'])==1 and len(sel['entries'])==23
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')]
textbytes=sum(e['size'] for e in texts);assert len(blobs)==19 and len(texts)==18
prior=B/'fresh-arithmetic-discovery-r162cd'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
folder=sel['folders'][0];wrapper=next(e for e in blobs if e['path']==folder+'/build/paper.tex')
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[266874,267833),EXACT Source166. Parent used ONE bounded14000-byte window[266874,280874),decoded only166/167numeric-bold titles and ONLY166body;167body/remainder not decoded;third heading only a byte boundary. ONE new family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
"""+folder+'\n'+wrapper['path']+';bytes'+str(wrapper['size'])+';Git blob'+wrapper['sha']+'.\n'
section+='Exactly19blobs23entriesincludingroots,18non-PDFtexts'+str(textbytes)+'''bytes,one compiledPDF. Read full paper.tex,preamble,all eleven section bodies(approximation,classical-incidence,concentration,depth,introduction,motions,polynomial,profiles,reduction,secants,sparse-cones),all three figureTeXs,README and bibliography. The wrapper alone is not the operative proof. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored distinct-distance,unit-distance,energy,motion-incidence and quantitative-configuration mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162ce* *arithmetic*r162ce*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162ce*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=166,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=19,canonical_entries=23,canonical_text_objects=18,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body167_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
