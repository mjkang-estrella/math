#!/usr/bin/env python3
"""Prepare the distinct Source164 round with inherited isolation and scope intact."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162cc-parent'; R=B/'fresh-arithmetic-discovery-r162cc'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cc-brief.txt'
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s): return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}

head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]; checks=[]; legacy=[]
for i,x in enumerate(t['tasks']):
 if i==838 or x.get('status') not in {'running','queued','waiting'}: continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x
  legacy.append(i); continue
 a=(P/x['brief']).read_bytes()
 assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values()); checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]: assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cb-brief.txt').read_bytes()
assert sha(oldbytes)=='77dd16362731744c01b61985c7fcb372eac90e47a40d34fb5c43ec2e2610e428'
old=oldbytes.decode(); marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1]; assert len(standing.encode())==5570
prefix=old[:old.index('Read BOTH COMPLETE actual Source162')]
prefix=prefix.replace('Arithmetic discovery r162cb — confirmed Ryser covering operative-proof discovery.','Arithmetic discovery r162cc — confirmed finite sums and products operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162cb/','fresh-arithmetic-discovery-r162cc/',1).replace('FRESH DISTINCT Source162','FRESH DISTINCT Source164',1).replace('Own r162cb I/O','Own r162cc I/O',1)
instructions="""Read the COMPLETE actual Source164 operative proof,actual wrapper,ALL mathematical sections and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. Entire source results are ALREADY PAID:for every finite coloring of the positive integers and every positive integer k,one k-element set has ALL nonempty subset sums AND ALL nonempty subset products in ONE common color. Credit every stronger actual framework,arithmetic,correlation,prediction,rough-progression,cube-limit and alignment operation,not just the headline. Do not audit stipulated source truth.

Keep ONE actual coloring,witness set,common color,scale sequence and limiting object through each composition. Finite versus infinite configurations,distinctness,nonempty subsets,mixed sums/products,ordered words and uniform quantitative/algorithmic bounds are different interfaces. Classical compactness,finite Ramsey transfer,ultrafilter and dynamical consequences are paid at compatible hypotheses. Read primary proofs before declaring compatibility unpaid. Sustain derivation and freeze exact full quantifiers only with a viable additional nonroutine proof. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. Every older scope remains immutable.

R162CB is CLOSED full-scope correctness PASS and contribution TECHNICAL,with correctness condition discharged,ZERO increment. The unchanged theorem covers every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1:one finite simple r-partite r-uniform hypergraph,exactly r nonisolated vertices per part,cover r,and pairwise distinct-edge intersection1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;PROOF SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. Full same-configuration omitted-line quotient and all cover budgets are paid source/classical reduction. No author change,repair or desired-grade retry. Parent read full proof-review derivations12549bytes and limits9951bytes,prior full contribution review25950bytes and limits10196bytes. Correctness reviewer read18source texts291598bytes and40primarypages;contribution reviewer readsame18texts and63primarypages. Both disclose incomplete ancestry,history0,peerinspection0. Both seals and all61authorfiles match;artifact checks are not gates. Parent Source164 operative-proof reading:NONE.

"""
instructions+=old[old.index('R162CA is CLOSED'):old.index('R162BJ remains archived')]
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/Source164-selection.json').read_bytes())
nav=json.loads((D/'private/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[264581,265378] and len(sel['folders'])==1 and len(sel['entries'])==15
blobs=[e for e in sel['entries'] if e['type']=='blob']
textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))
assert len(blobs)==12 and textbytes==261554
prior=B/'fresh-arithmetic-discovery-r162cb'
direct=[D/'assessment.md',prior/'STATEMENT.md',prior/'private/PROOF.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md']; inputs=[]
for p in direct:
 a=p.read_bytes(); inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[264581,265378),EXACT Source164 and its linked manuscript. Parent used ONE bounded14000-byte window[264581,278581),decoded only164/165numeric-bold titles and ONLY164body;165body/remainder not decoded. The actual catalogue skips the inferred163 label here:two assertions expecting consecutive numbering failed,and recovery displayed first120raw bytes of THIS164family and numeric heading indices/offsets in the same window. No additional family body was decoded. ONE new family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
"""
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex')
 section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+="""Combined12blobs15entriesincludingroots,11non-PDFtexts261554bytes,one compiledPDF. Read actual main.tex,all eight sections(introduction,framework,arithmetic,correlation,prediction,rough_progressions,cube_limits,alignment),README and references completely. Do not substitute summaries for operative proof. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored finite-sums/products,common-color,additive-multiplicative and cube-alignment mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162cc* *arithmetic*r162cc*\n'
missing=rules(old)-rules(text)
if missing: text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162cc*' in brief.decode()
N.mkdir(mode=0o700); R.mkdir(mode=0o700); (N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x); (N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=164,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=12,canonical_entries=15,canonical_text_objects=11,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body165_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep); print(json.dumps(prep))
