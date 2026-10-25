#!/usr/bin/env python3
"""Prepare the distinct Source161 round with inherited isolation and scope intact."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162ca-parent'; R=B/'fresh-arithmetic-discovery-r162ca'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ca-brief.txt'
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s): return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}

head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]; checks=[]; legacy=[]
for i,x in enumerate(t['tasks']):
 if i==835 or x.get('status') not in {'running','queued','waiting'}: continue
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
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bz-brief.txt').read_bytes()
assert sha(oldbytes)=='079aba7fa14b59a8963af73e590efa42340927a827de78ed4f85f222a3f7815f'
old=oldbytes.decode(); marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1]; assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE actual Source159')]
prefix=prefix.replace('Arithmetic discovery r162bz — confirmed arithmetic-progression operative-proof discovery.','Arithmetic discovery r162ca — confirmed Sidorenko and forcing operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bz/','fresh-arithmetic-discovery-r162ca/',1).replace('FRESH DISTINCT Source159','FRESH DISTINCT Source161',1).replace('Own r162bz I/O','Own r162ca I/O',1)
instructions="""Read the COMPLETE actual Source161 operative proof,actual wrapper,macros,ALL mathematical sections,figures and references plus strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE source results are ALREADY PAID:a connected bipartite graph with35vertices66edges violates Sidorenko's bound,and the same graph violates the forcing conjecture. Credit ALL stronger actual kernel,orbit,planted,tail,transverse,complex and consequence operations,not just these headlines. Do not audit stipulated source truth.

Keep ONE actual pattern,graphon or finite graph,density,parameter path and normalization through every construction. Homomorphism versus induced densities,graphon versus simple finite graphs,matching versus approximating constraints,and fixed versus uniform parameters are different interfaces. Classical blowups,tensor products,interpolation,compactness,concentration and quasirandomness consequences are paid at compatible hypotheses. Read primary proofs before declaring compatibility unpaid. Sustain mathematical derivation;freeze exact full quantifiers only with a viable additional nonroutine proof. Parent commissions separate correctness and actual-primary contribution reviews. No self-gates/count,desired-grade retry,narrowing or renamed old target. Every older scope remains immutable.

R162BZ is CLOSED PREFREEZE/no nominee. Same-majorant supersaturation,dense modelling,finite-error densification and cap-free diagonal removal close as paid comparisons. Stronger sparse transfer still needs productive-path and weighted-error control on one common scale schedule. Fixed-sampler,small-patch and nonsummability examples limit only specified deductions,not general sparse transfer. Parent read full DERIVATION24705bytes,SOURCE-INTERFACES11286bytes,WORKING,READING-LIMITS9602bytes,handoffs/verifier. Author read29source texts756340bytes,13explicit-companiontexts90576bytes,4completeprimarypapers48pages,2visuals,5completedexceptions,history0. Access/version/recoveries and incomplete ancestry are disclosed. Artifact MATCH76payloads78files15dirs,44pinnedblobs/10trees,4primaryPDFs5completedpairs,allauthorbytes/modesunchanged. Source160's van der Waerden companion is already read and paid;its catalogue body was skipped. Parent new Source161 operative-proof reading:NONE.

"""
instructions+=old[old.index('R162BY is CLOSED'):old.index('R162BJ remains archived')]
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source161-selection.json').read_bytes())
nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[262059,263076] and len(sel['folders'])==1 and len(sel['entries'])==19
blobs=[e for e in sel['entries'] if e['type']=='blob']
textbytes=sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))
assert len(blobs)==15 and textbytes==179335
prior=B/'fresh-arithmetic-discovery-r162bz'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md']; inputs=[]
for p in direct:
 a=p.read_bytes(); inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[262059,263076),EXACT Source161 and its linked manuscript. Parent used ONE bounded14000-byte window[262059,276059),decoded only161/162numeric-bold titles and ONLY161body;162body/remainder not decoded;third heading ONLY a byte boundary. Source160 body was skipped because its explicit companion was already completely read and paid. ONE new family-body screen. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
"""
for folder in sel['folders']:
 w=next(e for e in blobs if e['path']==folder+'/build/main.tex')
 section+=folder+'\n'+w['path']+';bytes'+str(w['size'])+';Git blob'+w['sha']+'.\n'
section+="""Combined15blobs19entriesincludingroots,14non-PDFtexts179335bytes,one compiledPDF. Read actual wrapper,macros,all eight sections(complex,consequences,introduction,kernel,orbits,planted,tail,transverse),both figure sources,README and references completely. Do not substitute summaries for operative proof. Authenticate exact bytes;parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exact exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored homomorphism-density,Sidorenko,forcing,graphon-kernel and quasirandomness mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162by* *arithmetic*r162ca*\n'
missing=rules(old)-rules(text)
if missing: text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162ca*' in brief.decode()
N.mkdir(mode=0o700); R.mkdir(mode=0o700); (N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x); (N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=161,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=15,canonical_entries=19,canonical_text_objects=14,canonical_text_bytes=textbytes,compiled_pdfs=1,new_family_screens=1,body162_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep); print(json.dumps(prep))
