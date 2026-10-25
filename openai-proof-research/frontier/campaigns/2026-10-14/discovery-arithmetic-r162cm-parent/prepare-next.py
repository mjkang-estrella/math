"""Prepare one new Source175 research brief; preserve all prior scopes/guards."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cn-parent';R=B/'fresh-arithmetic-discovery-r162cn';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cn-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads']
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cm-brief.txt').read_bytes();assert sha(oldbytes)=='a0f78deaf5febf012609b070d9e9613a67e78edab70a0e051c691fc2b1d654ab'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read BOTH COMPLETE Source174')].replace('Arithmetic discovery r162cm — confirmed strong-thin-tree operative-proof discovery.','Arithmetic discovery r162cn — confirmed expectation-threshold and graph-decomposition discovery.',1).replace('fresh-arithmetic-discovery-r162cm/','fresh-arithmetic-discovery-r162cn/',1).replace('FRESH DISTINCT Source174','FRESH DISTINCT Source175',1).replace('Own r162cm I/O','Own r162cn I/O',1)
instructions='''Read all THREE COMPLETE Source175 operative manuscripts,actual wrappers and ALL includes before selecting one additional full theorem. Integral/fractional expectation-threshold equivalence with the same budget,Talagrand discrete convexity,and bounded fixed graph-edge decompositions are ALREADY PAID. Credit stronger actual source and primary operations,including the scope of separate piece embeddings. Source truth stipulated;no audit.

Keep family,ground set,density,budget,graph,quantifiers and costs compatible. Separate piece embeddings need not yield one common embedding. Parent alone commissions correctness/contribution reviews;no restricted substitute,renaming or desired-grade retry.

R162CM is CLOSED PREFREEZE/no nominee. Exact prescribed marginals on uniformly thin trees of the same labelled graph remain unproved and UNFROZEN. Stronger metric-cone/source rounding,good-tree hull separation,dominated marginals,Lagrangian weighted-lower condition,boundary strongly Rayleigh laws and conditional labels are paid. A joint face/weighted-lower rounding or exact complementary-base repair controlling every original cut is a sufficient unproved route,not a necessity. The triangle refutes feasible subtraction inference only;it has the desired law. Initial-denominator exact partitions are stronger than marginal realization. No counterexample or algorithm lower bound. Complete canonical text read;primary ancestry incomplete;history0. Parent Source175 operative reading:NONE.

'''
recent=old[old.index('R162CL is CLOSED'):old.index('R162BJ remains archived')]
recent=recent.replace(' Full reading/limits and unchanged artifact seal are in parent intake. Parent Source174 operative-proof reading:NONE.','')
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source175-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[276357,278505] and len(sel['folders'])==3
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')];assert len(blobs)==22 and len(texts)==19 and sum(e['size'] for e in texts)==105743
prior=B/'fresh-arithmetic-discovery-r162cm';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue if needed:ONLY binary sources/CONTENTS.md[276357,278505),EXACT Source175. Parent used ONE14000-byte window[276357,290357),decoded175/176numeric-bold titles and ONLY175body;176body unread,thirdheader boundaryonly. First numeric-header pattern matched none;the same window was recovered with actual bold format before semantic decoding. One family screen. No extra locator,screen,whole catalogue,ancestor inventory or oldscan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
'''
for f in sel['folders']:
 e=next(e for e in texts if e['path'].startswith(f+'/') and e['path'].endswith('/main.tex'))
 section+=f+'\n'+e['path']+';bytes'+str(e['size'])+';Git blob'+e['sha']+'.\n'
section+='''Exactly22blobs35entriesincludingroots,19nonPDFtexts105743bytes,threecompiledPDFs. Read all19 actual texts,including wrappers,every mathematical include,figures,macros,bibliographies and READMEs. Authenticate all22blobs in these three prefixes. Metadata is not proof reading. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
Exceptions admit ONLY these files,not containers,linked bodies,other reviews or aliases. No permission propagates. Protected bodies AND metadata stay PRIVATE/local under original rights.

At most ONE correctly pruned optional ORIGINAL-history traversal. Apply EVERY inherited literal wildcard/substring to full-project-relative POSIX path.casefold() BEFORE descent,eligibility and body access at EVERY depth. Query genuine authored expectation-threshold,cover-budget,discrete-convexity and graph-piece mechanisms. No projectwide-then-filter,ancestor inventory,copied corpus,role/helper derivatives,size cutoff after eligibility,oldscan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncation recovery,late reads,omissions,false admissions. If unused,say so. No perfect-isolation,exhaustive-clearance or priority claim.

Seal once after SAME-logic preflight:sorted unique safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Read-only verification thereafter;edit NO sealed file. Tiny controls suffice;artifact checks are not mathematical gates.

'''
text=prefix+instructions+recent+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162cn* *arithmetic*r162cn*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode()
assert len(brief.decode())<120000,len(brief.decode())
assert 'come back to STANDARD speed' in brief.decode() and {'*arithmetic*162cn*','*arithmetic*r162cn*'}<=rules(brief.decode())
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=175,catalogue_extent=sel['catalogue_extent'],canonical_folders=3,canonical_blobs=22,canonical_entries=35,canonical_text_objects=19,canonical_text_bytes=105743,compiled_pdfs=3,new_family_screens=1,body176_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=1,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes());print(json.dumps(prep))
