"""Prepare a Source177 author conversation; all scopes/guards retained."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cp-parent';R=B/'fresh-arithmetic-discovery-r162cp';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cp-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads']
for p in [N,R,BP]:assert not p.exists(),p
a=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162co-brief.txt').read_bytes();assert sha(a)=='55e17fbef0268657cc20561cbfc9788c4a99e885ef25938c23151430b3de9442'
old=a.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read the COMPLETE Source176')].replace('Arithmetic discovery r162co — confirmed edge-count Kahn–Kalai operative-proof discovery.','Arithmetic discovery r162cp — confirmed bounded-degree coboundary-expander discovery.',1).replace('fresh-arithmetic-discovery-r162co/','fresh-arithmetic-discovery-r162cp/',1).replace('This is a NEW Source176 canonical-manuscript round adjacent to archived Source175,not a renamed continuation of its fixed-two-piece target.','This is a FRESH Source177 manuscript round,not a continuation of the threshold targets.',1).replace('Own r162co I/O','Own r162cp I/O',1)
prefix=re.sub(r'Before creation the parent checked.*?No perfect-isolation/exhaustive-clearance claim follows\.', 'Parent checked new paths against recorded foreign INITIAL briefs,without a liveness query. Own r162cp I/O is authorized;only FIVE exact completed files below exempt protected originals. No perfect-isolation/exhaustive-clearance claim.',prefix,flags=re.S)
instructions='''Read COMPLETE Source177/all includes and actual strongest primary/companion proofs. All-dimensional bounded-degree F2 expansion and stronger source operations are PAID. Preserve the complex,coefficients,norm,degree bound and all uniformity/algorithm costs. Source truth stipulated;no audit.

R162CO is CLOSED PREFREEZE/no nominee. Full q_f(H;n)<=C p_E(H;n) for every original simple H,n,budget1/2 remains unproved/unfrozen. Resampling,uniform-copy symmetrization at logarithmic density and exact prefix/assignment accounting are paid. Joint all-witness multiplicity remains missing. Triangle/star examples defeat specific shortcuts,not the full comparison. Parent alone assigns reviews/gates/count;no restricted substitute,renaming or desired-grade retry.
Structural170's reported full intermediate-congruence-cover/flat-coefficient/nonlinear-cofilling reductions were source/classical compositions. Arbitrary noncongruence monodromy and alphabet-uniform primitive algorithms stayed unresolved/unfrozen. Preserve these scopes;do not present their restatement as new or access protected old roots without an exact exception.

'''
recent=old[old.index('R162CN is CLOSED'):old.index('R162BJ remains archived')]
recent=recent.replace(' Complete canonical text read;primary ancestry incomplete;history0. Parent Source175 operative reading:NONE.','')
older=old[old.index('R162BJ remains archived'):old.index('Catalogue if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source177-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[279582,280658] and len(sel['folders'])==1
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')];assert len(blobs)==10 and len(texts)==9 and sum(e['size'] for e in texts)==52577
prior=B/'fresh-arithmetic-discovery-r162co';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 b=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(b),sha256=sha(b),mode=p.stat().st_mode))
e=next(e for e in texts if e['path'].endswith('/main.tex'))
section='''Catalogue:ONLY binary sources/CONTENTS.md[279582,280658),EXACT Source177. Parent used ONE14000-byte window[279582,293582),decoded177/178titles and ONLY177body;178body unread,thirdheading boundaryonly. One body screen;no extra locator,screen,whole catalogue,ancestor inventory or oldscan replay.
Canonical folder and ACTUAL wrapper from complete-tree metadata:
'''+sel['folders'][0]+'\n'+e['path']+';bytes'+str(e['size'])+';Git blob'+e['sha']+'''.
10blobs15entries,9nonPDFtexts52577bytes,onecompiledPDF. Read ALL9texts,mathematical includes,figures,macros,references,README;authenticate10blobs. Parent Source177 operative reading:NONE.
Read FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
Exceptions admit ONLY those files,not containers,links,reviews or aliases. No permission propagates;protected bodies AND metadata stay PRIVATE/local under original rights.
At most ONE correctly pruned optional ORIGINAL-history traversal. Apply EVERY inherited wildcard/substring to full-project-relative POSIX path.casefold() BEFORE descent,eligibility and body at EVERY depth. Query authored coboundary,cofilling,local-system and congruence-cover mechanisms. No projectwide-then-filter,ancestor inventory,copied corpus,role/helper derivatives,size cutoff,oldscan replay or live peer/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record extents,recovery,late reads,omissions,false admissions. If unused,say so. No exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted unique safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Read-only thereafter;edit NO sealed file. Tiny controls suffice;artifact checks are not mathematical gates.

'''
text=prefix+instructions+recent+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162cp* *arithmetic*r162cp*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode()
assert len(brief.decode())<120000,len(brief.decode())
assert 'come back to STANDARD speed' in brief.decode() and {'*arithmetic*162cp*','*arithmetic*r162cp*'}<=rules(brief.decode())
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=177,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=10,canonical_entries=15,canonical_text_objects=9,canonical_text_bytes=52577,compiled_pdfs=1,new_family_screens=1,body178_not_decoded=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,prior_related_scope_preserved='Structural170',completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=1,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes());print(json.dumps(prep))
