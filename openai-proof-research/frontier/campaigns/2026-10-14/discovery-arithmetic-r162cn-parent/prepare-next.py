"""Prepare Source176, a new canonical manuscript adjacent to Source175."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162co-parent';R=B/'fresh-arithmetic-discovery-r162co';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162co-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads']
for p in [N,R,BP]:assert not p.exists(),p
a=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cn-brief.txt').read_bytes();assert sha(a)=='64ff5cc0343890e13fd85bd5f3a49369ceaabbecbd809ccb300fbcef0bf978c7'
old=a.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read all THREE COMPLETE Source175')].replace('Arithmetic discovery r162cn — confirmed expectation-threshold and graph-decomposition discovery.','Arithmetic discovery r162co — confirmed edge-count Kahn–Kalai operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162cn/','fresh-arithmetic-discovery-r162co/',1).replace('This is a FRESH DISTINCT Source175 family in a new author conversation,not another continuation or renaming of the entropy-overlap target.','This is a NEW Source176 canonical-manuscript round adjacent to archived Source175,not a renamed continuation of its fixed-two-piece target.',1).replace('Own r162cn I/O','Own r162co I/O',1)
instructions='''Read the COMPLETE Source176 proof,all includes and strongest relevant primary/companion proofs before selecting a new full theorem. The all-simple-graph bound pc(H;n)<=C p_E(H;n)(1+log_2 h),h>=1,is ALREADY PAID. Read actual stronger operations,not just this headline. Source truth stipulated;no audit. Preserve the same graph,host n,edge count h,expected-copy threshold definition,budget and embedding convention across every step. Charge weights,numerics and all costs when relevant.

R162CN is CLOSED PREFREEZE/no nominee. For every simple H on at most n vertices,the possibility of ONE fixed complementary two-piece partition with both ordinary thresholds O(q(H;n)) remains unproved/unfrozen;separate embeddings allowed. Source generic two-threshold comparison,full product-row coupling,adaptive partition and exact type-mass/capacity/tensor consequences are paid. Common typicality over all threshold-hard subgraphs is sufficient and unproved,not necessary. Cycle regrouping counterexample rejects only merging;the cycle admits good path pieces. The p_E side exploration was not selected/frozen. This adjacent manuscript does NOT authorize relabelling that target or retrying a desired grade. Parent alone assigns reviews/gates/count.

'''
recent=old[old.index('R162CM is CLOSED'):old.index('R162BJ remains archived')]
older=old[old.index('R162BJ remains archived'):old.index('Catalogue if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source176-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[278505,279582] and len(sel['folders'])==1
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')];assert len(blobs)==9 and len(texts)==8 and sum(e['size'] for e in texts)==39021
prior=B/'fresh-arithmetic-discovery-r162cn';direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 b=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(b),sha256=sha(b),mode=p.stat().st_mode))
e=next(e for e in texts if e['path'].endswith('/main.tex'))
section='''Catalogue if needed:ONLY binary sources/CONTENTS.md[278505,279582),EXACT Source176. Parent used ONE14000-byte window[278505,292505),decoded176/177titles and ONLY176body;177body unread,thirdheading boundaryonly. One family-body screen,no extra locator/screen,whole catalogue,ancestor inventory or oldscan replay.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''+sel['folders'][0]+'\n'+e['path']+';bytes'+str(e['size'])+';Git blob'+e['sha']+'''.
Exactly9blobs14entriesincludingroot,8nonPDFtexts39021bytes,onecompiledPDF. Read all8texts,all mathematical includes,figures,macros,references and README. Authenticate all9blobs;metadata is not proof reading. Parent Source176 operative reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
Exceptions admit ONLY these files,not containers,linked bodies,other reviews or aliases. No permission propagates. Protected bodies AND metadata remain PRIVATE/local under original rights.

At most ONE correctly pruned optional ORIGINAL-history traversal. Apply EVERY inherited wildcard/substring to full-project-relative POSIX path.casefold() BEFORE descent,eligibility and body access at EVERY depth. Query authored Kahn–Kalai,expectation-threshold,copy-multiplicity,extension/packing mechanisms. No projectwide-then-filter,ancestor inventory,copied corpus,role/helper derivatives,size cutoff after eligibility,oldscan replay or live peer/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record extents,recovery,late reads,omissions,false admissions. If unused,say so. No exhaustive-clearance/priority claim.

Seal once after SAME-logic preflight:sorted unique safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Read-only thereafter;edit NO sealed file. Tiny controls suffice;artifact checks are not mathematical gates.

'''
text=prefix+instructions+recent+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162co* *arithmetic*r162co*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode()
assert len(brief.decode())<120000,len(brief.decode())
assert 'come back to STANDARD speed' in brief.decode() and {'*arithmetic*162co*','*arithmetic*r162co*'}<=rules(brief.decode())
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=176,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=9,canonical_entries=14,canonical_text_objects=8,canonical_text_bytes=39021,compiled_pdfs=1,new_family_screens=1,body177_not_decoded=True,distinct_canonical_manuscript=True,adjacent_to_previous_mathematical_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=0,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes());print(json.dumps(prep))
