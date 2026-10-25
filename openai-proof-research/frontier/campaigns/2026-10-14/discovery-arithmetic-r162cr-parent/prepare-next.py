from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cs-parent';R=B/'fresh-arithmetic-discovery-r162cs';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cs-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
for p in [N,R,BP]:assert not p.exists(),p
a=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cr-brief.txt').read_bytes();assert sha(a)=='d83ad2e2895fc2cb52399c16de04d34731280a4d1102feedbec18f47f1983858'
s=a.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=s.split(marker,1)[1];assert len(standing.encode())==5570
prefix="""Arithmetic r162cs:paired-state Hamiltonian-cycle discovery. Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cs/ (exists empty),including all scratch/downloads/copies. EVERY shell workdir /home/mj-kang/Documents/Dev/math/openai-proof-research.
Codex/GPT-6 Astra/high/default;STANDARD speed;19/20 latestR041 overrides obsolete Factory/18 lines. Parent alone assigns grades/count. No nested agents,git/shared edits,heavy installs,unbounded jobs,publication/uploads/contacts/browser UI or downstream work. Source operative truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated;no audit.
Read AGENTS/upstream/full standing brief. Journal ONLY binary[4801,6347),no whole hash/decode. Use complete preprints-tree metadata,ignore truncated tree.json. Own I/O and FIVE exact exceptions ONLY override exclusions. Parent prechecked namespaces,not live peers;no exhaustive-clearance claim.

"""
intro='''Read COMPLETE Source180/all includes and strongest actual primary proofs. Full Barnette/Pfaffian Hamiltonian conclusions and stronger constructive/state/extraction operations are PAID. Keep original graph,hypotheses,marked data and complexity costs. Source truth stipulated.
R162CR:PREFREEZE/no nominee. Uniform epsilon n^(1/4) Fourier-modulus deviation for all binary rows,n>4 remains unproved/unfrozen. Exact Fourier/first-order reductions paid;common integrality/units/norms missing. Examples reject shortcuts only.
Structural167 unchanged:determinant/extraction paid,2^m evaluations remain;polynomial filtering unproved. Prism refutes unfiltered shortcut only;no retry.

'''
recent=s[s.index('R162CQ remains'):s.index('R162BJ remains archived')];older=s[s.index('R162BJ remains archived'):s.index('Catalogue:ONLY')];hist=s[s.index('R162W is CLOSED'):s.index('Prospective isolation BEFORE')];iso=s[s.index('Prospective isolation BEFORE'):s.index(marker)]
sel=json.loads((D/'private/intake/Source180-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[282674,283416]
bs=[e for e in sel['entries'] if e['type']=='blob'];ts=[e for e in bs if not e['path'].endswith('.pdf')];assert len(bs)==5 and len(ts)==4 and sum(e['size'] for e in ts)==45063
prior=B/'fresh-arithmetic-discovery-r162cr';paths=[D/'assessment.md',prior/'private/COMPARISON.md',prior/'WORKLOG.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in paths:
 b=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(b),sha256=sha(b),mode=p.stat().st_mode))
e=next(e for e in ts if e['path'].endswith('/paper.tex'))
section='''Catalogue ONLY binary[282674,283416) in sources/CONTENTS.md,Source180. Parent one14000-byte window[282674,296674):180/181titles and ONLY180body decoded;181body unread,thirdheadingboundaryonly. No extra screen/locator or whole-catalogue read.
Canonical folder/ACTUAL body:
'''+sel['folders'][0]+'\n'+e['path']+';bytes'+str(e['size'])+';Git'+e['sha']+'''.
5blobs7entries,4texts45063bytes,onePDF. Read all4texts (paper,figure,bibliography,README);main.tex is NOT the wrapper. Parent operative reading:NONE.
FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
Exceptions admit ONLY those files,not containers,links,reviews or aliases. No permission propagates;protected bodies AND metadata remain PRIVATE/local under original rights.
At most ONE optional ORIGINAL-history traversal under the COMPLETE isolation rules below. Apply all guards before descent/eligibility/body. Read eligible paired-state/Pfaffian hits through equal/higher headings;record extents,recoveries,late reads,omissions,false admissions. If unused,say so;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight of sorted safe exact membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Read-only afterward. Tiny controls suffice;artifact checks are not mathematical gates.

'''
text=prefix+intro+recent+older+section+hist+iso+'\nNew literal guards:\n*arithmetic*162cs* *arithmetic*r162cs*\n';missing=rules(s)-rules(text)
if missing:text+='\nOther inherited exclusions:\n'+' '.join(sorted(missing))+'\n'
data=(text+marker+standing).encode();assert rules(s)<=rules(data.decode()) and data.split(marker.encode(),1)[1]==standing.encode();assert len(data.decode())<120000,len(data.decode())
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads'];N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(data);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes())
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(data),characters=len(data.decode()),sha256=sha(data),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=180,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=5,canonical_entries=7,canonical_text_objects=4,canonical_text_bytes=45063,compiled_pdfs=1,new_family_screens=1,body181_not_decoded=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,prior_related_scope_preserved='Structural167',completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=2,shortening_preserved_all_scopes_and_guards=True);dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
