from pathlib import Path
import json,hashlib,re,fnmatch,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r163-sol-parent';R=B/'fresh-arithmetic-discovery-r163-sol';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r163-sol-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
for p in [N,R,BP]:assert not p.exists(),p
t=json.loads((B/'tasks.json').read_bytes());assert len(t['tasks'])==861 and t['newAccepted']==19 and t['latestAcceptance']=='R041'
checks=[];names=[p.relative_to(P).as_posix() for p in [N,R,BP]]
for i,x in enumerate(t['tasks']):
 if x.get('status') not in {'running','queued','waiting'} or not x.get('brief'):continue
 a=(P/x['brief']).read_bytes();assert sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values()),(i,matches)
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
old=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cu-brief.txt').read_bytes();assert sha(old)=='048f551a1395048d473cd3d9aa1b0e38569521ed30538316bd1e8616414eaced'
s=old.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=s.split(marker,1)[1];assert len(standing.encode())==5570
prefix='''Parallel Arithmetic163Sol. Codex/GPT-6.1-Sol/high/ultrafast per latest user parallel instruction overrides prior model/tier ONLY here. One child/model;no nested agents.19/20,R041;parent alone grades/counts.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r163-sol/ (exists empty),including scratch/downloads/copies. EVERY shell workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. No git/shared edits,heavy installs,unbounded jobs,publication/uploads/contacts/browser UI or downstream work.
Read AGENTS/upstream/full standing brief. Source truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated;no audit. Journal ONLY binary[4801,6347),no whole hash/decode. Complete preprints-tree. Own I/O and FIVE exact completed exceptions ONLY override exclusions.
Read COMPLETE Source183/all includes and actual primary proofs. Full nonquantitative halving-line and all-k-set power savings and stronger source/primary operations are PAID. Preserve point sets,hypotheses,uniformity and costs;find a distinct nonroutine full-scope operation.
R162CU LIVE:exclude files,status,metadata,notes,aliases. Parent verified ORIGINAL guards cover this namespace;no exhaustive-clearance claim.
'''
recent=s[s.index('R162CT:PREFREEZE'):s.index('Catalogue ONLY')];hist=s[s.index('R162W is CLOSED'):s.index('Prospective isolation BEFORE')];iso=s[s.index('Prospective isolation BEFORE'):s.index(marker)]
sel=json.loads((D/'private/parallel-preparation/selection.json').read_bytes());nav=json.loads((D/'private/parallel-preparation/navigation.json').read_bytes());assert sel['catalogue_extent']==[287105,288176]
bs=[x for x in sel['entries'] if x['type']=='blob'];ts=[x for x in bs if not x['path'].endswith('.pdf')];assert len(bs)==12 and len(ts)==11 and sum(x['size'] for x in ts)==111708
prior=B/'fresh-arithmetic-discovery-r162ct';paths=[B/'discovery-arithmetic-r162ct-parent/assessment.md',prior/'private/COMPARISON.md',prior/'WORKLOG.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in paths:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
wrapper=next(e for e in ts if e['path'].endswith('/build/main.tex'))
section='''Catalogue ONLY binary[287105,288176),Source183. Parent ONE14000-byte window[287105,301105):183/184titles and ONLY183body decoded;184body unread,thirdheadingboundaryonly. No other catalogue read.
Wrapper:
'''+wrapper['path']+'''
12blobs15entries,11texts111708bytes,onePDF. Read ALL texts/includes;parent operative reading:NONE.
FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)+'''
ONLY these files,not containers,links,reviews or aliases. Protected bodies AND metadata PRIVATE/local under original rights.
At most ONE optional ORIGINAL-history traversal,COMPLETE guards below before descent/eligibility/body;eligible halving-line/k-set hits through equal/higher headings. Record limits;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Then read-only. Tiny controls;no mathematical gates.
'''
text=prefix+recent+section+hist+iso+'\nNew literal guards:\n*arithmetic*163-sol* *arithmetic*r163-sol*\n'
missing=rules(s)-rules(text)
if missing:text+='Other inherited exclusions:\n'+' '.join(sorted(missing))+'\n'
text=re.sub(r'\n{2,}','\n',text);data=(text+marker+standing).encode();assert rules(s)<=rules(data.decode()) and len(data.decode())<120000,len(data.decode());assert data.split(marker.encode(),1)[1]==standing.encode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
guard=dict(before_creation=True,before_semantic_reads=True,namespaces=names,checks=checks,foreign_live_queries=False,existing_cu_original_guards_already_cover_sibling=True)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(data);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes())
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(data),characters=len(data.decode()),sha256=sha(data),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,source=183,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=12,canonical_entries=15,canonical_text_objects=11,canonical_text_bytes=111708,compiled_pdfs=1,body184_not_decoded=True,parent_source_body_read=False,completed_direct_inputs=5,model='gpt-6.1-sol',reasoningEffort='high',serviceTier='ultrafast',parallel_authorization='Latest user instruction; one task per named model',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
