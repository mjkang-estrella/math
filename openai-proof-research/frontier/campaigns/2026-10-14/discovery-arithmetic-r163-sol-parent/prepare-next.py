from pathlib import Path
import json,hashlib,re,fnmatch,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r164-sol-parent';R=B/'fresh-arithmetic-discovery-r164-sol';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r164-sol-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
for p in [N,R,BP]:assert not p.exists(),p
t=json.loads((B/'tasks.json').read_bytes());assert len(t['tasks'])==862 and t['newAccepted']==19 and t['latestAcceptance']=='R041'
checks=[];names=[p.relative_to(P).as_posix() for p in [N,R,BP]]
for i,x in enumerate(t['tasks']):
 if x.get('status') not in {'running','queued','waiting'} or not x.get('brief'):continue
 a=(P/x['brief']).read_bytes();assert sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values()),(i,matches)
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
old=(B/'expanded-target-2026-10-17/fresh-arithmetic-r163-sol-brief.txt').read_bytes();assert sha(old)=='2360a101b3b97372cb68f9cdbb40329b1e940cf3560592b53c24314bf3e7400b'
s=old.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=s.split(marker,1)[1];assert len(standing.encode())==5570
prefix="Arithmetic164Sol:forbidden-subgraph correspondence-coloring discovery. Codex/GPT-6.1-Sol/high/ultrafast per latest user instruction,overriding older model/tier preferences.19/20,R041;parent alone grades/counts. No nested agents.\nWrite ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r164-sol/ (exists empty),including scratch/downloads/copies. EVERY shell workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. No git/shared edits,heavy installs,unbounded jobs,publication/uploads/contacts/browser UI or downstream work.\nRead AGENTS/upstream/full standing brief. Source truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated;no audit. Journal ONLY binary[4801,6347),no whole hash/decode. Complete preprints-tree. Own I/O and FIVE exact completed exceptions ONLY override exclusions.\nRead COMPLETE Source184's BOTH proofs/includes and actual primaries. Full forbidden-clique/subgraph correspondence-coloring and average-degree independence bounds and stronger source/primary operations PAID. Preserve original graph,cover,hypotheses,uniformity,costs;find a distinct nonroutine full-scope operation.\nR163-Sol:PREFREEZE/no nominee. Uniform1+C m(r+1)^(1/3-delta) cardinality for parametric minimum spanning forests on ALL labelled multigraphs,arbitrary affine real weights,all parameters/fixed ties unproved/unfrozen. Token chains/common active-minor reduction paid;graphic exchange/activity and rank-sensitive assembly unpaid. Cactus rejects shortcut,not full question.\nR162CU:CLOSED PREFREEZE/no nominee. Degree-only original-prime normalization and polynomial-density supersaturation with one nonincreasing cutoff per branch close as source comparisons. Counting cutoff is NOT an unpaid gap. Primary square-spectrum theorem rejects stronger nonnegative-witness shortcut,not source/counting. No grade/count.\nR162BX:uniform linear-cost small-set deletion on one original correspondence cover unresolved/unfrozen. Fixed-order deletion failure is not a full bound counterexample. Preserve scope;no retry.\n"
recent=s[s.index('R162CT:PREFREEZE'):s.index('Catalogue ONLY')];hist=s[s.index('R162W is CLOSED'):s.index('Prospective isolation BEFORE')];iso=s[s.index('Prospective isolation BEFORE'):s.index(marker)]
sel=json.loads((D/'private/intake/Source184-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[288176,290060]
bs=[x for x in sel['entries'] if x['type']=='blob'];ts=[x for x in bs if not x['path'].endswith('.pdf')];assert len(bs)==24 and len(ts)==22 and sum(x['size'] for x in ts)==164770
prior=B/'fresh-arithmetic-discovery-r163-sol';paths=[D/'assessment.md',prior/'private/COMPARISON.md',prior/'WORKLOG.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in paths:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
wrappers=[e for e in ts if e['path'].endswith('/build/main.tex')];assert len(wrappers)==2
section='''Catalogue ONLY binary[288176,290060),Source184. Parent ONE14000-byte window[288176,302176):184/185titles and ONLY184body decoded;185body unread,thirdheadingboundaryonly. No other catalogue read.
Wrapper:
'''+ '\n'.join(e['path'] for e in wrappers)+'''
24blobs32entries,22texts164770bytes,twoPDFs. Read ALL texts/includes;parent operative reading:NONE.
FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)+'''
ONLY these files,not containers,links,reviews or aliases. Protected bodies AND metadata PRIVATE/local under original rights.
At most ONE optional ORIGINAL-history traversal,COMPLETE guards below before descent/eligibility/body;eligible correspondence-coloring/clique-independence hits through equal/higher headings. Record limits;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Then read-only. Tiny controls;no mathematical gates.
'''
text=prefix+recent+section+hist+iso+'\nNew literal guards:\n*arithmetic*163-sol* *arithmetic*r164-sol*\n'
missing=rules(s)-rules(text)
if missing:text+='Other inherited exclusions:\n'+' '.join(sorted(missing))+'\n'
removed_headings=text.count('Additional prospective literal wildcard twins:');text=text.replace('Additional prospective literal wildcard twins:\n','');text=re.sub(r'\n{2,}','\n',text);data=(text+marker+standing).encode();assert rules(s)<=rules(data.decode()) and len(data.decode())<120000,len(data.decode());assert data.split(marker.encode(),1)[1]==standing.encode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
guard=dict(before_creation=True,before_semantic_reads=True,namespaces=names,checks=checks,foreign_live_queries=False,original_namespace_guards_checked=True)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(data);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes())
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(data),characters=len(data.decode()),sha256=sha(data),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,source=184,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=24,canonical_entries=32,canonical_text_objects=22,canonical_text_bytes=164770,compiled_pdfs=2,body185_not_decoded=True,parent_source_body_read=False,completed_direct_inputs=5,model='gpt-6.1-sol',reasoningEffort='high',serviceTier='ultrafast',parallel_authorization='Latest user:Sol high ultrafast; one task per named model',redundant_admin_headings_removed=removed_headings,publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
