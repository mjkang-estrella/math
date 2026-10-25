from pathlib import Path
import fnmatch, hashlib, json, re, stat, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'fresh-arithmetic-discovery-r162co';N=B/'discovery-arithmetic-r162cp-parent';NR=B/'fresh-arithmetic-discovery-r162cp';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cp-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
h=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
t=json.loads((B/'tasks.json').read_bytes());assert len(t['tasks'])==853 and t['newAccepted']==19 and t['latestAcceptance']=='R041' and t['gpt_subagent_preferences']['serviceTier']=='default'
assert t['tasks'][852]['clientRequestId']=='twenty-20261025-fresh-arithmetic-r162co-codex-astra-r1'
names=[p.relative_to(P).as_posix() for p in [N,NR,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==852 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 rules={z for z in re.findall(r'\*[^\s,;()]*\*',a.decode()) if z not in {'*','**'}}
 matches={n:sorted(z for z in rules if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
for p in [N,NR,BP]:assert not p.exists(),p
private=D/'private/intake';private.mkdir(parents=True,exist_ok=False,mode=0o700)
snap={}
for p in R.rglob('*'):
 s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
 if stat.S_ISREG(s.st_mode):
  a=p.read_bytes();snap[p.relative_to(R).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
 else:assert stat.S_ISDIR(s.st_mode)
dump(private/'root-before.json',snap)
working=(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes();head=subprocess.check_output(['git','show',h+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
(private/'working-journal-before.bin').write_bytes(working);(private/'head-journal-before.bin').write_bytes(head);(private/'working-tasks-before.json').write_bytes((B/'tasks.json').read_bytes())
protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
for n,v in protected.items():assert sha((P/n).read_bytes())==v
dump(D/'intake-baseline.json',dict(head=h,own_task=852,task_count=len(t['tasks']),working_journal_equal_head=working==head,foreign_journal_edit_preserved=working!=head,journal_head_sha256=sha(head),journal_work_sha256=sha(working),protected=protected))
dump(D/'intake-prospective-isolation.json',dict(head=h,before_creation=True,before_semantic_reads=True,namespaces=names,checks=checks,legacy=legacy,foreign_live_queries=False))
print(json.dumps(dict(head=h,files_snapshotted=len(snap),checks=len(checks),legacy=legacy,next_namespaces=names,count=19)))
