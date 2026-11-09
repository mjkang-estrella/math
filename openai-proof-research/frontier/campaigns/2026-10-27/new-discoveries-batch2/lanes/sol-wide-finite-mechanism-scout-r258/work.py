from pathlib import Path
import sys,json,hashlib,shutil,datetime,urllib.request,urllib.error,subprocess
ROOT=Path('/home/mj-kang/Documents/Dev/math')
B=ROOT/'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'
L=B/'lanes/sol-wide-finite-mechanism-scout-r258'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(rel,admin=False):
 p=ROOT/rel; d=L/('administrative' if admin else 'frozen')/rel
 d.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p)
 if not d.exists(): shutil.copyfile(p,d)
 assert sha(p)==h==sha(d)
 rec={'original':str(p),'copy':str(d),'sha256':h,'administrative':admin,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return d
if sys.argv[1]=='init':
 for r in ['openai-proof-research/AGENTS.md',str((B/'AGENTS.md').relative_to(ROOT)),str((B/'ledger.json').relative_to(ROOT)),str((B/'prior-campaign-context.json').relative_to(ROOT))]:freeze(r,True)
 for r in ['openai-proof-research/sources/upstream.json','openai-proof-research/sources/CONTENTS.md','openai-proof-research/frontier/scouts/discrete.md','openai-proof-research/frontier/scouts/arithmetic.md']:
  p=freeze(r); print('\nFILE',r,'\n',p.read_text()[:24000])
 for name in ['ledger.json','prior-campaign-context.json']:
  j=json.loads((L/'administrative'/B.relative_to(ROOT)/name).read_text());print(name,json.dumps(j)[:60000])
elif sys.argv[1]=='read':
 p=freeze(sys.argv[2]);s=p.read_text(errors='replace');a=int(sys.argv[3]) if len(sys.argv)>3 else 0;n=int(sys.argv[4]) if len(sys.argv)>4 else 25000;print(s[a:a+n])
elif sys.argv[1]=='run':exec(Path(sys.argv[2]).read_text())
