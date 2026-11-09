import pathlib,json,hashlib,re,subprocess
L=pathlib.Path(__file__).resolve().parents[1];C=L.parent;B=C.parent;rs=json.loads((L/'reservation.json').read_text())['rows']
inp=[L/'TASK.txt',C/'AGENTS.md',B/'AGENTS.md',B/'prior-campaign-context.json',C/'ledger.json',B/'ledger.json',L.parents[5]/'AGENTS.md']
out={str(p):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in inp if p.exists()}
(L/'input-audit.json').write_text(json.dumps(out,indent=2))
pat='|'.join(r'\b'+str(x['mathdb_id'])+r'\b' for x in rs)
p=subprocess.run(['rg','-n',pat,str(B),'-g','*.md','-g','results.json','-g','*ledger*.json','-g','!TASK.txt'],capture_output=True,text=True)
(L/'history-exact.txt').write_text('\n'.join(s for s in p.stdout.splitlines() if '/expanded-corpus-r249/' not in s))
pat='|'.join(re.escape(x['title']) for x in rs)
p=subprocess.run(['rg','-n','-i',pat,str(B),'-g','*.md'],capture_output=True,text=True)
(L/'history-titles.txt').write_text('\n'.join(s for s in p.stdout.splitlines() if '/expanded-corpus-r249/' not in s))
o={}
for p in (L/'text').glob('*.txt'):
 lines=p.read_text().splitlines();hits=[]
 for i,s in enumerate(lines):
  if re.search(r'Conjecture|[Cc]ounterexample|^Theorem|^Definition|^Example|Figure \d',s):hits.append({'line':i+1,'excerpt':'\n'.join(lines[max(0,i-1):i+6])})
 o[p.name]=hits
(L/'source-label-inventory.json').write_text(json.dumps(o,indent=2))
