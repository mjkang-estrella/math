import pathlib,json,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent;ids=json.loads((D/'reservation.json').read_text())['ids'];pat=r'\b('+'|'.join(map(str,ids))+r')\b'
p=subprocess.run(['rg','-n',pat,str(B),'-g','*.md','-g','*results*.json','-g','*review*.json','-g','*ledger*.json'],capture_output=True,text=True)
ls=[l for l in p.stdout.splitlines() if '/expanded-corpus-r98/' not in l and len(l)<5000];(D/'outputs/history-exact.txt').write_text('\n'.join(ls)+'\n')
paths=[D/'TASK.txt',D/'reservation.json',D.parent/'AGENTS.md',B/'AGENTS.md',D.parents[5]/'AGENTS.md',D.parent/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json']
out={}
for f in paths:
 if f.exists():
  b=f.read_bytes();out[str(f)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
(D/'outputs/input-review-receipts.json').write_text(json.dumps(out,indent=2)+'\n');print('bounded historical exact-ID matches',len(ls))
