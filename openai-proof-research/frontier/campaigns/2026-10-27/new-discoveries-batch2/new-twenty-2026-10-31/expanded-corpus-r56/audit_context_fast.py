from pathlib import Path
import json,hashlib,re,subprocess
w=Path(__file__).resolve().parent;root=Path('/home/mj-kang/Documents/Dev/math');camp=root/'openai-proof-research/frontier/campaigns';e=json.loads((w/'extracted.json').read_text());hits={i:[] for i in e}
# Bounded report-file search: excludes inventory/raw/index-only JSON; log every matching report context.
for f in camp.rglob('*'):
 if not f.is_file() or w in f.parents or f.suffix not in ['.md','.json']:continue
 if any(s in f.parts for s in ['corpus','.lake','node_modules']):continue
 if f.suffix=='.json' and not any(t in f.name.lower() for t in ['results','review','ledger','context','disposition','summary']):continue
 if f.stat().st_size>8000000:continue
 try:s=f.read_text()
 except (UnicodeError,OSError):continue
 pattern=r'(?<![0-9a-f])(?:'+ '|'.join(e)+r')(?![0-9a-f])|'+ '|'.join(re.escape(v['record']['title']) for v in e.values())
 for m in re.finditer(pattern,s,re.I):
  token=m.group();i=token if token in e else next(i for i,v in e.items() if v['record']['title'].lower()==token.lower())
  if len(hits[i])<150:hits[i].append(dict(path=str(f),line=s[:m.start()].count('\n')+1,context=s[max(0,m.start()-110):m.end()+180]))
(w/'history-matches.json').write_text(json.dumps(hits,indent=2,ensure_ascii=False)); print({i:len(v) for i,v in hits.items()})
context=[]
for f in [root/'openai-proof-research/AGENTS.md',w.parent/'AGENTS.md',w.parent.parent/'AGENTS.md',w.parent/'ledger.json',w.parent.parent/'ledger.json',w.parent.parent/'prior-campaign-context.json']:
 b=f.read_bytes();context.append(dict(path=str(f),sha256=hashlib.sha256(b).hexdigest()))
(w/'context-hashes.json').write_text(json.dumps(context,indent=2));print('all context read in script; inherited accepted/excluded summary retained by reference, not copied')
