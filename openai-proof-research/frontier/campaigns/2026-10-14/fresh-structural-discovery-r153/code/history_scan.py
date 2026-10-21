# Original r153 code, MIT. Run only from actual project root. Writes only own root.
import os,re,json,hashlib,sys
from pathlib import Path
ROOT=Path.cwd()
assert str(ROOT)=='/home/mj-kang/Documents/Dev/math/openai-proof-research'
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r153'
rounds={'arithmetic':[118,119,117,116,115,114,113,112,111,110,109,108,107], 'analytic':[147,148,146,145,144,143,142,141,140,139,138,137,136,135], 'structural':[152,151,150,149,148,147,146,145,144,143]}
tokens='corpus source primary history-derivative search inventory fixture control extract render vendor build copy frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature .venv venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence seal history ledger helper readme snapshot retention capture'.split()
extra=['t360s147','h138-','t185r144-','t177c143-','t373e135-','k369r134-','t088p133-']
patterns=[re.compile(r'.*'+k+r'.*r'+str(n)+r'.*',re.I) for k,ns in rounds.items() for n in ns]
query=re.compile(r'\b(?:sakoda|sipser|liveness|2nfa|2dfa|1nfa)\b|two[- ]way.{0,45}(?:automata|automaton|determin)|(?:automata|automaton).{0,45}(?:complement|alphabet)|(?:source|[it])\s*129\b',re.I)
mode=sys.argv[1] if len(sys.argv)>1 else 'initial'
assert mode in {'initial','probabilistic'}
if mode=='probabilistic':query=re.compile(r'\b(?:2pfa|1pfa|dwork|stockmeyer|yakaryilmaz|yakaryılmaz)\b|(?:probabilistic|restart|stochastic|first.exit).{0,50}(?:automata|automaton|diagram)|(?:automata|automaton|liveness).{0,50}(?:probabilistic|restart|stochastic)',re.I)
counts=dict(pruned=0,utf8=0,non_utf8=0,nul=0,symlinks=0,errors=0)
results=[];errors=[];eligible=[]
def blocked(name,path):
 s=name.lower()
 if 't360s147' in str(path.relative_to(ROOT)).lower():return True
 return path==OUT or s=='.git' or any(p.fullmatch(s) for p in patterns) or any(t in s for t in tokens+extra) or s in {'new-ten-2026-10-14.md','twenty-findings.md'} or s.startswith(('verify','validate','check_integrity'))
def walk(base):
 with os.scandir(base) as it:
  for ent in it:
   p=Path(ent.path)
   if blocked(ent.name,p):counts['pruned']+=1;continue
   if ent.is_symlink():counts['symlinks']+=1;continue
   if ent.is_dir(follow_symlinks=False):walk(p);continue
   if not ent.is_file(follow_symlinks=False):continue
   try:
    if 't360s147' in str(p.relative_to(ROOT)).lower():counts['pruned']+=1;continue
    b=p.read_bytes();s=b.decode('utf8')
   except UnicodeDecodeError:counts['non_utf8']+=1;continue
   except OSError as e:counts['errors']+=1;errors.append([str(p.relative_to(ROOT)),str(e)]);continue
   if '\x00' in s:counts['nul']+=1;continue
   counts['utf8']+=1
   rel=str(p.relative_to(ROOT));eligible.append(rel)
   matches=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if query.search(line)]
   if matches:results.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
walk(ROOT)
record={'counts':counts,'rounds':rounds,'tokens':tokens,'extra':extra,'query':query.pattern,'errors':errors,'eligible':eligible,'hits':results}
(OUT/('private/search/history-scan.json' if mode=='initial' else 'private/search/history-probabilistic.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(counts));print('Hit paths:')
for x in results:print(x['path'],len(x['matches']))
