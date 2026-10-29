import json,re,gzip,hashlib
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
hits=json.loads((L/'history-matches.json').read_text()); receipts=[];hs={x['sha256'] for x in hits}
strict=re.compile(rb'2311[.]08985|(?<![0-9])2344638(?![0-9])|post[ -]?Lie|post.Lie|Monadjem|Burde.{0,40}Dekimpe|2507[.]06214|2026[.]01[.]048|2602[.]00614',re.I)
for j in hits:
 p=R/j['path'];b=p.read_bytes();ms=list(strict.finditer(b))
 excerpts=[b[max(0,m.start()-90):m.end()+120].decode(errors='replace') for m in ms]
 receipts.append(dict(path=j['path'],original_hash=j['sha256'],reopened_hash=sha(b),unchanged=sha(b)==j['sha256'],strict_matches=len(ms),all_matching_excerpts=excerpts,role='registry tree or copied registry excerpt' if 'tree' in p.name or p.name.startswith('history-body') or p.name in {'omega-D5.json'} else 'original text/code'))
dump('original-reopen-receipts.json',receipts)
with gzip.open(L/'matching-aliases.jsonl.gz','wt') as out:
 with gzip.open(L/'history-aliases.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line)
   if h in hs:out.write(line)
retained={}
with gzip.open(L/'history-aliases.jsonl.gz','rt') as f:
 for line in f:
  h,p=json.loads(line)
  if re.search(r'r11[123]/.*(?:SUMMARY|discovery|PROOF|review|DECISION)',p,re.I):retained[p]=h
dump('retained-r111-r113-science.json',retained)
delta=json.loads((L/'sources/omega-compare.json').read_text());head=json.loads((L/'sources/omega-head.json').read_text());op=json.loads((L/'sources/openai-head.json').read_text())
dump('registry-delta-receipt.json',dict(head=head['sha'],observed_http='http.jsonl',openai_head=op['sha'],status=delta['status'],base=delta['base_commit']['sha'],merge_base=delta['merge_base_commit']['sha'],ahead_by=delta['ahead_by'],returned_commits=len(delta['commits']),returned_files=len(delta['files']),cap_warning=len(delta['files'])>=300 or len(delta['commits'])>=250,paths=[x['filename'] for x in delta['files']],semantic_clearance=False))
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,s):
  if s.strip():self.out.append(s.strip())
p=Text();p.feed((L/'sources/published.html').read_text());(L/'sources/published.txt').write_text('\n'.join(p.out))
print('reopened',len(receipts),'strict-hit bodies',sum(x['strict_matches']>0 for x in receipts),'r111-r113 retained',len(retained))
print('registry',head['sha'],delta['ahead_by'],len(delta['files']))
