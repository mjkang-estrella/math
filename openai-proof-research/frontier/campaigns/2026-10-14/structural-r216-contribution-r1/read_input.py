import sys,json,hashlib,fnmatch,re
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/structural-r216-contribution-r1'
A=json.loads((OWN/'packet/private/author-admissions.json').read_text())
AUTHOR=ROOT/A['root']; G=json.loads((OWN/'packet/private/guards.json').read_text())
def forbidden(rel):
 p=rel.casefold()
 return any(fnmatch.fnmatchcase(p,w) for w in G['wildcards']+G['derivatives']) or any(s in p for s in G['substrings'])
def read(path,start=1,stop=None):
 p=Path(path); p=ROOT/p if not p.is_absolute() else p
 rel=p.relative_to(ROOT).as_posix()
 allowed=any(p==AUTHOR/'packet'/x for x in A['packet']) or any(p==AUTHOR/x for x in A['outside']) or p.is_relative_to(OWN)
 if not allowed:raise ValueError('Not an exact admitted input')
 b=p.read_bytes(); lines=b.splitlines(keepends=True); stop=len(lines) if stop is None else stop
 assert 1<=start<=stop<=len(lines)
 selected=b''.join(lines[start-1:stop]); selected.decode()
 event={'path':rel,'line_start':start,'line_end_inclusive':stop,'byte_start':sum(map(len,lines[:start-1])),'byte_end':sum(map(len,lines[:stop])),'file_bytes':len(b),'file_sha256':hashlib.sha256(b).hexdigest(),'selection_sha256':hashlib.sha256(selected).hexdigest(),'semantic_display':True}
 with (OWN/'packet/private/semantic-reads.jsonl').open('a') as f:f.write(json.dumps(event)+'\n')
 print(json.dumps(event))
 for i,line in enumerate(lines[start-1:stop],start): print(f'{i:5d} '+line.decode().rstrip('\n'))
if __name__=='__main__':read(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 1,int(sys.argv[3]) if len(sys.argv)>3 else None)
