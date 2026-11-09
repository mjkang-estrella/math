from pathlib import Path
import hashlib,json,sys,re
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-review-r1');D=L.parent/'expanded-corpus-r198'
if sys.argv[1]=='before':
 paths=set(json.loads((L/'extra-before.json').read_text()))
 paths.update(str(p) for p in [D/'raw/341850.json',D/'outputs/341850-v1.txt',D/'outputs/csp-eccc.txt'])
 paths.update(str(p) for p in D.glob('outputs/submod-values-*.json'))
 paths.update(line.split('  ',1)[1] for line in (L/'inputs-before.sha256').read_text().splitlines())
 paths={str(Path(p).resolve()) for p in paths if Path(p).is_file()}
 (L/'expanded-before.json').write_text(json.dumps({p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in sorted(paths)},indent=2))
else:
 before=json.loads((L/'expanded-before.json').read_text());after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before}
 initial=json.loads((L/'extra-before.json').read_text());assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in initial.items())
 for line in (L/'inputs-before.sha256').read_text().splitlines():
  h,p=line.split('  ',1);assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
 assert before==after
 (L/'expanded-after.json').write_text(json.dumps(after,indent=2));print('All',len(before),'inputs unchanged; original pre-review hashes also unchanged')
# Concise registry match report, avoid printing huge JSON lines.
if sys.argv[1]=='after':
 matches=[]
 for p in list((L/'downloads').glob('pool-file-*/body'))+[L/'downloads/pool-projects-correct/body']:
  for i,line in enumerate(p.read_text().splitlines(),1):
   if re.search(r'341850|1902\.04740|Brakensiek|submodular|monomial',line,re.I):matches.append({'file':str(p.relative_to(L)),'line':i,'excerpt':line[:350]})
 (L/'registry-matches.json').write_text(json.dumps(matches,indent=2));print('Registry keyword matches:',len(matches));print(json.dumps(matches[:8],indent=2))
 (L/'source-quote-extracted.txt').write_text('\n'.join((L/'arxiv-v1.txt').read_text().splitlines()[1333:1379]))
