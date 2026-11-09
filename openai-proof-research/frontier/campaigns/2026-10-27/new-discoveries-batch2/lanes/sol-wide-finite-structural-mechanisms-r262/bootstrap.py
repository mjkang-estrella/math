import pathlib,hashlib,json,shutil
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
L=B/'lanes/sol-wide-finite-structural-mechanisms-r262'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'admin'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 records.append(dict(original=str(p),copy=str(q),sha256=h(q),kind='administrative snapshot'))
for lane in ['sol-wide-finite-arithmetic-mechanisms-r260','sol-wide-finite-mechanism-scout-r258']:
 for name in ['SCOUTING.md','SUMMARY.md']:
  p=B/'lanes'/lane/name;q=L/'frozen'/lane/name;q.parent.mkdir(parents=True,exist_ok=True)
  before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q)
  records.append(dict(original=str(p),copy=str(q),sha256=before,kind='scientific frozen'))
(L/'provenance.json').write_text(json.dumps(records,indent=2))
for r in records:
 if r['kind']=='scientific frozen':print('\nFILE',r['copy'],'\n',pathlib.Path(r['copy']).read_text())
