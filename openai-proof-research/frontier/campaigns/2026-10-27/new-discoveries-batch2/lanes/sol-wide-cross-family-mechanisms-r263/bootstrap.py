import pathlib,hashlib,json,shutil
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'); L=B/'lanes/sol-wide-cross-family-mechanisms-r263'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'admin'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);records.append(dict(original=str(p),copy=str(q),sha256=h(q),kind='administrative snapshot'))
for name in ['SUMMARY.md','SCOUTING.md','history-bindings.json','slice.json','explore.py']:
 p=B/'lanes/sol-wide-finite-structural-mechanisms-r262'/name;q=L/'frozen'/name;q.parent.mkdir(parents=True,exist_ok=True);before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q);records.append(dict(original=str(p),copy=str(q),sha256=before,kind='scientific frozen'))
(L/'provenance.json').write_text(json.dumps(records,indent=2))
for name in ['SUMMARY.md','SCOUTING.md','explore.py']:
 print('\nFILE',name,'\n',(L/'frozen'/name).read_text())
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'admin'/name).read_text());print('ADMIN',name,'keys',list(d));print(json.dumps(d.get('accepted',d.get('published_papers',[])))[:12000])
