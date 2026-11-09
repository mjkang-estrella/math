from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
R=L.parents[6]
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
def freeze(p,name,admin=False):
 q=L/('administrative' if admin else 'frozen')/name
 q.parent.mkdir(parents=True,exist_ok=True)
 before=h(p);shutil.copyfile(p,q);assert before==h(q)==h(p)
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before,administrative=admin))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:freeze(B/name,name,True)
P=L.parent/'sol-wide-analysis-scout-r221'
for name in ['SCOUTING.md','SOURCE_MAP.md','history-screen.json','provenance.json']:freeze(P/name,'r221--'+name)
for name in ['1911.08613v2.pdf','1911.08613v2.txt','pinned-CONTENTS.md','pinned-upstream.json','pinned-preprints-tree.json']:freeze(P/'sources'/name,name)
(L/'freeze.json').write_text(json.dumps(records,indent=2))
print('Frozen',len(records),'files')
