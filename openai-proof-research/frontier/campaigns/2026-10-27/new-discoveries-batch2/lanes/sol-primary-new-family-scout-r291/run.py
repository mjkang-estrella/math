import os,json,hashlib,pathlib,shutil,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,v): (L/n).write_text(json.dumps(v,indent=2)+'\n')
def main():
 (L/'administrative').mkdir(exist_ok=True)
 binds=[]
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md']:
  if p.exists():
   q=L/'administrative'/p.name; a=sha(p);shutil.copyfile(p,q);assert sha(q)==a==sha(p);binds.append({'original':str(p),'copy':str(q),'sha256':a})
 dump('administrative-bindings.json',binds)
 reports=[]
 for p in sorted((B/'lanes').glob('*/SCOUTING.md')):
  if p.parent==L:continue
  if p.stat().st_size>150000:continue
  reports.append({'path':str(p),'sha256':sha(p),'text':p.read_text(errors='replace')})
 dump('history-index.json',reports)
 inv=[]
 for root,ds,fs in os.walk(B/'lanes'):
  ds[:]=[d for d in ds if d not in ['administrative','admin','inputs','assigned','context','node_modules','build','frozen','snapshots']]
  for f in fs:
   if f.endswith(('.pdf','.txt','.tex','.html')):inv.append(str(pathlib.Path(root)/f))
 dump('source-inventory.json',inv)
 print('reports',len(reports),'source paths',len(inv))
 print('\n'.join(inv[-120:]))
if __name__=='__main__':main()
