#!/usr/bin/env python3
import pathlib,json,hashlib,re,datetime,urllib.request,subprocess,sys,concurrent.futures
ROOT=pathlib.Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i07_structures_novelty_r3'; E=pathlib.Path(__file__).resolve().parent
OLD=ROOT/'frontier/sources/i07_structures'
def sha(b): return hashlib.sha256(b).hexdigest()
def write(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 pin=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
 inv=json.loads((ROOT/'sources/preprints-tree.json').read_text()); rows=inv['tree']; paths={x['path']:x for x in rows}; assert len(paths)==len(rows) and not inv['truncated']
 names=sorted({x['path'].split('/')[1] for x in rows if '/' in x['path']})
 pattern=r'aspher|manifold|duality|Nielsen|realiz|four-dim|tensor|homeom|group-action|finite-group|reflection|disk-embed'
 selected=[n for n in names if re.search(pattern,n,re.I)]
 write(S/'inventory-screen.json',{'entries':len(rows),'blobs':sum(x['type']=='blob' for x in rows),'manuscript_directories':len(names),'truncated':inv['truncated'],'all_manuscript_directories':names,'query':pattern,'matched_directories':selected,'matched_complete_path_inventory':[x for x in rows if '/' in x['path'] and x['path'].split('/')[1] in selected]})
 verified=[]
 for x in json.loads((OLD/'retrieval-manifest.json').read_text()):
  p=OLD/'upstream'/x['path']; b=p.read_bytes(); assert sha(b)==x['sha256'] and len(b)==x['bytes']; blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert blob==paths[x['path']]['sha']; assert '/'+pin+'/' in x['url']; verified.append({'path':str(p.relative_to(ROOT)),'upstream_path':x['path'],'sha256':sha(b),'git_blob':blob,'bytes':len(b),'url':x['url']})
 selected_dirs={x['upstream_path'].split('/')[1] for x in verified}
 expected={x['path'] for x in rows if x['type']=='blob' and '/' in x['path'] and x['path'].split('/')[1] in selected_dirs and x['path'].endswith(('.tex','.bib'))}
 assert expected=={x['upstream_path'] for x in verified}
 contracts=json.loads((OLD/'theorem-contracts.json').read_text())
 for x in contracts:
  p=OLD/'upstream'/x['path']; b=p.read_bytes(); assert sha(b)==x['source_sha256']; st='\n'.join(b.decode().splitlines()[x['start_line']-1:x['end_line']]); assert st==x['statement'] and sha(st.encode())==x['statement_sha256']
 write(S/'pinned-verification.json',{'pin':pin,'files_verified':len(verified),'contracts_verified':len(contracts),'files':verified})
 inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/iterations/i07-structures.md','frontier/reviews/i07-structures-r2.md','frontier/sources/i07_structures/theorem-contracts.json','frontier/iterations/i07-structures-r2-parent-verification.json','frontier/sources/i07_structures/literature/manifest.json']
 write(S/'input-hashes.json',[{'path':p,'bytes':len((ROOT/p).read_bytes()),'sha256':sha((ROOT/p).read_bytes())} for p in inputs])
 retained=[]
 for x in json.loads((OLD/'literature/manifest.json').read_text()):
  p=ROOT/x['file']; b=p.read_bytes(); assert sha(b)==x['sha256']; t=p.with_suffix('.txt'); assert sha(t.read_bytes())==x['text_sha256']; retained.append({**x,'verified_pdf':True,'verified_text':True,'reuse_without_network_refetch':True})
 write(S/'retained-literature-verification.json',retained)
 print('Verified',len(verified),'pinned files,',len(contracts),'contracts,',len(retained),'retained literature pairs; screened',len(names),'directories.')
 if '--download' in sys.argv:
  sources={'zaslavsky-balance':'https://people.math.binghamton.edu/zaslav/Tpapers/npc.pdf','davis-book':'https://people.math.osu.edu/davis.12/davisbook.pdf','davis-leary':'https://people.math.osu.edu/davis.12/examples.pdf','davis-lueck':'https://jfdavis.pages.iu.edu/papers/dl5.pdf','hilman-kirstein-kremer':'https://arxiv.org/pdf/2409.02220','avramidi-okun-schreve':'https://arxiv.org/pdf/2301.06112','elementary-amenable-four':'https://arxiv.org/pdf/2501.12512'}
  def get(item):
   name,url=item; p=S/'literature'/f'{name}.pdf'
   try:
    req=urllib.request.Request(url,headers={'User-Agent':'research audit'})
    with urllib.request.urlopen(req,timeout=60) as r: b=r.read(); final=r.url
    assert b.startswith(b'%PDF'); p.write_bytes(b); subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
    return {'name':name,'url':url,'final_url':final,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(p.relative_to(ROOT)),'sha256':sha(b),'bytes':len(b),'text_sha256':sha(p.with_suffix('.txt').read_bytes())}
   except Exception as ex: return {'name':name,'url':url,'error':str(ex)}
  with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: results=list(pool.map(get,sources.items()))
  write(S/'literature/manifest.json',results); print(json.dumps(results,indent=2))
if __name__=='__main__': main()
