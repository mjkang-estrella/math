#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Re-fetch exact pinned sources; compare blob IDs, hashes and saved primary PDFs."""
import hashlib, json, shutil, subprocess, urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(data):return hashlib.sha256(data).hexdigest()
def blob(data):return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
def fetch(url):
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-provenance/1.0'}),timeout=40) as r:return r.read(),r.geturl(),r.status

def main():
 manifest=json.loads((REPO/'frontier/sources/i21_signed_saxl_dominance/pinned-manifest.json').read_text())
 tree=json.loads((REPO/'sources/preprints-tree.json').read_text());idx={x['path']:x for x in tree['tree']}
 rows=[]
 def pinned(x):
  data,url,status=fetch(x['url']);assert sha(data)==x['sha256'];assert blob(data)==x['git_blob']==idx[x['path']]['sha']
  p=ROOT/'inputs/pinned'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
  return {'path':str(p.relative_to(ROOT)),'upstream_path':x['path'],'url':x['url'],'resolved_url':url,'http_status':status,'sha256':sha(data),'git_blob_sha1':blob(data),'tree_blob_matches':True,'previous_sha256_matches':True,'bytes':len(data)}
 with ThreadPoolExecutor(max_workers=6) as pool:rows=list(pool.map(pinned,manifest))
 for name in ['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/iterations/i21-signed-saxl-dominance.md']:
  p=ROOT/'inputs/context'/name;p.parent.mkdir(parents=True,exist_ok=True);data=(REPO/name).read_bytes();p.write_bytes(data)
  rows.append({'path':str(p.relative_to(ROOT)),'copied_from':name,'sha256':sha(data),'bytes':len(data),'authentication':'local context snapshot; not independently remotely authenticated'})
 for name,url in [('harman-ryba-2023','https://alco.centre-mersenne.org/item/10.5802/alco.267.pdf'),('ikenmeyer-2015','https://arxiv.org/pdf/1410.6549v2'),('bessenrodt-bowman-2023','https://arxiv.org/pdf/2202.03066v3'),('bbs-2021','https://eprints.whiterose.ac.uk/id/eprint/182698/1/btran70.pdf')]:
  p=ROOT/'inputs/primary'/(name+'.pdf');row={'path':str(p.relative_to(ROOT)),'url':url,'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
  try:
   data,resolved,status=fetch(url);row.update(resolved_url=resolved,http_status=status,remote_sha256=sha(data),remote_matches_saved=(data==p.read_bytes()))
   if data!=p.read_bytes():
    dest=p.with_name(name+'-retrieved.pdf');dest.write_bytes(data);row['retrieved_path']=str(dest.relative_to(ROOT))
  except Exception as e:row['retrieval_error']=str(e)
  rows.append(row)
 for name in ['LICENSE','LICENSE.md','LICENSE.txt']:
  url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{name}'
  try:
   data,resolved,status=fetch(url);p=ROOT/'inputs/pinned'/name;p.write_bytes(data);rows.append({'path':str(p.relative_to(ROOT)),'url':url,'sha256':sha(data),'git_blob_sha1':blob(data),'bytes':len(data),'http_status':status});break
  except Exception as e:rows.append({'license_probe':url,'error':str(e)})
 for name in ['README.md','NOTICE']:
  url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{name}'
  try:
   data,resolved,status=fetch(url);p=ROOT/'inputs/pinned'/name;p.write_bytes(data)
   rows.append({'path':str(p.relative_to(ROOT)),'url':url,'sha256':sha(data),'bytes':len(data),'http_status':status})
  except Exception as e:rows.append({'probe':url,'error':str(e)})
 for pdf in sorted((ROOT/'inputs/primary').glob('*.pdf')):
  txt=pdf.with_suffix('.txt');cmd=['pdftotext','-layout',str(pdf),'-']
  result=subprocess.run(cmd,capture_output=True,check=True)
  rows.append({'path':str(txt.relative_to(ROOT)),'derived_from':str(pdf.relative_to(ROOT)),
   'extraction_command':cmd,'sha256':sha(txt.read_bytes()),'bytes':txt.stat().st_size,
   'fresh_extraction_matches_saved':result.stdout==txt.read_bytes(),'fresh_extraction_sha256':sha(result.stdout)})
 out={'retrieved_utc':datetime.now(timezone.utc).isoformat(),'pin':PIN,'accepted_true_per_user':True,'entries':rows}
 (ROOT/'source-manifest.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'pinned_files_authenticated':len(manifest),'primary':rows[-5:],'manifest':'source-manifest.json'},indent=2))
if __name__=='__main__':main()
