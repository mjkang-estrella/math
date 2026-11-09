from pathlib import Path
import hashlib,json,subprocess,stat,sys
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');C=B/'frontier/campaigns/2026-10-14';O=C/'t088p133-manuscript-review-r1'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
anchors={
 't088p133-contribution-r1':['c84fa541285ee770acf37b9df9728dee603bb40202fec6dfc868173a6069e7c7','66405c96dd6b76d25e7a290dc8d17d1f24abf489bcb2c45fd7e4deb8eef13656','89595f993f3f5ec2aa98bc87cfa30eefdaa2d4319b5f77b3c45349191e72627b'],
't088p133-manuscript-r2':['7a98b6fc2f55ddc21187b77dac24538e193492732e36fe0f07fe4c5bf3c29672','c726a7a8329271f9a903cb88b230217820574f1c5e35248ed3670becacc68d68','11a45a886b1cba9262809a8cfce0df5842ead74993efb0730400ab4702bab6f1'],
't088p133-manuscript-r1':['78f23929122e7620522feb5e5679dd290071f9848a15f892d4806275a83f8a39','e7d2588e9783d3f2bd0ec7754e7865be0e5c12ed8609531f5632e80266eccb34','87779f0e8a55fd31920a3345fed238cd70ea99afa26a758d7158e28e69110330'],
'fresh-analytic-discovery-r133':['4656a93d80d1b67f4d349f3f95382ab8b03e644e45ad61b22629a86bd5c2cd09','9ab6adfb17b4e612ad8bee1175109c15b73a1975b67dcc4c580dd955e3306324','3659f82ea364b41303f4097e7df0d12ef380cab5a2d43b0f6bc39ed1405d49fd'],
't088p133-proof-r3':['1de166996e1131bb730501cc1c22ea09b0b3418ec3b266ce63ecedb4f6d25a88','407a6065cd2e44824701ec63459003f740d2c343cf5aca7e84450a84a2c34695','1dbc83e2768d52df28a4475d3d572fa2c90264632ef85b7f5d2be12775e2422c'],
't088p133-formal-v1':['4fa662b09a569b1120f1fe524e6f7b8d81db0cdd6b021eef8027b1622ab15964','042edffc552a51b2c5a96cfdfca660de9ced1d2295106765f292dc546dd8210a','7c169c608cce6f452cf95ddee16ea1cc37fab8633d474d67d63e82245cdf1476'],
't088p133-formal-review-r1':['d50f1d0309089266f87e13d02a10e49d0b4fed8961031a14cfbdbb983e33943a','028b5a8d5f5ebad46c5b690e4259e626cfd8d6d045b4a68aac551bee0d3f3978','69a03b514296d023e3f16034252931dce413f908c3e6770e8e0dc42876d61ebc']}
results={}
for name,aa in anchors.items():
 r=C/name;got=[h(r/p) for p in ['FINAL.json','packet/MANIFEST.json','REPORT.md']];assert got==aa,(name,got); results[name]={'anchors':got}
 m=json.loads((r/'packet/MANIFEST.json').read_text())
 entries=m.get('entries',m.get('files',{})); count=0
 for rel,vv in entries.items():
  p=r/rel; ss=p.lstat(); assert not p.is_symlink()
  if vv.get('kind')=='dir': assert p.is_dir(); continue
  assert p.is_file() and ss.st_nlink==1
  assert h(p)==vv['sha256'],(name,rel)
  assert ss.st_size==vv.get('bytes',vv.get('size'))
  if 'mode' in vv: assert stat.S_IMODE(ss.st_mode)==vv['mode']
  count+=1
 results[name]['manifest_named_files_verified']=count
 if name=='t088p133-manuscript-r2':
  cmd=['python3','-B',str(r/'packet/public/verify.py'),str(r)]
  for label,a in zip(['final','manifest','report'],aa):cmd+=['--'+label+'-sha256',a]
  z=subprocess.run(cmd,capture_output=True,text=True);assert z.returncode==0,z.stderr
  results[name]['trusted_verifier_stdout']=z.stdout
  for rel,key in [('private/MANIFEST-r2.json','private_evidence_manifest_sha256'),('private/build-cache-manifest-r2.json','private_cache_inventory_sha256')]:
   f=json.loads((r/'FINAL.json').read_text());assert h(r/rel)==f[key]
   mm=json.loads((r/rel).read_text())
   for rr,vv in mm['files'].items():
    pp=r/rr; assert h(pp)==vv['sha256'] and pp.stat().st_size==vv['bytes'],rr
    assert stat.S_IMODE(pp.stat().st_mode)==vv['mode'],rr
   results[name][key]={'sha256':h(r/rel),'named_files':len(mm['files']),'verified_bytes_sizes_modes':True}
assert h(B/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
results['tree']={'sha256':h(B/'sources/preprints-tree.json'),'not_body_audit':True}
(O/('evidence/'+(sys.argv[1] if len(sys.argv)>1 else 'authentication-recheck.json'))).write_text(json.dumps(results,indent=2));print(json.dumps(results,indent=2))
