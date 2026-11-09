#!/usr/bin/env python3
"""One own-packet seal, after same-logic preflight. Never reseals an existing manifest."""
import hashlib
import json
import os
from pathlib import Path

PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT=PROJECT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cu'
assert Path.cwd()==PROJECT
ns={'__name__':'r162cu_readonly_verifier'}
exec(compile((ROOT/'verify.py').read_bytes(),str(ROOT/'verify.py'),'exec'),ns)
mp=ROOT/ns['MANIFEST']; assert not mp.exists(), 'already sealed'
files,dirs=ns['collect'](ROOT)
m={'schema':1,'kind':'r162cu-author-packet','source_pin':ns['PIN'],
   'complete_tree_sha256':ns['TREE_SHA'],'files':files,'directories':dirs,
   'detached_modes':{ns['MANIFEST']:0o100644,'REPORT.md':(ROOT/'REPORT.md').lstat().st_mode}}
mb=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode()
sha=lambda b:hashlib.sha256(b).hexdigest()
a={'final':sha((ROOT/'FINAL.md').read_bytes()),'manifest':sha(mb),'report':sha((ROOT/'REPORT.md').read_bytes())}
pre=ns['verify_packet'](ROOT,a,project=PROJECT,provisional_manifest=mb)
print('SAME-LOGIC PREFLIGHT MATCH',json.dumps(pre,sort_keys=True),flush=True)
fd=os.open(mp,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o644)
with os.fdopen(fd,'wb') as f:
    f.write(mb);f.flush();os.fsync(f.fileno())
post=ns['verify_packet'](ROOT,a,project=PROJECT)
print('SEALED ONCE; READ-ONLY MATCH',json.dumps(post,sort_keys=True),flush=True)
print(json.dumps({'FINAL_SHA256':a['final'],'MANIFEST_SHA256':a['manifest'],'REPORT_SHA256':a['report']},indent=2),flush=True)
