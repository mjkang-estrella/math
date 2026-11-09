import json,hashlib,os
lane='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6'
EXCLUDE_DIRS={'tmp'}
EXCLUDE_FILES={'SHA256-MANIFEST.json','frozen-after.json','frozen-before.json'}
entries={}
for root,dirs,files in os.walk(lane):
    dirs[:]=sorted(d for d in dirs if d not in EXCLUDE_DIRS and not d.startswith('.'))
    for f in sorted(files):
        p=os.path.join(root,f)
        rel=os.path.relpath(p,lane)
        if rel in EXCLUDE_FILES: continue
        entries[rel]=hashlib.sha256(open(p,'rb').read()).hexdigest()
for must in ['frozen-inputs.json','TASK.txt','runner.py','write_lane.py','verify_frozen.py','bootstrap.py']:
    assert must in entries, must
rec={'manifest':'independent-audit-r6-sha256',
 'note':'sha256 of current bytes of every lane artifact; freeze integrity via verify_frozen',
 'terminal_self_exclusions':{
   'SHA256-MANIFEST.json':'this manifest (self-circular otherwise)',
   'frozen-after.json':'written by provided verify_frozen.py AFTER this manifest',
   'frozen-before.json':'root-provided verifier output already recorded at setup',
   'tmp/':'throwaway diagnostic probes (Lean parse/tactic isolation; content-free)'},
 'count':len(entries),'files':dict(sorted(entries.items()))}
open(lane+'/SHA256-MANIFEST.json','w').write(json.dumps(rec,indent=2)+'\n')
print('entries',len(entries))
