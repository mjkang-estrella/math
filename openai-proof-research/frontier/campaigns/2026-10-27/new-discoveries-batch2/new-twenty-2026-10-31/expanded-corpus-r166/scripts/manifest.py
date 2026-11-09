import pathlib,hashlib,json
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
skip={'outputs/manifest-sha256.json','logs/manifest.log','logs/manifest.receipt.json'}
m={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and str(p.relative_to(D)) not in skip}
(D/'outputs/manifest-sha256.json').write_text(json.dumps({'excluded_self_and_live_manifest_job':sorted(skip),'files':m},indent=2)+'\n')
