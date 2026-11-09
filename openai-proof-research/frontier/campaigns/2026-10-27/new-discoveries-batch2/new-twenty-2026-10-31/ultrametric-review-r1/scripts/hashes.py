import hashlib, json, sys, os
D='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r157'
files=['CASE-367834.md','raw/367834.jsonl','results.json','outputs/provenance.json','lean-draft/Conj62.lean','scripts/ultra62.py','logs/ultra62.log','logs/ultra62.receipt.json',
'sources/pdf/2504.02425.pdf','sources/txt/2504.02425.txt','sources/untrusted-utu/published.bin','sources/txt/utu-published.txt','sources/abs/2504.02425.html',
'sources/pdf/2402.15774.pdf','sources/txt/2402.15774.txt','sources/pdf/2502.04228.pdf','sources/txt/2502.04228.txt','sources/pdf/2510.01667.pdf','sources/txt/2510.01667.txt','sources/pdf/2607.14098.pdf','sources/txt/2607.14098.txt','sources/related/2010.07280.html','sources/related/2607.14098.html','sources/related/2510.01667.html','TASK.txt','SUMMARY.md']
out={}
for f in files:
    p=os.path.join(D,f)
    out[f]=hashlib.sha256(open(p,'rb').read()).hexdigest() if os.path.exists(p) else None
json.dump({'base':D,'sha256':out},open(sys.argv[1],'w'),indent=1)
print(json.dumps(out,indent=1))
