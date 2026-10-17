"""One-time handoff assembly; repository-relative source references. MIT.
Not needed by recipients of the clean public package.
"""
from pathlib import Path
import hashlib,json,shutil
R=Path(__file__).resolve().parents[1]; B=R.parent
records=[]
for src,dst in [('fresh-arithmetic-discovery-r4/verify_math.py','author.py'),('seymour-s2-proof-r1/check_mechanisms.py','reviewer.py')]:
    data=(B/src).read_bytes(); (R/'support/inherited'/dst).write_bytes(data)
    records.append({'path':'support/inherited/'+dst,'origin':src,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'modified':False})
s=(R/'support/inherited/reviewer.py').read_text()
head=s[:s.index('def main():')]
body=s[s.index('    deletion=blowup=anchors=0'):s.index('    result=')]
end='''    return {'deletion_endpoint_cases':deletion,'blowup_subset_cases':blowup,'anchor_exclusion_cases':anchors}\nif __name__=='__main__':print(json.dumps(main(),sort_keys=True))\n'''
adapt='# Portable adapter: unchanged mathematical loops of inherited/reviewer.py.\n# Repository authentication and receipt writing removed; see PROVENANCE.md. MIT.\n'+head+'def main():\n'+body+end
(R/'support/reviewer_portable.py').write_text(adapt)
records.append({'path':'support/reviewer_portable.py','origin':'support/inherited/reviewer.py','sha256':hashlib.sha256(adapt.encode()).hexdigest(),'bytes':len(adapt.encode()),'modified':True,'change':'Removed repository/source authentication prefix and repository receipt-writing suffix; mathematical functions and loops unchanged.'})
(R/'checker-identities.json').write_text(json.dumps(records,indent=2)+'\n')
inputs={}
for rel in ['fresh-arithmetic-discovery-r4/candidate.md','fresh-arithmetic-discovery-r4/scope.md','fresh-arithmetic-discovery-r4/source-contracts.md','fresh-arithmetic-discovery-r4/output-manifest.json','seymour-s2-proof-r1/review.md','seymour-s2-proof-r1/checks.json','seymour-s2-contribution-r1/review.md','seymour-s2-contribution-r1/findings.md','seymour-s2-contribution-r1/input-receipt.json','seymour-s2-contribution-r1/seal.json','complex-projector-borsuk-parent/fresh-r17-brief.txt']:
    data=(B/rel).read_bytes();inputs[rel]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
(R/'input-manifest.json').write_text(json.dumps(inputs,indent=2)+'\n')
receipt=json.loads((B/'seymour-s2-contribution-r1/input-receipt.json').read_text())
(R/'source-identities.json').write_text(json.dumps({'pin':receipt['source_pin'],'upstream':receipt['authenticated_source_files'],'primary_urls':receipt['private_urls'],'private_primary_identities':receipt['private_primary_files'],'dara':receipt['dara_primary'],'rights':'Identity records only; no third-party source or reading copy is included.'},indent=2)+'\n')
for name in ['LICENSE-CODE','LICENSE-PROSE']:
    shutil.copyfile(B/'kn-minus-edge-manuscript-r2'/name,R/name)
