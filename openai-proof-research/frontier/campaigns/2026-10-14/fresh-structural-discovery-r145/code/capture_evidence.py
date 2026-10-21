"""Late selected-original capture; never a whole-root or first-read certificate."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parents[1];P=R.parents[3]
paths={
 'AGENTS.md':'full', 'sources/upstream.json':'full',
 'sources/CONTENTS.md':'lines1-110 incidental; literal family-term searches only afterward',
 'sources/preprints-tree.json':'complete JSON metadata parsed; targeted path matching, not source semantic reading',
 'frontier/NEW-TEN-2026-10-14.md':'lines1-180 only',
 'frontier/scouts/discrete.md':'lines1-178, with unrelated headings incidental; union-closed proof sections only used',
 'frontier/reviews/frankl-direct-r2.md':'full; direct old operative original followed late',
 'frontier/experiments/frankl_r2_nearmiss.mjs':'full',
 'frontier/experiments/frankl_r2_exhaustive.mjs':'lines1-130',
}
base='frontier/campaigns/2026-10-14/'
for rel in ['discovery-structural-r144-parent/assessment.md','discovery-structural-r144-parent/contribution-r1-disposition.md','discovery-structural-r144-parent/proof-r1-disposition.md','fresh-structural-discovery-r144/notes/03-frozen-scope.md','fresh-structural-discovery-r144/notes/04-author-proof.md','fresh-structural-discovery-r144/notes/05-evidence-and-comparison.md','discovery-analytic-r138-parent/contribution-r1-disposition.md']:
 paths[base+rel]='full; explicitly named completed exception; truncated combined scope/proof display recovered separately'
records=[]
for i,(path,extent) in enumerate(paths.items()):
 data=(P/path).read_bytes();local=R/'private/context'/f'{i:02d}'/Path(path).name;local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(data)
 records.append({'canonical_local_path':path,'snapshot':str(local.relative_to(R)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'capture':'late-current-original; first-read bytes not authenticated','read_extent':extent})
(R/'private/context/receipts.json').write_text(json.dumps({'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'whole_original_root_authenticated':False,'original_manifest_reused_for_reduced_copy':False,'membership':'these selected snapshots only; independent of any original packet manifest','records':records},indent=2)+'\n')
print('late selected originals',len(records))
