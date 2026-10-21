from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;P=R.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
initial=json.loads((R/'private/named-context-metadata.json').read_text())
selected={x['path']:'complete direct named context; combined display truncations recovered in smaller reads' for x in initial}
selected.update({
 'AGENTS.md':'complete', 'sources/upstream.json':'complete',
 'sources/preprints-tree.json':'complete metadata parsed/hash; only Source374 paths semantically selected',
 'frontier/NEW-TEN-2026-10-14.md':'lines 1-170; later r12/log-concave-Brenier matching lines only (mutable navigation, not original theorem input)',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r12/original-scope.md':'complete full old LC scope',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r12/candidate.md':'sections 1-4 partial combined display, then lines 125-220 recovered; remaining candidate not claimed fully read',
 'frontier/campaigns/2026-10-14/brenier-logconcave-parent/review-r1-disposition.json':'complete, followed from journal on actual overlap',
 'frontier/iterations/i33-density-robust-brenier.md':'full-file display truncated; direct 1-115 also partially truncated in combined output. Exact Q and source interfaces, explicit weighted obstruction, sections 4-7 visible; not a complete read certificate',
 'frontier/iterations/i34-target-uniform-brenier.md':'1-105 and 110-230: exact Q, audit, interface budget, zigzag, constructed gluing, two-atom counterexample, start of entropic route; 106-109 and later proof not credited',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r13/original-scope.md':'complete ACCIDENTAL unrelated nodal scope false admission; no premise or pursued family',
})
obs=[];membership=[]
for path,extent in selected.items():
 b=(P/path).read_bytes(); dest=R/'private/originals'/path
 if path!='frontier/NEW-TEN-2026-10-14.md':
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 rec={'original':path,'size':len(b),'git_blob_computed':blob(b),'sha256':sha(b),'read_extent':extent,'snapshot_timing':'late after semantic reading; not first-read authentication'}
 first=next((x for x in initial if x['path']==path),None)
 if first:rec['matches_initial_named_observation']=first['sha256']==sha(b)
 obs.append(rec)
 if path!='frontier/NEW-TEN-2026-10-14.md':membership.append({'copy':str(dest.relative_to(R)),'original':path,'size':len(b),'sha256':sha(b)})
(R/'original-current-bindings.json').write_text(json.dumps({'observation_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'selected actual current originals only; no recursive original-root or historical authentication','records':obs},indent=2)+'\n')
(R/'input-membership.json').write_text(json.dumps({'scope':'explicit selected late snapshots; independent of any original packet manifest; no original manifest copied','members':membership},indent=2)+'\n')
ledger=json.loads((R/'source-ledger.json').read_text())
for rec in ledger:rec['read_extent']='complete text, including full operative section; no PDF rendered';rec['line_count']=len((R/rec['local']).read_bytes().splitlines())
(R/'source-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
reads={
 '2609.35574v1/body.tex':[(47,68),(190,448),(513,570),(575,680),(780,910)],
 '2401.01088v1/2_singularity_convex_functions.tex':[(1,155)],
 '2401.01088v1/3_stability_pushforward.tex':[(1,263)],
 '2604.22366v2/Input_maintext_Leo_Revision.tex':[(832,905)],
}
entries=[]
for rel,ranges in reads.items():
 p=R/'private/primary'/rel;lines=p.read_bytes().splitlines(keepends=True)
 for a,b in ranges:entries.append({'path':str(p.relative_to(R)),'first_line':a,'last_line':b,'sha256_passage':sha(b''.join(lines[a-1:b]))})
(R/'reading-ledger.json').write_text(json.dumps({'actual_primary_passages':entries,'other_primary_limits':'Ruan 2610.07577v1 keyword navigation only; Wang-Wang 2610.09640v1 acquired, not semantically read. Cazelles other ranges keyword navigation. Ford bibliography named transitive entries; no entire-paper claims. CDM initial combined display truncated and endpoints recovered; passage at 155 begins with commented text, main proof read through conclusion.', 'late_reads':'All primaries after first source read and history search; Ford before the initial cancellation derivation was expanded, CDM before final integrated derivation. No freeze ever occurred.'},indent=2)+'\n')
print('selected originals',len(obs),'source files',len(ledger),'primary passages',len(entries),'initial named unchanged',all(x.get('matches_initial_named_observation',True) for x in obs))
