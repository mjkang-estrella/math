import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;root=L.parents[0].parent
refs=json.loads((L/'bindings.json').read_text());D={x['path']:x for x in refs}
for p in [L.parents[1]/'AGENTS.md',L.parents[1]/'ledger.json',L.parents[1]/'prior-campaign-context.json',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')]:
 b=p.read_bytes();D[str(p)]={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
(L/'bindings.json').write_text(json.dumps(list(D.values()),indent=2)+'\n')
f=json.loads((L/'failures.json').read_text());f.append({'kind':'instruction_read_timing','status':'DISCLOSED_PROCEDURAL_DEVIATION','details':'Ancestor openai-proof-research/AGENTS.md read initially; campaign new-discoveries-batch2/AGENTS.md was read only at finalization, after scientific screening. Its bytes pinned now, not a retroactive pre-content freeze. Current ledger/context hashes match previously bound304 snapshots; current administrative bodies only partially displayed due truncation, not claimed whole-body review. No investment or acceptance, no children, count changes, prohibited actions.'});(L/'failures.json').write_text(json.dumps(f,indent=2)+'\n')
p=L/'SUMMARY.md';s=p.read_text();s=s.replace('(588 inputs)','(588 preflight inputs; final bindings add instruction/admin references)');s+='\nProcedural caveat: the campaign-level AGENTS.md was discovered/read only at finalization, after screening, whereas the repository ancestor was read at start. This timing failure is preserved in failures.json and is not repaired retroactively by the final hash. Current ledger/context match the hashes of previously bound r304 administrative snapshots; no claim of complete current administrative-body reading is made. No result was proposed or accepted. Root should assess this caveat independently of final integrity PASS.\n';p.write_text(s)
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'schema_version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':L.name,'excluded_separate_envelopes':['manifest.json','final-receipt.json'],'files':files},indent=2)+'\n')
print('sealed',len(files),'files')
