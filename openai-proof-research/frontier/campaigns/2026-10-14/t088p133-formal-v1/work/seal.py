# Local implementation sealing helper; excluded work, no external writes.
from pathlib import Path
import hashlib,json,stat
root=Path(__file__).resolve().parent.parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
entries={}
for p in [root/'packet',*sorted((root/'packet').rglob('*'))]:
 if p==root/'packet/MANIFEST.json':continue
 s=p.lstat(); assert not p.is_symlink()
 rec={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'kind':'dir' if p.is_dir() else 'file'}
 if p.is_file():rec.update(bytes=s.st_size,sha256=sha(p))
 entries[str(p.relative_to(root))]=rec
manifest={'format':1,'candidate':'T088P133','round':1,'entries':entries,
 'scope':'Exact packet path set; manifest itself externally anchored.',
 'exclusions':['work/','FINAL.json (separately anchored)','REPORT.md (separately anchored)'],
 'private_source_bodies_included':False,'compiled_dependency_cache_included':False}
(root/'packet/MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
final={'candidate':'T088P133','stage':'scoped formal implementation','round':1,
 'runner':'Codex / GPT-6 Astra / high / default service tier',
 'status':'IMPLEMENTATION_COMPLETE_PENDING_INDEPENDENT_REVIEW',
 'scope':'Universal Proposition B two-bracket real algebra, strict and non-strict rational mixture wrappers, one-sided deterministic bounds; not the full theorem.',
 'full_theorem_formalized':False,'independent_review':False,
 'manifest_sha256':sha(root/'packet/MANIFEST.json'),'outside_report_sha256':sha(root/'REPORT.md'),
 'source_sha256':{f:sha(root/'packet/public'/f) for f in ['T088P133.lean','Controls.lean']},
 'declarations':{'support':21,'controls':20},'publication':'STOPPED',
 'unresolved_implementation_issues':[],
 'outstanding':'Independent parent/formal review and subsequent campaign requirements; no gate or count assigned.'}
(root/'FINAL.json').write_text(json.dumps(final,indent=2)+'\n')
anchors={f:sha(root/f) for f in ['FINAL.json','packet/MANIFEST.json','REPORT.md']}
(root/'work/anchors.json').write_text(json.dumps(anchors,indent=2)+'\n')
print(json.dumps(anchors,indent=2))
