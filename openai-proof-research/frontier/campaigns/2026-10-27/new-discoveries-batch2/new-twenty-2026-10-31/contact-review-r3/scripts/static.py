from pathlib import Path
import re,json,hashlib,zipfile
r=Path(__file__).resolve().parents[1];src=r.parent/'contact-formal-r6/formal';out={}
for f in sorted(src.glob('*.lean')):
 text=f.read_text(); code=re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S);code=re.sub(r'"(?:\\.|[^"\\])*"','',code)
 hits=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',code)
 out[f.name]=hits
assert not any(out.values()),out
for f in src.glob('*.lean'):
 assert f.read_bytes()==(r/'extracted/formal'/f.name).read_bytes()
old=(src/'SourceContact.lean').read_text().split('def SourceConjecture : Prop :=')[1].split('\nend')[0]
new=(src/'SourceContactLocal.lean').read_text().split('def SourceConjectureLocal : Prop :=')[1].split('\nend')[0]
assert old.replace('HasZeroSetContact','HasLocalZeroSetContact')==new
result={'forbidden_token_scan':out,'extracted_sources_identical':True,'universal_definition_only_predicate_changed':True}
(r/'logs/static.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
