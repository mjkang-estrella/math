import json,re,sys
from pathlib import Path
root=Path(sys.argv[1]).resolve()
pattern=re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|bv_decide|implemented_by|partial|extern)\b|_unsafe_rec')
findings=[]
files=sorted((root/'src').glob('*.lean'))
for path in files:
    for n,line in enumerate(path.read_text().splitlines(),1):
        # Audit detects these strings as forbidden declaration metadata.
        if path.name=='Audit.lean' and '"_unsafe_rec"' in line:
            line=line.replace('"_unsafe_rec"','"GENERATED_RECURSION_PATTERN"')
        findings.extend([path.name,n,m.group()] for m in pattern.finditer(line))
print(json.dumps({'files':len(files),'forbidden_source_tokens':findings},indent=2))
if findings: raise SystemExit(1)
