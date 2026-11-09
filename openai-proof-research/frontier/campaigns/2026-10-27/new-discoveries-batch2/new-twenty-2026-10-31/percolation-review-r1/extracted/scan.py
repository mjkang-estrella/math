import sys,re,json
from pathlib import Path
root=Path(sys.argv[1]).resolve()
pattern=re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|partial|extern)\b')
findings=[]
for p in sorted((root/'src').glob('*.lean')):
    for n,line in enumerate(p.read_text().splitlines(),1):
        for m in pattern.finditer(line): findings.append([p.name,n,m.group()])
report={'files':len(list((root/'src').glob('*.lean'))),'forbidden_source_tokens':findings}
print(json.dumps(report,indent=2))
if findings: sys.exit(1)
