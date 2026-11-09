from pathlib import Path
import re,json,sys
root=Path(sys.argv[1]);findings=[];files=sorted((root/'src').glob('*.lean'))
for p in files:
 s=p.read_text()
 # Ignore comments and string literals; metadata audit separately checks declarations.
 s=re.sub(r'"(?:\\.|[^"\\])*"','""',s)
 s=re.sub(r'--[^\n]*','',s);s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
 for x in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b|_unsafe_rec',s):findings.append([str(p),x.group()])
print(json.dumps({'files':len(files),'findings':findings},indent=2));assert not findings
