from pathlib import Path
import re,sys
root=Path(__file__).resolve().parent.parent
src=root/sys.argv[1]
for path in sorted(src.glob('*.lean')):
    s=path.read_text()
    # Strip strings, nested block comments, and line comments before token scanning.
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1; i+=2
        elif depth and s.startswith('-/',i): depth-=1; i+=2
        elif depth: i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        elif s[i]=='"':
            i+=1
            while i<len(s) and s[i]!='"': i+=2 if s[i]=='\\' else 1
            i+=1; out.append(' ')
        else: out.append(s[i]); i+=1
    assert depth==0
    bad=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b|_unsafe_rec',''.join(out))
    assert not bad,(str(path),bad)
    print('SOURCE SCAN PASS',path.name)
