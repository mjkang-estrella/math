import json, re, math, itertools, collections, pathlib
lane=pathlib.Path(__file__).resolve().parents[1]
root=lane.parent
src=lane/'build/src'
def rec(w):
    if not w:return ()
    i=w.index(max(w))
    return rec(w[:i])+rec(w[i+1:])+(w[i],)
def stack(w):
    s=[]; out=[]
    for x in w:
        while s and s[-1]<x:out.append(s.pop())
        s.append(x)
    return tuple(out+s[::-1])
seed=list(map(int,re.search(r'def seed20.*? := \[(.*?)\]',(src/'StackSortFinal.lean').read_text()).group(1).split(',')))
table=json.loads((root/'expanded-corpus-r133/outputs/stack_pairs_P_1_82.json').read_text())
counts=[]
for n in range(8):
    h=collections.Counter()
    for w in itertools.permutations(range(n)):
        a=rec(w); assert a==stack(w);h[a]+=1
    p=sum(v*v for v in h.values());counts.append(p)
    assert p==seed[n]
    if n:assert p==int(table[str(n)])
    print('literal',n,'P',p,'maxFib',max(h.values()),'sum',sum(h.values()))
for w in [(),(0,),(2,0,1),(1,2,0),(4,1,6,3,5,2)]:
    print('word',w,'sort',rec(w));assert rec(w)==stack(w)
assert seed[1:]==[int(table[str(n)]) for n in range(1,21)]
g=seed[:]
for n in range(21,131):
    g.append(4*g[n-1]+sum(math.comb(n-1,i)*g[i]*g[n-1-i] for i in range(1,n-1)))
c=int(re.search(r'def lower130 : ℕ := (\d+)',(src/'StackSortCertificate.lean').read_text()).group(1))
assert g[130]==c
lhs=4*131*math.factorial(130)*173**131;rhs=c*100**131
assert lhs<rhs
print('G130',c,'certificate true; positive difference',rhs-lhs)
print('seed20 equals all 20 frozen entries; no claim of independent brute force above 7')
# Remove nested block comments, line comments, and quoted strings, preserving line numbers.
def strip(s):
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\':out.extend('  ');i+=2
            elif s[i]=='"':string=False;out.append(' ');i+=1
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j
            out.extend(' '*(j-i));i=j
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    return ''.join(out)
findings=[]
for f in sorted(src.glob('StackSort*.lean')):
    clean=strip(f.read_text())
    for m in re.finditer(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',clean):
        findings.append([f.name,clean.count('\n',0,m.start())+1,m.group()])
print('source scan',len(list(src.glob('StackSort*.lean'))),'modules:',findings)
assert not findings
(lane/'logs/independent-results.json').write_text(json.dumps({'brute_P_0_7':counts,'certificate130':True,'G130_matches':True,'all_seed_table_matches':True,'source_scan':findings},indent=2)+'\n')
import zipfile, hashlib
with zipfile.ZipFile(root/'stacksort-formal-r6/stacksort-source6.zip') as z:
    entries=[x for x in z.namelist() if x.endswith('.lean')]
    for x in entries:assert z.read(x)==(lane/'build'/x).read_bytes()
    print('All',len(entries),'archived Lean sources unchanged')
modules={f.stem:f for f in src.glob('StackSort*.lean')}
closure=set()
def visit(m):
    if m in closure:return
    closure.add(m)
    for d in re.findall(r'^import\s+(\w+)',modules[m].read_text(),re.M):
        if d in modules:visit(d)
visit('StackSortFinal6')
assert all((src/(m+'.olean')).exists() for m in closure)
print('Endpoint local import closure',len(closure),'modules; all compiled oleans present')
(lane/'logs/closure.txt').write_text('\n'.join(sorted(closure))+'\n')
