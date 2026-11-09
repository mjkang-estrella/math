import runpy,sys,pathlib,json,re,collections
lane=pathlib.Path(__file__).resolve().parent.parent
root=pathlib.Path(sys.argv[1]).resolve()
b=runpy.run_path(str(lane/'scripts/build.py'))
run=b['run'];binary=b['binary'];sources=b['sources']
closure=set();work=['ChanLevineFinal']
while work:
 n=work.pop()
 if n in closure:continue
 closure.add(n)
 work += [d for d in re.findall(r'^import (\S+)',sources[n].read_text(),re.M) if d in sources]
text=(lane/'scripts/audit-template.lean.txt').read_text().replace('LOCAL_MODULES','#[ '+', '.join('`'+n for n in sorted(closure))+' ]')
a=root/'tmp/AssemblyAudit.lean';a.write_text(text)
log=run('assembly-audit',[binary/'lean','-j1','-M3500','-DwarningAsError=true',a]);s=(root/log).read_text()
roots=set(re.findall(r'^ROOT (\S+)',s,re.M))
rows=re.findall(r'^CHECK (\S+) LOCAL (true|false) UNSAFE (true|false) PARTIAL (true|false) IMPLEMENTED_BY (.*?) EXTERN (true|false)',s,re.M)
checks={r[0]:r[1:] for r in rows};assert len(checks)==len(rows)
edges=collections.defaultdict(set)
for x,y in re.findall(r'^EDGE (\S+) (\S+)',s,re.M):edges[x].add(y)
seen=set();work=list(roots)
while work:
 x=work.pop()
 if x in seen:continue
 seen.add(x);work+=list(edges[x])
assert seen==set(checks)
assert len(seen)==int(re.search(r'TOTAL_CLOSURE (\d+)',s)[1])
assert roots=={n for n,r in checks.items() if r[0]=='true'}
assert all(r[1:3]==('false','false') and not n.endswith('_unsafe_rec') for n,r in checks.items())
flags={n:r for n,r in checks.items() if r[3]!='none' or r[4]=='true'}
assert all(checks[n][0]=='false' for n in flags)
axioms=set(re.findall(r'^CLOSURE_AXIOM (\S+)',s,re.M));assert axioms<={'propext','Classical.choice','Quot.sound'}
report={'module_closure':sorted(closure),'local_declarations':len(roots),'upstream_declarations':len(seen)-len(roots),'total_closure':len(seen),'allowOpaque':True,'generated_declarations_included':True,'independent_closure_equality':True,'unsafe':0,'partial':0,'unsafe_rec':0,'LOCAL_flags':{},'UPSTREAM_metadata':flags,'axioms':sorted(axioms),'log':log}
(root/'logs/assembly-audit.json').write_text(json.dumps(report,indent=2))
controls={
'WrongDifferentGCD':"import ChanLevineFinal\nexample : ChanLevine.r 3 3 0 = ChanLevine.r 3 3 1 := by\n  exact (ChanLevine.mathdb_338887 3 3 (by decide) (by decide) 0 1 (by decide)).2.2\n",
'MissingPositiveLevel':"import ChanLevineFinal\nexample (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (i j : ZMod n) (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) : ChanLevine.r n m i = ChanLevine.r n m j := by\n  exact (ChanLevine.mathdb_338887 n m hn (by omega) i j h).2.2\n",
'WrongWeightConvention':"import Controls\nexample : ChanLevine.Controls.wrongWeight ChanLevine.Controls.start = ChanLevine.Controls.wrongWeight (ChanLevine.fire ChanLevine.Controls.start 0) := by decide\n"}
for n,src in controls.items():
 p=root/'tmp'/f'{n}.lean';p.write_text(src);run('negative-'+n,[binary/'lean','-j1','-M3500','-DwarningAsError=true',p],fail=True)
p=root/'tmp/PositiveControls.lean'
p.write_text("import ChanLevineFinal\nimport Controls\nexample : ChanLevine.r 3 3 1 = ChanLevine.r 3 3 2 := (ChanLevine.mathdb_338887 3 3 (by decide) (by decide) 1 2 (by decide)).2.2\nexample : ChanLevine.Controls.wrongWeight ChanLevine.Controls.start ≠ ChanLevine.Controls.wrongWeight (ChanLevine.fire ChanLevine.Controls.start 0) := ChanLevine.Controls.wrong_weight_rejected\n")
run('positive-controls',[binary/'lean','-j1','-M3500','-DwarningAsError=true',p])
(root/'logs/validation-result.json').write_text(json.dumps({'status':'PASS','audit':report,'negative_controls':list(controls),'positive_controls':'PASS'},indent=2))
print('ASSEMBLY VALIDATION PASS',flush=True)
