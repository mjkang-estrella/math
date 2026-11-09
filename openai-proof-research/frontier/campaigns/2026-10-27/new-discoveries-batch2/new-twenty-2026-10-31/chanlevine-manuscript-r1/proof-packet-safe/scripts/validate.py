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
header="import ChanLevineFinal\nimport Lean.Util.CollectAxioms\nopen Lean\nset_option maxRecDepth 30000\nset_option maxHeartbeats 20000000\nrun_cmd do\n  let env ← getEnv\n  let locals : Array Name := #[ "+', '.join('`'+n for n in sorted(closure))+" ]\n"
a=root/'tmp/AssemblyAuditRoots.lean'
a.write_text(header+"  for (n, _) in env.constants.toList do\n    if let some idx := env.getModuleIdxFor? n then\n      if locals.contains env.header.moduleNames[idx.toNat]! then logInfo m!\"ROOT {n}\"\n")
rootlog=run('assembly-audit-roots',[binary/'lean','-j1','-M3500','-DwarningAsError=true',a])
roots=set(re.findall(r'^ROOT (\S+)',(root/rootlog).read_text(),re.M));assert roots
checks={};edges={};axioms=set();logs=[rootlog];pending=set(roots);batch=0
while pending:
 names=sorted(pending)[:256];pending.difference_update(names);batch+=1
 # Name literals preserve private and generated declaration components.
 body="  let names : Array String := #[ "+', '.join(json.dumps(n,ensure_ascii=False) for n in names)+" ]\n  let wanted := names.foldl (fun (s : Std.HashSet String) n => s.insert n) {}\n"
 body+=r'''  for (n, ci) in env.constants.toList do
    if !wanted.contains n.toString then continue
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
    if let .inductInfo v := ci then deps := deps ++ v.ctors.toArray
    let depText := String.intercalate "|" (deps.toList.map Name.toString)
    let impl := Lean.Compiler.getImplementedBy? env n
    let ext := isExtern env n
    let localDecl := match env.getModuleIdxFor? n with
      | some idx => locals.contains env.header.moduleNames[idx.toNat]!
      | none => false
    logInfo m!"CHECK {n} LOCAL {localDecl} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} IMPLEMENTED_BY {impl} EXTERN {ext} DEPS {depText}"
    if ci.isUnsafe || ci.isPartial || n.toString.endsWith "_unsafe_rec" then throwError "Forbidden declaration {n}"
    if localDecl && (impl.isSome || ext) then throwError "Forbidden local implementation {n}"
    if let .axiomInfo _ := ci then
      logInfo m!"CLOSURE_AXIOM {n}"
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do throwError "Forbidden axiom {n}"
'''
 a=root/'tmp'/f'AssemblyAuditBatch{batch}.lean';a.write_text(header+body)
 log=run(f'assembly-audit-batch-{batch}',[binary/'lean','-j1','-M3500','-DwarningAsError=true',a]);logs.append(log);s=(root/log).read_text()
 rows=re.findall(r'^CHECK (\S+) LOCAL (true|false) UNSAFE (true|false) PARTIAL (true|false) IMPLEMENTED_BY (.*?) EXTERN (true|false) DEPS ([^\n]*)',s,re.M)
 assert {r[0] for r in rows}==set(names),(batch,len(rows),len(names))
 for name,*r,ds in rows:
  assert name not in checks;checks[name]=tuple(r);edges[name]=set(ds.split('|')) if ds else set()
 axioms.update(re.findall(r'^CLOSURE_AXIOM (\S+)',s,re.M))
 for name in names:pending.update(edges[name]-checks.keys())
 print('AUDIT_PROGRESS',len(checks),'pending',len(pending),flush=True)
seen=set();work=list(roots)
while work:
 x=work.pop()
 if x in seen:continue
 seen.add(x);work+=list(edges[x])
assert seen==set(checks)
assert roots=={n for n,r in checks.items() if r[0]=='true'}
assert all(r[1:3]==('false','false') and not n.endswith('_unsafe_rec') for n,r in checks.items())
assert not any('ofReduceBool' in n or 'native_decide' in n or n=='sorryAx' for n in checks)
flags={n:r for n,r in checks.items() if r[3]!='none' or r[4]=='true'}
assert all(checks[n][0]=='false' for n in flags)
assert axioms<={'propext','Classical.choice','Quot.sound'}
report={'module_closure':sorted(closure),'local_declarations':len(roots),'upstream_declarations':len(seen)-len(roots),'total_closure':len(seen),'allowOpaque':True,'generated_declarations_included':True,'independent_closure_equality':True,'unsafe':0,'partial':0,'unsafe_rec':0,'LOCAL_flags':{},'UPSTREAM_metadata':flags,'axioms':sorted(axioms),'logs':logs,'batches':batch}
(root/'logs/assembly-audit.json').write_text(json.dumps(report,indent=2))
(root/'logs/assembly-graph.json').write_text(json.dumps({'roots':sorted(roots),'edges':{n:sorted(d) for n,d in edges.items()}},indent=2))
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
