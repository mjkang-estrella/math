import pathlib,json,hashlib,re,datetime
D=pathlib.Path(__file__).resolve().parent; A=D.parent/'expanded-corpus-r49'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((D/'frozen-inputs.json').read_text())['files']; bad={p:{'expected':h,'actual':sha(pathlib.Path(p)) if pathlib.Path(p).exists() else None} for p,h in f.items() if not pathlib.Path(p).exists() or sha(pathlib.Path(p))!=h}
(D/'integrity-after.json').write_text(json.dumps({'bindings':len(f),'mismatches':bad},indent=2));assert len(f)==328 and not bad
summary={}
for m in ['Yip355956','V3Config355701']:
 s=(D/f'origin-{m}.log').read_text();full=(D/f'full-origin-{m}.log').read_text();flags=(D/f'flags-{m}.log').read_text(); names=re.findall(r'^ORIGIN ([^\n]+)',s,re.M)
 ax=[]
 for x in re.findall(r'depends on axioms: \[(.*?)\]',s):ax+= [re.sub(r'\.\{.*','',a.strip()) for a in x.split(',') if a.strip()]
 assert set(ax)<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'(unsafe|partial|axiom)=true',flags)
 assert f'FLAG_COUNT {len(names)}' in flags
 summary[m]={'origin_count':len(names),'names':names,'transitive_axioms':sorted(set(ax)),'all_flags_false':True,'full_dump_completed':f'ORIGIN_COUNT {len(names)}' in full,'full_dump_ellipsis_count':full.count('⋯'),'full_dump_sha256':sha(D/f'full-origin-{m}.log')}
(D/'audit-summary.json').write_text(json.dumps(summary,indent=2))
base={'source_fidelity':'PASS','ordinary_semantics':'PASS','independent_exact_witness':'PASS','fresh_strict_build':'PASS','module_leanchecker':'PASS','origin_inventory':'PASS','transitive_axioms':'PASS','unsafe_partial_new_axiom_flags':'PASS','negative_controls':'PASS','before_after_integrity':'PASS'}
r={'utc':datetime.datetime.now(datetime.UTC).isoformat(),'role':'independent technical review only','campaign_count_context':'4/20 beyond 39; zero credit assigned here','novelty_significance':'UNRESOLVED: separate Claude review unfinished/provider quota, no implicit PASS','acceptance':'ROOT ONLY; neither candidate accepted by this audit','packet_sha256':sha(A/'proof-packet.zip'),'integrity_bindings':328,'manifest_bindings':115,'literal_result_entries':40,'results':{}}
for id,m,ep in [('355956','Yip355956',['MathDB355956.yip_conjecture_false','MathDB355956.yip_conjecture_SG_false']),('355701','V3Config355701',['MathDB355701.conjectureInclusion_false','MathDB355701.conjectureMaximum_false'])]:
 complete=summary[m]['full_dump_completed'];r['results'][id]={'technical_verdict':'PASS' if complete else 'HOLD_FULL_PROOF_DUMP_INCOMPLETE','gates':dict(base,full_types_proofs_unabridged='PASS' if complete else 'INCOMPLETE_CPU_CAP'),'mathematical_objections':[],'technical_objections':[] if complete else ['Unabridged pp.all=true pp.proofs=true pp.deepTerms=true origin dump killed at 120 CPU seconds (return -9), after starting 20/40 declarations. Compact full-origin inventory/axiom audit and kernel replay do pass, but do not satisfy this separately requested full-proof-dump gate.'],'endpoints':ep,'source_sha256':sha(A/f'lean/{m}.lean'),'audit':summary[m]}
r['trust_limits']=['External prebuilt upstream oleans trusted, not rebuilt or source-to-olean attested','leanchecker reuses the same Lean kernel, not an independent foundation','No registry/novelty clearance, no publication or acceptance credit','RSS is systemd MemoryMax=6G; AS adjusted from12 to64GiB following reproduced thread failure; CPU120s wall140s per process']
(D/'review.json').write_text(json.dumps(r,indent=2)+'\n')
print({k:v['technical_verdict'] for k,v in r['results'].items()})
