import pathlib,json,re,hashlib
r=pathlib.Path(__file__).resolve().parent;f=r/'fresh-extracted'
def metrics(p):
 s=p.read_text();m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)',s);t=0
 for x in m[1].split(':'):t=t*60+float(x)
 return t,int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])
rows=[]
mods=(f/'module-order.txt').read_text().splitlines()
for mod in mods:
 if not (f/'logs'/f'{mod}.ok').exists():continue
 a,b=metrics(f/'logs'/f'build-{mod}.log');c,d=metrics(f/'logs'/f'check-{mod}.log')
 rows.append(dict(module=mod,build_wall_seconds=a,check_wall_seconds=c,build_peak_rss_kib=b,check_peak_rss_kib=d))
info=json.loads((r/'pilot-info.json').read_text());by={x['module']:x for x in rows};pilots=[]
for variant,sizes in [('ordinary_elaboration',[1000]),('direct_expressions',[1000,5000])]:
 for n in sizes:
  subset=info[:n//100];names=[x['module'] if variant=='ordinary_elaboration' else x['module'].replace('MaskPilot','MaskRaw') for x in subset]
  if not all(m in by for m in names):continue
  bs=sum(by[m]['build_wall_seconds'] for m in names);cs=sum(by[m]['check_wall_seconds'] for m in names);h=sum(x['hint_uses'] for x in subset)
  pilots.append(dict(variant=variant,additions=n,start_index=13561,end_exclusive=13561+n,hint_uses=h,compile_seconds=bs,checker_seconds=cs,total_seconds=bs+cs,hints_per_second=h/(bs+cs),speedup_vs_round5_32=h/(bs+cs)/32,peak_rss_kib=max(max(by[m]['build_peak_rss_kib'],by[m]['check_peak_rss_kib']) for m in names),scope='local checks and conditional mask entailments only; no closed CNF prefix extension'))
(r/'module-times.json').write_text(json.dumps(rows,indent=2)+'\n')
result=dict(status='partial',modules_total=len(mods),modules_verified=len(rows),compiler_seconds=sum(x['build_wall_seconds'] for x in rows),checker_seconds=sum(x['check_wall_seconds'] for x in rows),pilots=pilots,closed_new_additions=0,round5_inherited_frontier=13561,round6_remaining_connected_additions=129671,endpoint='Percolation.not_conjecture20_mask_conditional : NormalizedCNFUnsat5 → ¬ Conjecture20',unconditional_status='unproved',allowed_axioms=['propext','Classical.choice','Quot.sound'])
result['total_seconds']=result['compiler_seconds']+result['checker_seconds'];result['source_archive_sha256']=hashlib.sha256((r/'source-only.zip').read_bytes()).hexdigest()
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
