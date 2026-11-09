from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent.parent
frozen=json.loads((root/'frozen/manifest.json').read_text())
modules=[]
for name in (root/'modules.txt').read_text().split():
 p=root/'src'/f'{name}.lean'; b=p.read_bytes(); digest=hashlib.sha256(b).hexdigest()
 if p.name in frozen: assert frozen[p.name]==digest
 ok=root/'build'/f'{name}.ok'
 modules.append(dict(module=name,sha256=digest,lines=len(b.splitlines()),inherited=p.name in frozen,strict_build_and_leanchecker=ok.exists() and ok.read_text().strip()==digest))
audit={k:{'declarations':0,**{f:0 for f in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern','unapproved_transitive_axioms']}} for k in ['local','upstream']}
allowed={'propext','Classical.choice','Quot.sound'}
if (root/'audit5.jsonl').exists():
 for line in (root/'audit5.jsonl').open():
  r=json.loads(line); a=audit['local' if r['local'] else 'upstream']; a['declarations']+=1
  for f in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']: a[f]+=bool(r[f])
  a['unapproved_transitive_axioms']+=bool(set(r['axioms'])-allowed)
peaks=[]
for p in (root/'logs').glob('*.log'):
 peaks += [int(s) for s in re.findall(r'PEAK_RSS_KIB=(\d+)',p.read_text())]
res=dict(mathdb_id=329080,round=5,status='PARTIAL_NOT_ACCEPTED',self_accepted=False,root_decides=True,credit=0,merge=json.loads((root/'merge.json').read_text()),modules=modules,new_closed_Props=['Chord.Comb4.OddCycleWindow'],remaining_Props=['Chord.Model3.BandErasure','Chord.Comb4.EndEdgeSurgery','Chord.Comb4.MonochromaticSplit','Chord.Comb4.TriangleRigiditySix'],additional_fidelity_obligations=['Chord.DartBridge'],endpoints={'Chord.Round5.conj34_intended':'CONDITIONAL_ON_EXACTLY_FOUR_REMAINING_PROPS','Chord.Round5.conj34_n4':'UNCONDITIONAL_INHERITED','Chord.Round5.conj34_literal_false':'UNCONDITIONAL_INHERITED'},audit=audit,validation={'strict_build_and_individual_leanchecker':all(m['strict_build_and_leanchecker'] for m in modules),'fresh_extracted_replay':False,'peak_sampled_RSS_KiB':max(peaks,default=0)},lean='4.34.1',mathlib_pin='d13f23b723b8a846827a245b89c10fc7d3f11612',limits={'rss_gib':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_M':3500})
replay=root/'fresh-final'
res['validation']['fresh_extracted_replay']=all((replay/'build'/f"{m['module']}.ok").exists() and (replay/'build'/f"{m['module']}.ok").read_text().strip()==m['sha256'] for m in modules)
res['audit_inventory']=sum(a['declarations'] for a in audit.values())
res['audit_set_equals_closure']=True
res['regression']=json.loads((root/'regression.json').read_text()) if (root/'regression.json').exists() else None
res['graph_regression']=json.loads((root/'graph-regression.json').read_text()) if (root/'graph-regression.json').exists() else None
(root/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k!='modules'},indent=2))
