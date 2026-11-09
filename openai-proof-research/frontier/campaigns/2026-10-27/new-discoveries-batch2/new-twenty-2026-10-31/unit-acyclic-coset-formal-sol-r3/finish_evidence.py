from pathlib import Path
import json,hashlib,re,tarfile
lane=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=json.loads((lane/'results'/'generated-build-plan.json').read_text())['production_modules']
records=[]
for base in [lane,lane/'cleanroom']:
    for m in mods:
        src=base/'src'/f'{m}.lean';obj=base/'build'/f'{m}.olean'
        assert src.is_file() and obj.is_file()
        records.append({'root':str(base.relative_to(lane)), 'module':m,'source_sha256':sha(src),'postchecker_olean_sha256':sha(obj)})
        assert sha(src)==sha(lane/'src'/f'{m}.lean')
        for token in ['sorry','admit','axiom','unsafe','partial','extern','implementedBy','native_decide']:
            assert not re.search(r'\b'+token+r'\b',src.read_text()),(src,token)
(lane/'results'/'postchecker-hashes.json').write_text(json.dumps(records,indent=2))
receipts=[]
for p in list((lane/'receipt').glob('*.json'))+list((lane/'cleanroom'/'receipt').glob('*.json')):
    d=json.loads(p.read_text());assert not d['group_members_left']
    if 'lean_' in d['label'] or 'leanchecker_' in d['label']:
        lp=d['env']['LEAN_PATH'].split(':')
        expected=p.parent.parent/'build'
        assert lp[0]==str(expected)
        assert all('/.lake/packages/' in x and x.endswith('/.lake/build/lib/lean') for x in lp[1:])
    receipts.append({'path':str(p.relative_to(lane)), 'exit':d['exit'],'label':d['label'],'group_members_left':d['group_members_left'],'guard':d['guard'],'sha256':sha(p)})
(lane/'results'/'receipt-index.json').write_text(json.dumps(receipts,indent=2))
for base in [lane,lane/'cleanroom']:
    rs=[json.loads(p.read_text()) for p in (base/'receipt').glob('*.json')]
    for m in mods:
        assert any(d['label']==f'lean_{m}' and d['exit']==0 for d in rs)
        assert any(d['label']==f'leanchecker_{m}' and d['exit']==0 for d in rs)
    for m in ['WrongIndicator','WrongUnit','WrongAcyclic']:
        assert any(d['label']==f'audit_{m}' and d['exit']==1 for d in rs)
    inv=json.loads((base/'audit'/'inventory.json').read_text())
    assert inv['local_count']==101 and not inv['forbidden']
    assert set(inv['refutation_axioms'])=={'propext','Classical.choice','Quot.sound'}
    lookup={r['name']:r for r in inv['declarations']};seen=set();todo=['UnitCoset.refutation']
    while todo:
        n=todo.pop()
        if n in seen:continue
        seen.add(n);todo.extend(lookup[n]['dependencies'])
    endpoint=[lookup[n] for n in sorted(seen)]
    (base/'audit'/'endpoint-closure.json').write_text(json.dumps({'count':len(seen),'axioms':[r['name'] for r in endpoint if r['axiom']],'declarations':endpoint},indent=2))
qa={'pdf':'manuscript/340110-draft.pdf','pages':4,'render_receipt_label':'render-blocked-draft','visual_inspection':'All four individual rendered pages inspected through view_image; readable Times fonts, no clipped text, no overlap, complete footers and margin space.','images':[f'manuscript/page-{i}.png' for i in range(1,5)],'fallback':'reportlab missing; groff ms macro missing; no installation attempted. Final PDF generated with own pure-stdlib PDF writer using Times-Roman/Times-Bold; failed logs retained.','skill_marker':'mark-pdf-start exit0, exactly once before first authoring write'}
(lane/'manuscript'/'QA.json').write_text(json.dumps(qa,indent=2))
with tarfile.open(lane/'results'/'340110-source.tar.gz','w:gz') as tf:
    files=[*lane.joinpath('src').glob('*.lean'),*lane.joinpath('audit').glob('*.lean')]
    files += [lane/n for n in ['runner.py','env.sh','check.sh','checker.sh','audit.sh','run_negative.sh','write_lane.py','extract.py','results/generated-build-plan.json','SOURCE-TO-LEAN.md']]
    files += list((lane/'manuscript').glob('*.py'))
    for p in files:tf.add(p,arcname=str(p.relative_to(lane)))
print(json.dumps({'modules':mods,'receipt_count':len(receipts),'all_groups_empty':True,'source_equality':True,'qa_pages':4}))
