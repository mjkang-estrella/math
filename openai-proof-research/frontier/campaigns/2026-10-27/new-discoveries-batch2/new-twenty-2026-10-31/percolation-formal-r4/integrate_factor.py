from pathlib import Path
import json,zipfile,hashlib
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');P=R/'packet';S=P/'src';F=R/'fresh-extracted'
mods=['NDefs024']+[f'NCheck024_{k}' for k in range(5)]+['NReplay024']
for m in mods:(S/(m+'.lean')).write_bytes((R/'check-factoring/src'/(m+'.lean')).read_bytes())
old=(P/'module-order.txt').read_text().splitlines();assert len(old)==436
order=old[:434]+mods+old[-2:];assert len(order)==443
p=S/'NormalizedEndpoint.lean';t=p.read_text().replace('NReplay023','NReplay024').replace('prefix023','prefix024').replace('prefix_sound023','prefix_sound024').replace('after12000','after12500');p.write_text(t)
p=S/'AuditR4.lean';t=p.read_text();a=t.index('  let localModules : Array String := #');b=t.index('\n  for (n, ci)',a);t=t[:a]+'  let localModules : Array String := #'+json.dumps(order,separators=(',',':'))+t[b:];p.write_text(t)
assert set(order)=={p.stem for p in S.glob('*.lean')}
(P/'module-order.txt').write_text('\n'.join(order)+'\n')
rows=json.loads((R/'normalized-trimmed.json').read_text())['steps']
with (P/'replay-frontiers.tsv').open('a') as f:f.write(f'NReplay024\t12500\t{rows[12499][0]}\t{rows[12500][0]}\n')
(P/'source-manifest.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P))+'\n' for p in sorted(S.glob('*.lean'))))
with zipfile.ZipFile(R/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(S.glob('*.lean')):z.write(p,str(p.relative_to(P)))
 for n in ['module-order.txt','source-manifest.sha256','guard.sh','replay.sh','scan.py','replay-frontiers.tsv','normalized-trimmed.json','normalized.cnf','certificate-sha256.json','generator-correspondence.json','generate_replay.py']:z.write(P/n,n)
with zipfile.ZipFile(R/'source-only.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist());z.extractall(F)
(R/'unreplayed-generated/README.md').write_text('Unverified raw source drafts are excluded from source-only.zip. Raw NReplay024 failed the CPU cap, but its factored replacement is now included in the formal packet. The genuine unverified suffix begins with NReplay025, steps[12500]. The unconditional endpoint draft remains unverified.\n')
print({'modules':443,'next_zero_based_index':12500,'next_lrat_id':rows[12500][0],'last_id':rows[12499][0]})
