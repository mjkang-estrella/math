from pathlib import Path
import json,sys,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r238')
PREFIX={'sep':'preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/build/','oct':'preprints/Nonuniqueness-with-local-conservation-for-the-hard-sphere-Boltzmann-equation-October-5-2026/build/'}
bounds=json.loads((R/'private/canonical-boundaries.json').read_text())
mode,alias,rel=sys.argv[1:4]; p=PREFIX[alias]+rel; meta=bounds[p]
if mode=='class':
 print(p,json.dumps(meta)); sys.exit()
b=(R/'private/canonical'/p).read_bytes(); lines=b.splitlines(keepends=True); offsets=[0]
for l in lines: offsets.append(offsets[-1]+len(l))
a=int(sys.argv[4]) if len(sys.argv)>4 else 1; z=int(sys.argv[5]) if len(sys.argv)>5 else len(lines)
assert 1<=a<=z<=len(lines)
masked={x['line'] for x in meta['boundaries'] if x['label']=='EDITORIAL_OR_PRODUCTION_REQUIRES_CLASSIFICATION'}
# Production matches in the two drivers and hypersetup lines only; any other marker requires explicit prior resolution.
if masked and rel not in ['paper.tex','main.tex','preamble.tex']:
 raise SystemExit('Unresolved editorial candidates; classify explicitly before reading.')
print('\nSELECTED',p,'LINES',a,z,'BYTES',offsets[a-1],offsets[z])
for i in range(a,z+1):
 print(f'{i}: '+('[MASKED PRODUCTION LINE]\n' if i in masked else lines[i-1].decode()),end='')
with (R/'private/semantic-reads.jsonl').open('a') as f:
 f.write(json.dumps({'path':p,'lines':[a,z],'bytes':[offsets[a-1],offsets[z]],'masked_lines':sorted(masked.intersection(range(a,z+1))),'sha256':hashlib.sha256(b).hexdigest(),'parser':'bytes.splitlines(keepends=True), same parser for classification and display'})+'\n')
