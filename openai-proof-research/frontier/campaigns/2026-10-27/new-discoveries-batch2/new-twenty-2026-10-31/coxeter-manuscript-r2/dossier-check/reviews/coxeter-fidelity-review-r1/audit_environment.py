from pathlib import Path
import json,hashlib,re,subprocess
w=Path(__file__).resolve().parent; f=w/'fresh';d=json.loads((f/'dependency-hashes.json').read_text());out={'scope':d['scope'],'unresolved':d['unresolved'],'external':{},'local_source':{}}
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for n,v in d['modules'].items():
 if n in [p.stem for p in f.glob('*.lean')]:out['local_source'][n]=h(f/(n+'.lean'))==v['source_sha256'];continue
 vals={k:h(v[k]) for k in ['source','olean']};assert vals['source']==v['source_sha256'] and vals['olean']==v['olean_sha256'],n
 out['external'][n]=vals
pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib');g=pk/'.git'
if g.is_file():g=(pk/g.read_text().strip().split(': ',1)[1]).resolve()
head=(g/'HEAD').read_text().strip();out['mathlib_HEAD']=head
if head.startswith('ref: '):
 ref=head[5:];rf=g/ref
 out['mathlib_revision']=rf.read_text().strip() if rf.exists() else next(l.split()[0] for l in (g/'packed-refs').read_text().splitlines() if l.endswith(' '+ref))
else:out['mathlib_revision']=head
assert out['mathlib_revision']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
tc=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux');out['lean_version']=subprocess.check_output([str(tc/'bin/lean'),'--version'],text=True).strip();out['lean_binary_sha256']=h(tc/'bin/lean');out['lean_toolchain']=(pk/'lean-toolchain').read_text();out['external_count']=len(out['external']);assert all(out['local_source'].values())
# Lexical scan strips comments; executable declarations and escape hatches checked separately from prose.
def strip(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);return re.sub(r'--[^\n]*','',s)
scan={}
for p in f.glob('*.lean'):
 hits=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|implemented_by|extern|run_tac|elab_rules|set_option\s+.*(?:trust|kernel)',strip(p.read_text()));scan[p.name]=hits;assert not hits,(p,hits)
out['local_scan']=scan
(w/'environment-audit.json').write_text(json.dumps(out,indent=2));print('PASS',out['external_count'],'external source/olean hashes; local source hashes; pin',out['mathlib_revision'],out['lean_version'])
