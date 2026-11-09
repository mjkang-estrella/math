from run_audit import *
import re,collections
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((O/'frozen-inputs.json').read_text()); actual={p:h(pathlib.Path(p)) for p in f};bad=[p for p in f if f[p]!=actual[p]];(O/'frozen-after.json').write_text(json.dumps({'count':len(f),'mismatches':bad,'actual':actual},indent=2));assert not bad
before=json.loads((O/'cache-before.json').read_text());after={str(p):{'size':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns,'sha256':h(p)} for p in PACK.rglob('*.olean*') if p.is_file()};changes=[p for p in set(before)|set(after) if before.get(p)!=after.get(p)];(O/'cache-after.json').write_text(json.dumps(after,indent=2));(O/'cache-integrity.json').write_text(json.dumps({'count_before':len(before),'count_after':len(after),'changed':changes,'read_only_usage':True,'filesystem_enforced_read_only':False,'trust':'User-writable prebuilt upstream cache; not independently rebuilt or attested source-to-olean. Before snapshot completed during initial local builds; all writes of build commands target reviewer lane.'},indent=2));assert not changes
mr=PACK/'mathlib';g=mr/'.git';head=(g/'HEAD').read_text().strip();ref=head[5:] if head.startswith('ref: ') else None;rev=head
if ref:
 rp=g/ref
 rev=rp.read_text().strip() if rp.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
assert rev=='d13f23b723b8a846827a245b89c10fc7d3f11612'
pins=json.loads((O/'pins.json').read_text());pins['mathlib_HEAD_read_directly_no_git_command']=rev;pins['toolchain_leanchecker_same_installation']=str(BIN);pins['dependency_manifest']=json.loads((PACK.parent.parent/'lake-manifest.json').read_text());(O/'pins.json').write_text(json.dumps(pins,indent=2))
log=(O/'review-inventory-final.log').read_text();assert '⋯' not in log and 'TOTAL 66' in log
rows=re.findall(r'^DECL (\S+) ORIGIN some \((\w+)\) UNSAFE (\w+) PARTIAL (\w+) BODY (\w+)$',log,re.M);assert len(rows)==66 and all(x[2:]==('false','false','true') for x in rows)
ax=re.findall(r'^TRANSITIVE_AXIOMS (\S+) \[(.*)\]$',log,re.M);assert len(ax)==66
allowed={'propext','Classical.choice','Quot.sound'};assert all(set(a.split(', ') if a else [])<=allowed for n,a in ax)
source_scan={}
for n in ['Defs','BoolProbe','Checker','Endpoint']:
 s=(F/(n+'.lean')).read_text();source_scan[n]=re.findall(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool)\b',s);assert not source_scan[n]
(O/'inventory.json').write_text(json.dumps({'actual_total':66,'counts_by_actual_origin':dict(collections.Counter(x[1] for x in rows)),'declarations':[dict(zip(['name','origin','unsafe','partial','body'],x)) for x in rows],'transitive_axioms':dict(ax),'all_full_types_without_elision':True,'print_axioms_commands':66,'forbidden_source_tokens':source_scan,'audit_module_not_mathematical_origin':True},indent=2))
receipts=[json.loads(p.read_text()) for p in sorted(O.glob('*.receipt.json'))];(O/'all-receipts.json').write_text(json.dumps(receipts,indent=2));print('integrity',len(f),len(before),'inventory',len(rows),'mathlib',rev)
