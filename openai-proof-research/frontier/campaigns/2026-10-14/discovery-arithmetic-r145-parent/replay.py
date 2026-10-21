#!/usr/bin/env python3
"""Read-only Arithmetic145 detached-anchor intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,re,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r145'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'788e8ecded67f4f9be0c6617aab005b75b28b691ea9863c7beda7834bf408d11','MANIFEST.json':'dc40310a0c2adbce3f12ced6961fe16aec6bcc55028d4dbd2f798eeb4b3df7e5','REPORT.md':'77026568713ca9c1242ba706ded3da42dd83eb3f5ba4cdfa8ba2389b94d1bc9e'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify.py'),'--root',str(ROOT),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and json.loads(r.stdout)=={'artifact_verification':'matched','payload_files':92,'mathematical_gate':False}
    m=read(ROOT/'MANIFEST.json');assert len(m['files'])==92;names={x['path']for x in m['files']};assert {p for p,x in before.items()if x['kind']=='file'}==names|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';canonical=read(ROOT/'private/source-bindings.json');assert len(canonical)==21
    for x in canonical:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['canonical']];assert p.resolve().is_relative_to(ROOT)and len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};reading=(ROOT/'private/READING.md').read_text();completed=re.findall(r'^\| (discovery-arithmetic-r144-parent/assessment.md|fresh-arithmetic-discovery-r144/[^|]+?) \| (\d+) \| ([a-f0-9]{64}) \|$',reading,re.M);assert len(completed)==6
    for path,size,digest in completed:
        p=B/path;assert p.stat().st_size==int(size)and sha(p)==digest;stable[p.relative_to(P).as_posix()]=digest
    sections=[]
    for x in read(ROOT/'private/original-extents.json'):
        p=P/x['path'];assert sha(p)==x['original_sha256'];copy=P/x['copy'];assert copy.resolve().is_relative_to(ROOT)
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['stop']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256']and data==copy.read_bytes();stable[x['path']]=sha(p);sections.append({'path':x['path'],'start':x['start'],'end':x['stop'],'selection_sha256':x['sha256'],'late':x.get('late',False)})
    assert len(sections)==13 and len(stable)==12 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':92,'outside_envelopes':3,'canonical_objects':21,'completed_originals':6,'selected_original_sections':13,'stable_named_originals':stable,'history_section_anchors':sections,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete PREFREEZE/DERIVATIONS/UNRESOLVED/FINAL/REPORT/private SOURCE-OPERATIONS/READING/selection-limits/verifier. Actual source/primary/history semantic extents attributed to author. Named i31 whole-original digest explicitly supplied by author and matches the preserved unrelated user diff.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','completed_originals','selected_original_sections','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
