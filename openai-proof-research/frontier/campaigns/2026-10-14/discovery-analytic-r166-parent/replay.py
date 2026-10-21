#!/usr/bin/env python3
"""Read-only exact selected author-packet authentication; not a mathematical review."""
import importlib.util, json, stat, subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-analytic-discovery-r166'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(A);root_mode=stat.S_IMODE(A.stat().st_mode)
    anchors={'FINAL.md':'4f05d30afddd2ded0bff86890708cd4a97ab8e0d475794dc9f6db0a29731b64b','private/MANIFEST.json':'e150294533d34bb603a9809a9a90d9db502575362f9d0c41b26a60bb8a49fb8e','REPORT.md':'e3c0a6fee124a78f670bbd2590b0b649196518a33a56f147a1fb4070a812673a'}
    result=json.loads(subprocess.check_output(['python','-I','-B',str(A/'private/verify_packet.py'),'--packet',str(A),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/MANIFEST.json'],'--report-sha',anchors['REPORT.md'],'--project',str(P)],cwd=P,text=True));assert result['artifact_integrity']=='consistent' and result['payload_files']==60 and result['canonical_objects']==9
    assert sha(A/'STATEMENT.md')=='c518b1e730585463899f83a6c1aa1023717817671ecdcd540245024745a1cd33'
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==root_mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':root_mode},indent=2)+'\n')
    original_paths=read(A/'private/direct-originals.json')['objects']+read(A/'private/original-selections.json');stable={e['original']:sha(P/e['original'])for e in original_paths}
    (O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':result,'statement_sha256':sha(A/'STATEMENT.md'),'author_proof_sha256':sha(A/'PROOF.md'),'whole_root_files':sum(x['kind']=='file'for x in before.values()),'whole_root_directories':sum(x['kind']=='dir'for x in before.values()),'whole_root_unchanged_after_readonly_verification':True,'stable_named_originals':stable,'private_manifest_and_protected_payload_remain_local':True,'mathematical_verdict':None},indent=2)+'\n')
    print(json.dumps({'artifact_replay':result,'statement':sha(A/'STATEMENT.md'),'proof':sha(A/'PROOF.md'),'whole_root_unchanged':True}))
if __name__=='__main__':main()
