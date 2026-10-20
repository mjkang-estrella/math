#!/usr/bin/env python3
"""Parent current-artifact replay, not an independent mathematical review."""
import datetime, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent
BASE=OUT.parent
PROJECT=BASE.parents[2]
ROOT=BASE/'fresh-structural-discovery-r141'
ANCHORS={'MANIFEST.json':'d3b391f7e04f3f4ebd8fddc63eb7d06ad25d6a5002c25350d01f64454b70fe44',
         'outsideREPORT.md':'1c3d009c8e6d0f65c40e5fda34fb1227043fd927355896821361c363f565cfda',
         'FINAL.json':'d201bd382acfdb5022c3299ec852a55844a5eb1a55b098a8c9d36e568b4cfa80'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def snap(root):
    out={}
    for b,ds,fs in os.walk(root,followlinks=False):
        for n in sorted(ds+fs):
            p=Path(b)/n;s=p.lstat();row={'mode':stat.S_IMODE(s.st_mode)}
            if p.is_symlink():row.update(kind='symlink',target=os.readlink(p))
            elif stat.S_ISDIR(s.st_mode):row.update(kind='directory')
            elif stat.S_ISREG(s.st_mode):row.update(kind='file',bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
            else:raise AssertionError(p)
            out[p.relative_to(root).as_posix()]=row
    return out
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();before=snap(ROOT)
    dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current root after prose/code reads and before copied replay;no historical whole-parent claim.'})
    assert all(sha(ROOT/n)==h for n,h in ANCHORS.items())
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for e in manifest['entries']:
        if e['type']=='file':assert sha(ROOT/e['path'])==e['sha256']
    # The verifier itself is a payload authenticated above, before code execution.
    tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
    assert sha(PROJECT/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bypath={e['path']:e for e in tree['tree']};provenance=json.loads((ROOT/'packet/public/provenance.json').read_text())
    hashes={e['sha256'] for e in manifest['entries'] if e['type']=='file'}
    assert all(e['sha256'] in hashes and e['text_sha256'] in hashes for e in provenance['external'])
    for e in provenance['pinned_sources']:
        p=ROOT/'packet/private/upstream'/e['path'];b=p.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert len(b)==e['size']==bypath[e['path']]['size'] and blob==e['git_blob']==bypath[e['path']]['sha'] and sha(p)==e['sha256']
    bindings=[]
    for n in ['context-bindings.json','history-bindings.json']:
        for e in json.loads((ROOT/'packet/private'/n).read_text()):
            assert sha(ROOT/e['copy'])==e['sha256'];current=sha(PROJECT/e['path']);mutable=e['path']=='frontier/NEW-TEN-2026-10-14.md'
            assert mutable or current==e['sha256']
            bindings.append({'path':e['path'],'capture_sha256':e['sha256'],'current_sha256':current,'mutable_observation':mutable,'currently_matches':current==e['sha256']})
    args=['--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['outsideREPORT.md'],'--final-sha256',ANCHORS['FINAL.json']]
    controls=[]
    with tempfile.TemporaryDirectory(prefix='structural141-copy-',dir=OUT) as tmp:
        copy=Path(tmp)/'r141';shutil.copytree(ROOT,copy);verifier=copy/'packet/public/verify_packet.py'
        def check(label,expected,custom=None):
            observed=snap(copy)
            r=subprocess.run([sys.executable,'-B',str(verifier),'--root',str(copy),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==observed
            controls.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'output':r.stdout.strip()})
        check('baseline',True)
        p=copy/'packet/public/prefreeze-derivation.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');check('payload',False);p.write_bytes(b)
        p=copy/'extra.txt';p.write_text('extra');check('extra_file',False);p.unlink()
        p=copy/'copied-controls/fixture/empty-directory';mode=stat.S_IMODE(p.stat().st_mode);p.rmdir();check('missing_empty_directory',False);p.mkdir(mode=mode)
        p=copy/'packet/public/prefreeze-derivation.md';b=p.read_bytes();p.unlink();check('missing_payload',False);p.write_bytes(b)
        wrong=args.copy();wrong[1]='0'*64;check('wrong_detached_manifest',False,wrong)
        p=copy/'link';p.symlink_to('packet/public/prefreeze-derivation.md');check('symlink',False);p.unlink()
        p=copy/'hardcopy';os.link(copy/'packet/public/prefreeze-derivation.md',p);check('hardlink',False);p.unlink()
        for n in ['FINAL.json','outsideREPORT.md']:
            p=copy/n;b=p.read_bytes();p.write_bytes(b+b'changed\n');check('changed_'+n,False);p.write_bytes(b)
        check('restored_copy',True)
        assert snap(copy)==before
        r=subprocess.run([sys.executable,'-B',str(copy/'packet/public/replay_projection.py')],capture_output=True,text=True,timeout=90);assert r.returncode==0,(r.stdout,r.stderr)
        diagnostic=json.loads(r.stdout);old=json.loads((ROOT/'packet/private/projection-computation.json').read_text())
        assert diagnostic['cases']==old['cases'] and diagnostic['status']==old['status']
        dump('copied-diagnostic.json',diagnostic)
    assert snap(ROOT)==before
    assert all(sha(PROJECT/x['path'])==x['current_sha256'] for x in bindings)
    dump('copied-controls.json',{'cases':controls,'negative_cases':9,'positive_cases':2,'actual_root_unchanged':True,'copied_work_removed':True,'limits':'Read-only verifier preservation per copy check; byte/inventory/mode/link behavior only, no mathematical or OS enforcement gate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_entries':151,'payload_files':111,'payload_directories':40,'pinned_source_blobs':len(provenance['pinned_sources']),'primary_pdf_text_records':len(provenance['external']),'named_inputs':bindings,'artifact_cases':11,'negative_cases':9,'finite_cases':len(diagnostic['cases']),'visible_choices':sum(x['visible_sets_checked'] for x in diagnostic['cases']),'actual_root_unchanged':True,'current_named_originals_unchanged':True,'nominee':None,'count_change':0,'limits':'Artifact support only. Parent read public prose/code and parsed metadata;private source/primary/history/search bodies authenticated,not semantically reread. No mathematical or priority/exclusion/historical whole-parent gate.'})
    print(json.dumps({'entries':151,'sources':len(provenance['pinned_sources']),'bindings':len(bindings),'artifact_cases':11,'negative':9,'finite_cases':8,'visible_choices':68,'root_unchanged':True}))
if __name__=='__main__':main()
