"""Create proportionate copied controls, then seal own main packet once."""
from pathlib import Path
import json,shutil,sys,hashlib
from verify_packet import inventory,verify,digest
ROOT=Path(__file__).resolve().parent

def seal(r):
    p=r/'MANIFEST.json';assert not p.exists(),'seal-once refusal'
    p.write_text(json.dumps({'schema':'r168-exact-payload-v1','payload':inventory(r)},indent=2)+'\n')
    return {n:digest(r/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
if __name__=='__main__':
    assert not (ROOT/'MANIFEST.json').exists(),'main already sealed'
    fixture=ROOT/'private/copied-control';fixture.mkdir()
    (fixture/'notes').mkdir()
    (fixture/'notes/calculation.md').write_bytes((ROOT/'notes/02-integrated-calculation.md').read_bytes())
    (fixture/'verify_packet.py').write_bytes((ROOT/'verify_packet.py').read_bytes())
    (fixture/'FINAL.md').write_text('Copied artifact controls only; no mathematical gate.\n')
    (fixture/'REPORT.md').write_text('Selection: own calculation note and verifier; no inherited manifest.\n')
    anchors=seal(fixture);results=[]
    def check(name,expect,aa=anchors):
        before=inventory(fixture)
        try:verify(fixture,aa);ok=True
        except (AssertionError,FileNotFoundError):ok=False
        assert before==inventory(fixture),'verifier wrote fixture'
        assert ok==expect,(name,ok,expect)
        results.append({'control':name,'accepted':ok,'expected':expect,'read_only':True})
    check('clean',True)
    p=fixture/'notes/calculation.md';original=p.read_bytes();p.write_bytes(original+b'\nmutation\n');check('changed',False);p.write_bytes(original)
    p.unlink();check('missing',False);p.write_bytes(original)
    pextra=fixture/'notes/.extra';pextra.write_text('extra');check('extra-hidden',False);pextra.unlink()
    for n in anchors:bad=dict(anchors);bad[n]='0'*64;check('wrong-'+n,False,bad)
    check('restored',True)
    (ROOT/'private/copied-control-results.json').write_text(json.dumps({'anchors':anchors,'results':results},indent=2)+'\n')
    anchors=seal(ROOT);result=verify(ROOT,anchors)
    print(json.dumps({'anchors':anchors,'verification':result,'controls':len(results)},indent=2))
