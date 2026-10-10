"""Author acquisition finalization. This writes only the assigned I74 paths.
Never invoked by verify.py. Does not change any prior evidence or seal.
"""
from pathlib import Path
import hashlib,json,re,runpy,subprocess,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i74_relative_symplectic_packing'
E=Path(__file__).resolve().parent
OLD=ROOT/'frontier/sources/i70_symplectic_geometry_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

def main():
    versions=[]
    for p in sorted((S/'primary').glob('*-abs.json')):
        r=json.loads(p.read_text());identity=p.name[:-9]
        body=(p.parent/r['body']).read_bytes();v=max(map(int,re.findall(re.escape(identity)+r'v(\d+)',body.decode())))
        versions.append({'arxiv':identity,'latest_observed':v,'record':str(p.relative_to(ROOT)),'body_sha256':sha(body),'versioned_record':str((p.parent/(identity+f'v{v}-html.json')).relative_to(ROOT))})
    write(S/'current-versions.json',versions)
    bindings=[]
    def bind(p,a,b,purpose):
        data=p.read_bytes();lines=data.splitlines(keepends=True);assert 1<=a<=b<=len(lines),(p,a,b,len(lines))
        bindings.append({'path':str(p.relative_to(ROOT)),'first_line':a,'last_line':b,'file_sha256':sha(data),'passage_sha256':sha(b''.join(lines[a-1:b])),'purpose':purpose})
    oldpass=json.loads((OLD/'passages.json').read_text())
    for i in list(range(12))+[30]:
        x=oldpass[i];bind(OLD/x['path'],x['first_line'],x['last_line'],'Audited source operation: '+x['purpose'])
    P=S/'primary'
    selections=[('2312.13224v1-html.txt',272,331,'Shrink and varying-class deformation, Propositions 2.3-2.4'),
    ('2011.03317v2-html.txt',537,602,'Actual dimension-four connectivity/inflation and different-domain countermodels'),
    ('1112.1149v1-html.txt',35,84,'Weaker arXiv-v1 definitions and stability statements; superseded in part by published version'),
    ('1112.1149v1-html.txt',233,270,'v1 polarization and ellipsoid induction'),
    ('bh-published-pdf.txt',44,140,'Published open-ellipsoid conventions, Remark 1.2 and Theorems 1.1/1.3/1.5'),
    ('bh-published-pdf.txt',344,377,'Published disjoint-ellipsoid common-axis suspension, Propositions 3.4-3.5'),
    ('bh-published-pdf.txt',474,575,'Published actual full fillings, equal-ball stability, and stronger Opshtein Theorem 4.5'),
    ('2211.15970v2-html.txt',386,420,'Kahler-type existence and closed-space orbit theorem'),
    ('2211.15970v2-html.txt',483,531,'Projective-space transitivity versus existence avoiding hyperplane'),
    ('2211.15970v2-html.txt',1375,1397,'Integrability and exceptional-normalization interface'),
    ('2211.15970v2-html.txt',1530,1585,'Actual blowdown/common-complex-structure and relative-Moser proof'),
    ('2509.15390v1-html.txt',66,110,'Dimension-four boundary theorem and nonautomatic full open limit'),
    ('2509.15390v1-html.txt',899,930,'Tame boundary-compatible packings and annulus subgraphs'),
    ('2509.15390v1-html.txt',1099,1135,'Actual Theorem B stratification and Morse-handle proof'),
    ('1404.4183v1-html.txt',44,107,'Strong unequal-ball stability, dimension restriction, singular-inflation and curve interface'),
    ('2307.01140v2-html.txt',65,113,'Boundary obstruction examples and compact-smooth boundary distinctions'),
    ('pin-5.body',1,75,'Newer hypersymplectic companion has real dimension four and positive-triple premise'),
    ('pin-6.body',1,75,'Embedded Seshadri surface companion and very-general nef classes')]
    for f,a,b,purpose in selections:bind(P/f,a,b,purpose)
    # Author PDF first pages have statements used only for scope comparison.
    t=(P/'hind-isotopies-pdf.txt').read_text().splitlines();j=next(i for i,l in enumerate(t) if 'Theorem 1.9.' in l)
    bind(P/'hind-isotopies-pdf.txt',1,min(j+35,len(t)),'Hind nonisotopy domains and ambient space; not ball-prefix RP')
    write(S/'passages.json',bindings)
    d=runpy.run_path(str(E/'diagnostics.py'))['main']();write(S/'diagnostic-results.json',d)
    r=subprocess.run([sys.executable,'-B',str(ROOT/'frontier/experiments/i70_symplectic_geometry_discovery/verify.py')],cwd=ROOT,text=True,capture_output=True)
    write(S/'i70-replay.json',{'command':['python','-B','frontier/experiments/i70_symplectic_geometry_discovery/verify.py'],'returncode':r.returncode,'stderr':r.stderr,'result':json.loads(r.stdout)})
    assert r.returncode==0
    print(json.dumps({'passages':len(bindings),'current_versions':len(versions),'diagnostic_groups':len(d['groups']),'i70_replay':r.returncode}))
if __name__=='__main__':main()
