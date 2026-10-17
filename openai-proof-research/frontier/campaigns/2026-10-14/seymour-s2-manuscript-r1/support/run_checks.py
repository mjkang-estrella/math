"""Run both finite diagnostics from a clean public extraction. Original code MIT."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[1]
def require(condition,message):
    if not condition:raise ValueError(message)
def run(rel):
    p=subprocess.run([sys.executable,'-B',str(R/rel)],cwd=R,capture_output=True,text=True)
    require(p.returncode==0,rel+' failed: '+p.stderr)
    return json.loads(p.stdout)
def main():
    records=json.loads((R/'checker-identities.json').read_text())
    require({r['path'] for r in records}=={'support/inherited/author.py','support/inherited/reviewer.py','support/reviewer_portable.py'},'missing checker identity')
    for rec in records:
        data=(R/rec['path']).read_bytes()
        require(hashlib.sha256(data).hexdigest()==rec['sha256'] and len(data)==rec['bytes'],'changed checker '+rec['path'])
    # Exact relation between the preserved reviewer and portable adapter.
    source=(R/'support/inherited/reviewer.py').read_text()
    adapter=(R/'support/reviewer_portable.py').read_text()
    require(source[:source.index('def main():')] in adapter,'reviewer function drift')
    loops=source[source.index('    deletion=blowup=anchors=0'):source.index('    result=')]
    require(loops in adapter,'reviewer mathematical loop drift')
    author=run('support/inherited/author.py')
    require(author['boundary']=={'graphs':23664,'nonempty_subset_identity_cases':352224},'author boundary result drift')
    shortcut=author['invalid_shortcut_counterexample']
    require(shortcut['out_bitmasks']==[36,25,10,17,37,10] and shortcut['all_63_subset_deficits_nonpositive'] is True and shortcut['singleton_deficits']==[0,-1,0,0,-1,0],'shortcut result drift')
    reviewer=run('support/reviewer_portable.py')
    require(reviewer=={'deletion_endpoint_cases':15129,'blowup_subset_cases':198936,'anchor_exclusion_cases':151362},'reviewer result drift')
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS_ONLY','author':author,'reviewer':reviewer,'full_graph_proof_by_computation':False},indent=2))
if __name__=='__main__':
    try:main()
    except Exception as exc:print('CHECK FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
