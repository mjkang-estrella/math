#!/usr/bin/env python3
"""Create I38-owned provenance records. Never writes a sealed dependency.

Run only before artifact sealing. Verification uses verify.py instead.
"""
import datetime
import hashlib
import html
import json
import re
from pathlib import Path
from audit import ROOT, S, CORPUS, MANIFEST, sha, screen_prior_project


def save(name, obj):
    (S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')


def main():
    assert not (S/'artifact-seal.json').exists(), 'Artifacts are sealed; do not regenerate provenance'
    records = []
    def passage(path, intervals, role):
        data = path.read_bytes()
        lines = data.decode('utf-8').split('\n')
        rows = []
        for first,last in intervals:
            last = min(last,len(lines))
            selected = '\n'.join(lines[first-1:last])
            rows.append({'first_line':first,'last_line':last,'sha256':sha(selected.encode()),'opening_anchor':selected[:180]})
        records.append({'path':str(path.relative_to(ROOT)),'sha256':sha(data),'line_convention':'1-based LF-delimited, inclusive','role':role,'passages':rows})
    pinned = json.loads((S/'pinned-manifest.json').read_text())
    full_reads = []
    for f in pinned:
        path = f['path']
        g = 'The-Gaussian-Propeller-Bound' in path
        selected = g and (path.endswith('/main.tex') or any(path.endswith('/'+n+'.tex') for n in ['extremizers','scalars','geometry','elimination','certificates','references']))
        selected |= 'The-symmetric-Mahler' in path and path.endswith('/introduction.tex')
        selected |= 'Equality-cases-in-the-sharp-one-dimensional' in path and any(path.endswith('/'+n+'.tex') for n in ['introduction','action','compactness','rigidity'])
        selected |= 'Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials' in path and path.endswith('/action-limit.tex')
        if selected:
            full_reads.append(path)
            passage(CORPUS/path,[(1,10**9)],'Full relevant source file read; external inputs remain explicit premises, not re-audited upstream truth')
    d = S/'literature'
    primary = {
        'hjn-author.txt':([(1,210),(327,437),(562,655),(810,890),(1525,1560),(1690,1775)],'Three-dimensional sharp theorem and explicit uniqueness remark; selected proof/exclusion passages, not a fresh replay of the computer proof'),
        'hjn-v2.txt':([(1280,1553)],'Version comparison and relevant finite-dimensional proof segment; this version omits author Remark 1.4'),
        'kn-author.txt':([(1690,1850),(1980,2100)],'Full merging/simplicial reduction passage and Gaussian-maxima duality'),
        'kim-v1.txt':([(1,140),(2191,2280)],'Explicit local linear remainder and final assembly of main proof; intermediate polytope lemmas not all semantically read'),
        'fgl-v2.txt':([(130,360),(1050,1160),(1970,2300)],'Bubble decomposition statement, nonvanishing and full relevant two-bubble binding operation; not its whole concentration-compactness proof'),
        'corthree-author.txt':([(225,282),(978,1180)],'Three-cell theorem and angular inequality proof, compared separately with arXiv v3'),
        'corthree-v3.txt':([(2018,2141),(2280,2450),(2600,2725)],'Circular rearrangement and quantitative positive/negative proof estimates (53),(65)'),
        'smallcorr-current.txt':([(300,340)],'Main dimension-reduction interface and application, selected passages only'),
        'hyperstable-v1.txt':([(156,220)],'Theorems 1.5 and 1.7 retain hyperstability and finite cell hypotheses'),
        'stable-author.txt':([(1,370),(418,457),(2670,2840)],'Moment penalty and quantitative predecessor explicitly located; closing second-variation lemma read'),
        'hei14-author.txt':([(450,715),(2140,2225)],'Complete strongest direct quantitative three-cell proof: Lemmas 2.5-2.8 and closing discussion'),
        'robust-v1.txt':([(140,285)],'Single-set robust Borell theorem and proof-method scope; full proof not read')
    }
    for name,(intervals,role) in primary.items():
        passage(d/name,intervals,role)
    save('read-passages.json',records)
    save('read-scope.json',{'full_pinned_operation_files':full_reads,'other_pinned_manifest_entries':'Mechanically screened/identified, not all read semantically. General Mahler and scalar LT companions are retained for scope/provenance; no theorem unique to them is a proof premise.','corpus_coverage':'9340 files byte-verified and normalized-whitespace regex searched; not a claim of reading 749 full manuscripts.','primary_coverage':'Exact selected ranges and role descriptions in read-passages.json. Strongest direct earlier stability proof (Heilman 2014 Lemma 2.8) read in full.','visual_QA':'HJN author PDF pages 3 and 28 and Kim v1 page 2 rendered and inspected; no visual figure is a new theorem certificate.','initial_exploratory_web_batch':'Not retained; six subsequent complete numbered query/response records are sealed.','original_project_search':'prior-project-screen.json is the initial search. prior-project-screen-current.json repeats the broader mechanical screen near handoff and records eligible-file hashes. Neither claims semantic full reading.'})
    dep = {'path':str(MANIFEST.relative_to(ROOT)),'sha256':sha(MANIFEST.read_bytes()),'bytes':MANIFEST.stat().st_size,'mutable':False,'role':'Read-only complete reused text-corpus manifest; per-file Git and SHA identities are also rechecked'}
    save('external-dependencies.json',[dep])
    versions = []
    for p in sorted(d.glob('*current.html')):
        text = re.sub(r'\s+',' ',html.unescape(re.sub(r'<[^>]+>',' ',p.read_text())))
        pos = text.find('Submission history')
        history = text[pos:text.find('Full-text links:',pos)] if pos>=0 else 'NOT FOUND'
        found = re.findall(r'\[v(\d+)\]',history)
        versions.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p.read_bytes()),'submission_history':history,'latest_version':max(map(int,found)) if found else None})
    save('versions.json',{'retrieved_as_part_of':'Fresh I38 primary requests; use each download manifest for exact request/response times and headers','arxiv_records':versions,'version_discrepancies':['HJN author PDF explicitly has Remark 1.4 uniqueness; arXiv v2 omits it. The author version is the equality premise.','Corthree author PDF and arXiv v3 differ in quantitative coefficients; only common three-cell scope used.','Stable author PDF and arXiv v1 are separate byte identities; author version passages were read.','Smallcorr PDF fetched unversioned; its first-page banner identifies v2, consistent with abs submission history.'],'failures':[{'file':'fgl-published.pdf','status':403,'use':'Excluded from proof; retained HTML error bytes and response metadata'},{'file':'fgl-v3.pdf','status':404,'use':'Incorrect version guess; corrected from current abs to successful v2; excluded from proof'}],'local_tool_failures':['Optional bs4 import was unavailable; version extraction uses standard-library HTML stripping.','Optional sympy import was unavailable; exact diagnostics use standard-library rational polynomial arithmetic.','An initial G/scalars.tex read used the wrong directory; corrected to G/build/sections/scalars.tex.']})
    prior = screen_prior_project()
    prior['recorded_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save('prior-project-screen-current.json',prior)
    print(json.dumps({'full_pinned_reads':len(full_reads),'read_records':len(records),'prior_files_scanned':prior['files_scanned'],'prior_matching_lines':len(prior['matches'])},indent=2))


if __name__ == '__main__':
    main()
