"""Observe protected originals, replay read-only checks, then seal this review once."""
import datetime, hashlib, json, pathlib, runpy, subprocess, sys
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
AUTHOR=PROJECT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r102'
assert not (ROOT/'FINAL.json').exists() and not (ROOT/'MANIFEST.json').exists(), 'production seal already exists'
ns=runpy.run_path(str(ROOT/'verify.py'))
digest,inventory=ns['digest'],ns['inventory']
def snapshot(root):
    out={}
    for p in sorted(root.rglob('*')):
        s=p.lstat();out[str(p.relative_to(root))]={'mode':s.st_mode,'nlink':s.st_nlink,'size':s.st_size,'sha256':digest(p) if p.is_file() else None}
    return out
before=json.loads((ROOT/'private/original-before.json').read_text())
after=snapshot(AUTHOR)
assert before==after, 'author original changed since initial observation'
(ROOT/'private/original-after.json').write_text(json.dumps(after,indent=2)+'\n')
external_before=json.loads((ROOT/'private/external-originals-before.json').read_text())
external_after=[]
for a in external_before:
    h=digest(PROJECT/a['original'])
    external_after.append({**a,'after_sha256':h,'unchanged_during_review':h==a['current_sha256']})
(ROOT/'private/external-originals-after.json').write_text(json.dumps(external_after,indent=2)+'\n')
r73=json.loads((ROOT/'private/r73-receipt.json').read_text())
assert digest(PROJECT/r73['original'])==r73['sha256']==digest(ROOT/'private/r73-reading-and-credit.md')
author_anchors={'final':'eb35ddaa80501311da50e8f65d67dc33c970530e3b00003188182b2f8ef9e34f','manifest':'e212b8f45f7fb8ae07e30ba292ea8bab83c8983c0d3311f2bd308c0a590f8a9f','report':'9d5253a754956107d1920df6d67353a1169ad54b5d7f7d5bc40d7331fe35c8c2'}
replays=[]
for target in [AUTHOR,ROOT/'private/author-copy']:
    cmd=[sys.executable,'-B',str(target/'verify.py'),'--root',str(target)]
    for key,h in author_anchors.items():cmd+=['--'+key+'-sha256',h]
    result=subprocess.run(cmd,capture_output=True,text=True)
    assert result.returncode==0,result.stderr
    replays.append({'root':str(target),'returncode':result.returncode,'stdout':result.stdout.strip(),'stderr':result.stderr.strip()})
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'whole_author_original_unchanged':True,'author_anchors':author_anchors,'author_replays':replays,'external_named_current_originals_unchanged':sum(x['unchanged_during_review'] for x in external_after),'external_named_original_count':len(external_after),'matches_author_acquisition_before':sum(x['matches'] for x in external_before),'r73_current_copy_and_original_match':True,'limits':'Exact author original tree before/after and named external file observations only. Parent navigation may drift; no whole-workspace or historic preservation assertion.'}
(ROOT/'private/preservation.json').write_text(json.dumps(receipt,indent=2)+'\n')
(ROOT/'REPORT.md').write_text('''# T009P102 independent contribution review, round 1

**TECHNICAL, conditional on correctness, for the entire unchanged Theorem T and Proposition I jointly.**

The constructive reduction in public/REVIEW.md covers every prime, every finite n>=1, the named algebraically closed bases, the actual field map without extra Frobenius identification, and every arbitrary linearized endomorphism in the full finite-p-rank scope of I. It does not assume that n=1 isomorphism classification implies tangent rigidity. The source determinant pairing evaluates the mixed relation as B=rA in every transverse Euler coordinate, with r=f/(1+f), Dr=0 and r^p!=r. The credited classical logarithmic-derivative corollary kills those coordinates. The source monomial-kernel, independent-pair and eigenvector operations then give a single F_p scalar. Classical p-torsion-freeness and the written last-layer expansion, normalization, induction and uniqueness give the entire finite-level theorem. This joint construction is assessed as a technical composition of the actual available operations, not graded by proof length or parameter change alone.

The review includes the full-scope obligation map and C1-C7 responses. It credits the actual source intersection/exponent/global-scalar/projective reconstruction proofs, Jacobson III.12 necessity/characterization and the Cartier primary of Seshadri, Geisser-Levine Theorem8.1, the full Cadoret-Pirutka Lemma23/Proposition27/Section3.6 integral descent, and the strongest inspected local/global mod-ell and pro-ell interfaces at their compatible hypotheses. Integral quotient lifts, exact algebraic-dependence structure, top-field Kummer characteristic restrictions and coherent towers are not assumed. The r97 precursor is retained verbatim privately as an earlier author suggestion, not adopted as a prior independent verdict. The old r24/r97/r98 Hom scopes are unchanged.

This is an independent contribution verdict only. No independent full correctness gate has occurred; no correctness PASS, acceptance, campaign count, priority, formal, manuscript, release or publication gate is issued. No author repair or scope edit was made. Parent alone adopts the verdict and requests later work. No matching full-scope primary theorem was established in the bounded reads; that observation is not the basis for substantiality or worldwide priority.

public/READINGS.md records actual proof extents, versions, the imperfect Cartier OCR and visual recovery, author freeze/late-read chronology, independent searches, failed guessed path, truncation recoveries and access limits. The first broad filename inventory failed to prune active-directory names at every depth and exposed filenames; no active body was read. Subsequent traversals used explicit pre-descent exclusions. This error is disclosed rather than represented as compliance. Hidden/ignored/JSON/large and private/work history were included in the later saved searches without a size cutoff, with explicit corpus exclusions and overinclusive dependency/copied-log limits. Search hits and copied bytes are not semantic-read or absence certificates.

The sealed original author object matches the supplied full detached FINAL/MANIFEST/REPORT anchors, scope/proof hashes, and exact85-payload/21-directory inventory before and after review. Its inspected read-only verifier passes on the original and the independent retained copy, authenticating27 pinned bodies against the complete13223-entry tree/Git blobs/SHA256. private/preservation.json gives the final per-file boundary. Thirteen of fourteen named current originals matched author acquisition at entry; the mutable NEW-TEN ledger differed and was not a stable mathematical binding. Before/after observations do not demand whole-parent preservation. No source, primary, old-root or original author bytes were changed or resealed.

Original review prose/code/metadata are separate from protected primary/source/history/search/render evidence under private/. Nine proportionate copied preseal integrity fixtures behaved as expected; their trees were removed. They are artifact controls, not mathematical tests. The exact manifest includes scratch and all retained payload files/directories/modes. This outside REPORT is separately anchored; FINAL binds REPORT and MANIFEST and is itself externally anchored. The read-only verifier requires all three full detached hashes. No local-sidecar trust or hidden scratch exclusion substitutes for the handoff.

Runner: Codex / GPT-6.1-Sol / high / default service tier, user-authorized. All writes and temporary work were inside t009p102-contribution-r1/. No nested agents, git/staging/commit, shared edits, browser UI, contacts, uploads, submissions, downstream formal/manuscript/release or publication work occurred. Publication remains stopped.
''')
manifest=inventory(ROOT)
(ROOT/'MANIFEST.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
final={'task':'T009P102 contribution round1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':digest(ROOT/'MANIFEST.json'),'report_sha256':digest(ROOT/'REPORT.md'),'review_sha256':digest(ROOT/'public/REVIEW.md'),'scope_sha256':ns['SCOPE'],'contribution':'TECHNICAL_CONDITIONAL_ON_CORRECTNESS','correctness_gate':'NOT_PERFORMED','parent_adoption':'PARENT_DECISION','author_anchors':author_anchors,'payload_files':len(manifest['files']),'payload_directories':len(manifest['directories']),'source_pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','source_operations':'STIPULATED_TRUE'}
(ROOT/'FINAL.json').write_text(json.dumps(final,sort_keys=True,indent=2)+'\n')
anchors={key:digest(ROOT/name) for key,name in [('final','FINAL.json'),('manifest','MANIFEST.json'),('report','REPORT.md')]}
cmd=[sys.executable,'-B',str(ROOT/'verify.py'),'--root',str(ROOT)]
for key,h in anchors.items():cmd+=['--'+key+'-sha256',h]
p=subprocess.run(cmd,capture_output=True,text=True)
assert p.returncode==0,p.stderr
print(json.dumps({'anchors':anchors,'verification':json.loads(p.stdout),'preservation':{key:receipt[key] for key in ['whole_author_original_unchanged','external_named_current_originals_unchanged','external_named_original_count']}},indent=2))
