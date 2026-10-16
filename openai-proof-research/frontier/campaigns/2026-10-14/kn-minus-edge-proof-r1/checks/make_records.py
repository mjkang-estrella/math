"""Review provenance/manifests. Original code: Myeongjin Kang, MIT."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import platform

BASE = Path(__file__).resolve().parents[1]
ROOT = BASE.parents[3]
FROZEN = BASE.parent / 'fresh-substantial-discovery-r2'

def describe(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

def write(name, value):
    (BASE/name).write_text(json.dumps(value, indent=2)+'\n')

inputs = {FROZEN/'input-manifest.json',FROZEN/'output-manifest.json'}
for name in ('input-manifest.json','output-manifest.json'):
    manifest = json.loads((FROZEN/name).read_text())
    for entry in manifest['files']:
        path = FROZEN/entry['path']
        actual = describe(path)
        assert actual['bytes'] == entry['bytes']
        assert actual['sha256'] == entry['sha256']
        inputs.add(path)
inputs.update(ROOT/p for p in ('AGENTS.md','sources/upstream.json','sources/CONTENTS.md',
                              'sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md'))
write('input-manifest.json',{'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                           'files':[describe(p) for p in sorted(inputs)]})
write('provenance.json',{
    'recorded_utc':datetime.now(timezone.utc).isoformat(),
    'review_role':'Independent adversarial proof reviewer; not author of the frozen candidate',
    'review_model':'GPT-6.1-Sol/high; normal speed; no delegated agents',
    'author':{'name':'Myeongjin Kang','affiliation':None},
    'rights':{'original_review_prose':'CC BY 4.0','original_review_code':'MIT',
              'third_party':'Original authors and rights preserved; no blanket relicensing'},
    'verdict':'PASS',
    'scope':'Full Theorem A (all n>=2, every missing edge, ordinary crossing number), full Corollary B (m>=4,n>=1,path n edges)',
    'required_mathematical_repairs':[],
    'assumptions':['Pinned OpenAI mathematics at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true by user',
                   'Normal citation of Ouyang-Wang-Huang 2014 Corollary 5.1; exact scope checked in retained primary text'],
    'read_extent':{
        'AGENTS.md':'full; no other applicable AGENTS files found',
        'sources/upstream.json':'full',
        'frontier/NEW-TEN-2026-10-14.md':'full; current 4/10 includes accepted R026; no count changed',
        'sources/CONTENTS.md':'family 165 excerpt only',
        'sources/preprints-tree.json':'programmatic exact main.tex blob entry lookup, not full text reading',
        'frozen/candidate.md':'full, 182 lines, 23029 bytes, specified SHA-256 confirmed',
        'frozen/source-contracts.md':'full',
        'frozen/README.md':'full',
        'frozen/provenance.json':'full',
        'frozen/input-manifest.json':'full; every entry checked',
        'frozen/output-manifest.json':'full; every entry checked',
        'frozen/checks/kn_minus_e_checks.py':'full source and output; successful full rerun in owned directory',
        'frozen/checks/kn_minus_e_modp_large.py':'full source and output; audited modular arithmetic and overflow bounds; no full rerun',
        'frozen/sources/upstream/kn/main.tex':'full actual 943-line source; source hypotheses/interfaces checked, theorem truth stipulated',
        'frozen/sources/upstream/kn/README.md':'full',
        'frozen/sources/literature/owh-2014-sciencedirect-fetch.txt':'primary-text sections 1-5 through Corollary 5.3 read; relevant hypotheses, definitions, statements and derivations read; references list not fully read',
        'frozen/sources/literature/clancy.txt':'only lines 545-570 and 1134-1150, context only',
        'other_frozen_input_files':'bytes/hash authentication only; no claim of mathematical reading of Borsuk, Sadhu, Schaefer, or bipartite companion files'
    },
    'fresh_source_download':json.loads((BASE/'sources/upstream-authentication.json').read_text()),
    'primary_literature':{
        'citation':'Z. Ouyang, J. Wang, Y. Huang, Discrete Mathematics 328 (2014), 71-78',
        'doi':'https://doi.org/10.1016/j.disc.2014.03.011',
        'source':'Authenticated frozen publisher full-text extraction; not survey-only',
        'locators':{'path_convention':264,'upper_theorem':288,'lower_theorem':300,'corollary':310,'derivation':314},
        'hypotheses':'K_m vertex transitive, at least four dominating vertices for m>=4; n>=1; P_n n edges',
        'conditional_dependency_found':False,
        'live_retrieval_status':'Fresh web and urllib attempts returned HTTP 403; not represented as a successful live source authentication',
        'published_proof':'Cited normally; no claimed full re-audit of zip-product antecedents'
    },
    'computations':{
        'python':platform.python_version(),
        'author_stdlib':'All result lines match original; no bytecode written to frozen directory',
        'independent':json.loads((BASE/'checks/adversarial.json').read_text()),
        'reviewer_control_development':'Early logs retain failed overstrong nonzero expectations for inadmissible tests. Uncrossed missing edge at n=15 had zero full-drawing crossings; some invalid tests vanish even on a crossed missing edge. Final assertions distinguish sufficiency from a nonexistent converse.',
        'certificate_scope':'Finite exact/modular support only; event-sign wiggle model is not an exported drawing; no full theorem formalization'
    },
    'formalization':'Core identified in review; no Lean proof produced or claimed',
    'actions':{'writes_only':str(BASE.relative_to(ROOT)),'frozen_inputs_unchanged':True,
               'shared_indexes_edited':False,'stage_or_commit':False,'public_action':False,
               'messages_to_others':False,'subagents':False,'acceptance_or_count_change':False},
    'boundaries':'Contribution, priority, manuscript and campaign acceptance remain separate gates'
})
outputs = [p for p in BASE.rglob('*') if p.is_file() and p.name!='output-manifest.json']
write('output-manifest.json',{'self_excluded':True,'files':[describe(p) for p in sorted(outputs)]})
print(json.dumps({'inputs':len(inputs),'outputs':len(outputs),'verdict':'PASS'}))
