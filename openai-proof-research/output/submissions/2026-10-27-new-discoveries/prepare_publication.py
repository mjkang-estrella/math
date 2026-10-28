#!/usr/bin/env python3
"""Prepare public publication copies; never upload, publish, or alter accepted archives."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import re
import shutil
import zipfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
CAMPAIGN = REPO / 'frontier/campaigns/2026-10-26/new-discoveries'
AUTHOR = 'Myeongjin Kang'
DATE = '2026-10-27'

# Publication summaries were checked against each actual accepted manuscript.
SUMMARIES = {
1: ('A sharp converse fractional-binomial inequality through log-convexity',
    'We prove the converse fractional-binomial inequality posed by Gerhold and Simon as Conjecture 3.2, together with a biased refinement and optimality of the coefficient. Log-convexity of a finite sum of scaled Gamma quotients and its values at parameters one and two give the comparison. The Gamma-convexity ingredient is classical and explicitly credited. The Lean certificate covers the precise source statement, refinement and sharpness.'),
2: ('Nonconvergence of randomized subtraction games with odd moves',
    'For every finite nonempty set of positive odd subtraction moves, with uniform choice among the legal moves, the probability of winning for the player to move does not converge as the heap grows. A positive finite-window invariant proves the result without a coprimality or root-simplicity assumption. This answers the separate all-odd nonconvergence assertion in Capitelli and Somma; the different MathDB root-simplicity conjecture is not resolved.'),
3: ('An exact counterexample to trigonometric positivity for square roots of geometric sums',
    'We refute Kovalev Conjecture 1.3 using d=49, partial-sum index 949 and t=arccos(523/527). A finite integer certificate proves strict negativity of the literal trigonometric sum from the normalized square-root Taylor coefficients. The coefficient recurrence, cosine bridge and source counterexample are proved in Lean. The separate zero-free conjecture and minimality are not claimed.'),
4: ('An odd-degree identity for polynomial values at derivative roots',
    'We prove Wojnar, Wojnar and Brin Conjecture 2 for every complex polynomial of odd degree, with derivative roots counted with multiplicity. Normalized Newton moments extend the means polynomially in the remaining degree; an apolar self-pairing and finite differences yield the identity. The literal source means and arbitrary-polynomial endpoint are proved in Lean. Classical Newton, apolarity and finite-difference ingredients are credited.'),
5: ("Four interior roots in Yuster's entropy polynomial",
    'At k=48, the canonically parameterized polynomial in Yuster Conjecture 3.9 has at least four distinct roots strictly between zero and one. Rational parameter enclosures and five exact sign checks give the certificate. Lean proves the literal coefficients, parameter condition, four real roots and root-count contradiction. No smallest example, exact total root count or refutation of the separate known entropy inequality is claimed.'),
6: ('Negative-order Vendi–LCR comparison without a full-rank assumption',
    'For finite positive semidefinite similarity matrices with diagonal one and entries between zero and one, we prove the uniform Vendi–LCR comparison at every negative order using the positive spectral support evidenced in the source implementation. A spectral Jensen argument also proves the directly defined minus-infinity endpoint. Classical Jensen and Holder–McCarthy inequalities and known nonnegative/full-rank cases are credited. No analytic order-limit theorem or weighted-distribution formal extension is claimed.'),
7: ('Unit-circle nonvanishing for rational Hartogs-triangle polynomials',
    'For every coprime pair m>n>=1, the polynomial in Edholm–Mathew Conjecture 4.20 has no root on the unit circle and exactly m-n roots in the punctured unit disc, counted with multiplicity. A finite coefficient reindexing gives a sum of squared floor-polynomial values, and an adjacent-polynomial difference makes it strictly positive. The source coefficient bridge and full polynomial theorem are proved in Lean; older kernel identities are credited.'),
8: ('Classical-mean power sums: the exact real-exponent ranges',
    'For the arithmetic, geometric, harmonic and quadratic means A,G,H,Q of two positive inputs, the inequality A^n+G^n<=Q^n+H^n holds universally exactly when n<=0 or n>=1. The reverse holds universally exactly at n=0. This gives one complete real-exponent classification resolving the published Mestrovic–Andjic conjecture, including strict failures in its asserted interval. Both classifications and the actual positive-input witnesses are certified in Lean.'),
9: ("A strict valley in Keith's multicolor partition array",
    'A three-color box-partition array for the 25 by 25 box at size 325 has three consecutive points on a line of step (1,-2) with coefficients 53130, 50600 and at least 52900. This refutes Keith\'s multicolor linear-cut unimodality conjecture. The actual generating polynomial and an injection establishing the last bound are proved in Lean. The original Dousse–Kim two-color conjecture remains untouched.'),
10: ('A Hermitian counterexample to C*-algebraic Novak positivity',
    'We construct four self-adjoint inputs with two coordinates in M_2(C) for which the literal exponential-defined Novak kernel is Hermitian but not positive semidefinite. An explicit quadratic form equals cos(pi*sqrt(15))-3 and is at most -2. This refutes Krishna\'s C*-algebraic extension; the scalar and commutative Novak theorems are unaffected. The matrix construction and exact failure are proved in Lean.'),
11: ('A cubic counterexample to three C*-algebraic polynomial inequalities',
    'One degree-three matrix construction refutes Krishna\'s C*-algebraic Schoenberg, de Bruin–Sharma and Kushel–Tyaglov conjectures. The ordered deletion derivative factors for every complex matrix argument, including noncommuting arguments. Both adjoint versions of each proposed inequality fail through exact negative quadratic forms. Lean proves the factorization and all six Hermitian failures. The common construction counts as one outcome; classical scalar results are unaffected.'),
12: ('Sharp maximal index for separately sorted arithmetic and geometric means in every dimension at least five',
    'For each probability vector in dimension d>=5, form and independently sort all d^2 ordered arithmetic means and all d^2 ordered geometric means. The sum of their respective largest k entries is at most d for every probability vector exactly when k<=2d-5. Incidence bounds, Cauchy–Schwarz and a sharpness family prove the classification. The complete separately sorted source statement is certified in Lean.'),
13: ('Positive diagonal concavity does not imply concavity for elementary-symmetric sums',
    'The four-variable polynomial f=1+2*sigma_1+sigma_2+2*sigma_3+sigma_4 has strictly positive coefficients and a diagonal fourth root concave on the entire positive axis, while f^(1/4) is not concave on the positive orthant. An exact identity and a strictly interior rational midpoint certificate refute Lachaume Conjecture 1. The literal elementary symmetric functions and regularity are proved in Lean. The older real-rootedness-converse failure is explicitly uncredited.'),
14: ('Sharp universal constants for the 3 by 3 permanental Koteljanskii ratio',
    'For every real strictly totally positive 3 by 3 matrix, the source permanental Koteljanskii ratio lies strictly between 2/3 and 9/8, and both constants are optimal. Positive scalings reduce the proof to two polynomial certificates; strictly totally positive families approach the bounds. The result answers the explicit optimal-constant question accompanying Skandera–Soskin Proposition 11. It does not resolve the separate MathDB Sihong conjecture or claim the known boundary example as new.'),
15: ('Strict connection–Dirac spectral dominance for every finite graph',
    'For every nonempty finite graph simplicial complex and each permitted k, the sum of the k largest connection-matrix eigenvalues exceeds the corresponding signed-Dirac sum by at least sqrt(2)-1. Isolates and disconnected graphs are included. This proves the entire dimension-at-most-one case of Knill\'s conjecture, not the higher-dimensional statement. All incidence, spectral and literal face-family bridges are proved in Lean; no optimal gap is claimed.'),
16: ('A continuous critical-branch obstruction to C*-algebraic Sendov conjectures',
    'A cubic over C([0,1],C) has roots of norm at most 9/10, a completely split derivative with two distinct continuous critical branches, and strictly positive continuous convex weights. Nevertheless every critical element has supremum distance greater than 21/20 from a fixed root. This refutes the published C*-Sendov Conjectures 3 and 4 as one common outcome. The scalar Sendov problem and the separate density-of-invertibles formulation are not formally claimed resolved.'),
17: ('Odd-total lower bound for simple SOC representations',
    'If positive integer weights have odd total, every literal simple second-order-cone representation of their weighted geometric mean has at least as many constraints as original variables. This answers Wang\'s 2024 Section 7 open question (2), rather than newly resolving the older cardinality bound in the related MathDB record. The proof initially allows repeated indices, self-loops and cycles; the structural and parity conclusions follow from soundness. The full representation endpoint is proved in Lean.'),
18: ('A fortieth-derivative obstruction to the Mills-ratio complete-monotonicity conjecture',
    'For the actual Gaussian Mills ratio r, the quotient -r^2/r\' has negative fortieth derivative throughout some interval of strictly positive regular inputs. This refutes Ferreira–Simon Conjecture 3 already at n=0. A degree-21 integer polynomial in pi/2, rational Bernstein bounds and continuity supply the certificate. The Gaussian tail, derivative identification and interior conclusion are proved in Lean. No minimal derivative order or contradiction of the square-root-input proposition is claimed.'),
19: ('All-order smooth realization of increasing repeated-integral endpoint jets',
    'We prove Burke–Haris–Madhavendra Conjecture 1.2 for every order, including order zero. An atomless Stieltjes measure has a strictly positive smooth density realizing its finitely many moments and equal to one near the endpoints. Separation, an explicit bump-moment openness argument and repeated integration give the full source endpoint-jet statement. All measure, kernel, openness and endpoint bridges are proved in Lean. Standard moment technology and the previously known low-order cases are credited.'),
20: ('Davis all-degree rational-function conjecture via a fourth-moment bound',
    'We prove Davis Conjecture 3.1 strictly throughout its stated degree and real-variable domain. A finite detailed-balance identity rewrites the source quotient through second and fourth moments. A general comparison covers degrees at least 43, and 38 exact polynomial certificates cover the remaining degrees. The explicit source equation-2.4 difference remainder and full bound are certified in Lean; Euclidean division is not separately formalized. No optimality or separate critical-point conjecture is claimed.'),
21: ('Uniform Burnside–Gautschi bound for interpolated gamma values',
    'Schmidlin Conjecture 37 holds strictly for every nonnegative base point and, more generally, every nonnegative interpolation parameter. A classical Stirling remainder bound, logarithmic entropy estimate and translated positive-discriminant certificate prove the comparison. The literal gamma-function expression, source domain and all supporting inequalities are proved in Lean. Classical estimates and the previously established x>=1 range are credited; no optimal constant is claimed.'),
22: ('All-order adjacent-count inequality for the flat Bernoulli game',
    'We prove the adjacent-count inequality in Hetyei Conjecture 6.10 for every n>=12. After factorial normalization, a renewal sequence has negative increments from index 11 onward. Symmetric arrowhead matrices, weighted power inequalities and exact finite checks propagate the sign. The literal ordered-composition factorial count and every spectral, recurrence and limit bridge are proved in Lean. The source sign typo, helpers and finite checks do not count as separate results.'),
23: ('Convexity of the Le Roy parameter threshold',
    'For every gamma>1, the literal positive-admissibility threshold in Simon\'s paper is convex on (0,1/gamma). Rescaling expresses it as a supremum of positive perspectives; finiteness and positivity identify that supremum with the source infimum. This resolves the separate threshold-convexity question at the end of Section 3. The main complete-monotonicity iff conjecture remains unclaimed. The exact infimum–supremum identification and convexity endpoint are proved in Lean.'),
24: ('An alternating Turán inequality for normalized Euler numbers',
    'We prove Sokal Conjecture 3.3 for every starting index n>=0 and positive shifts j,k, using the actual normalized Taylor coefficients of sec(t)+tan(t). Classical partial fractions, a uniform positive-error contraction and four parity cases establish the sign. The generating-function identity, all coefficient bridges and the complete source inequality are proved in Lean. Known subsequence results, partial fractions and finite experiments are credited rather than counted separately.'),
25: ('A failure of the DeTemple complete-monotonicity threshold',
    'We refute the sufficient direction of Yang–Chu–Zhang Conjecture 1(ii) at a strictly positive parameter strictly below 155/294. The literal gamma/digamma quotient violates a positive-input midpoint inequality, hence its proposed negative is not completely monotone. The existential strictly interior source refutation is proved in Lean; the separately calculated rational witness is mathematical evidence, not the formal endpoint. Part (i) and an exact replacement threshold are not claimed.'),
26: ('A Gaussian envelope for Hermite polynomials',
    'We prove Guo–Liu\'s full literal Hermite-envelope conjecture. A sine comparison gives enough strict energy loss in odd degree to attain the exact Gamma-normalized coefficient. A real-root moment inequality controls stationary peaks after the cutoff and supplies the clamped tail. Actual Rodrigues Hermite polynomials, the precise source cutoff and every assembly bridge are proved in Lean. Classical oscillator, Wallis and polynomial tools and known low/even-degree cases are credited.'),
27: ('Partition coefficients for generalized peakon transfer matrices',
    'We give a universal factorial formula for every partition coefficient in every positive trace power of the source generalized peakon Lax matrix, for all particle numbers. A curve-conditioned rank-two determinant collapse and the formal trace-log identity prove the formula and both printed families. Lean covers arbitrary coherent complex particle amplitudes and the literal square-root matrices at nonnegative real momenta. Classical determinant and multinomial tools and known families are uncredited as separate outcomes.'),
28: ('No finite C*-Smale mean-value constant at degree three',
    'Over the fixed connected algebra C([0,1],C), no finite constant controls the first-order Smale norm divided difference for all split monic cubics. For every proposed constant, a continuous cubic family has an invertible test derivative and exactly two existing critical elements, both violating the bound. The full quantified theorem is proved in Lean. This is a stronger infinite-constant theorem, not the first refutation of the scalar or C*-constant-one conjecture, which was publicly refuted before this work.'),
29: ('An injective C*-power series violating the Bieberbach coefficient bound',
    'A normalized norm-entire power series on C([0,1],C) is globally injective and has an everywhere norm-convergent formal derivative series, but its second coefficient violates the general C*-Bieberbach order bound. A continuous exponential period anchored at zero proves global injectivity without assuming univalent scalar fibers. Lean proves the full source Conjecture 1.2/1.4 counterexample as one common outcome. Invertible-coefficient, polynomial, Robertson and Lebedev–Milin variants remain unclaimed.'),
30: ('A two-term counterexample to Bessel–Fourier kernel positivity',
    'The literal order-zero modified Fejer kernel in Acosta Babb\'s published Conjecture 1 satisfies K_2^(2/5)(47/50)<-1/500. Both real parameters are strictly interior. Exact rational series and Bernstein bounds identify the genuine first two positive J0 zeros and prove the strict negative value in Lean. The complete certificate has 87 declarations in eight modules. Separate slow-decay existence questions, redundant half-power witnesses and numerical scans are not additional outcomes.')
}

COMMON = ('AI-assisted preprint by Myeongjin Kang, with no affiliation. Internal AI review is not external journal peer review. '
          'The accompanying Lean certificate covers the precise scoped main statement; inspect the formal endpoint, assumptions and provenance in the supporting package. '
          'Prior-art investigations are documented bounded searches, not worldwide-priority certification. '
          'Original prose is offered under CC BY 4.0 and original code/Lean under MIT; third-party rights and existing notices are preserved. '
          'The public supporting ZIP contains original proof sources and verification evidence, with bibliographic links and hashes instead of redistributed third-party source manuscripts.')

def sha(data): return hashlib.sha256(data).hexdigest()
def dumps(obj): return (json.dumps(obj, indent=2, ensure_ascii=False)+'\n').encode()

def archive_bytes(prefix, payload):
    stream=io.BytesIO()
    with zipfile.ZipFile(stream, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, blob in sorted(payload.items()):
            info=zipfile.ZipInfo(prefix+'/'+name, (2026,10,27,0,0,0))
            info.external_attr=0o100644<<16
            z.writestr(info, blob, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    return stream.getvalue()

def keep(name):
    p=PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts: raise ValueError(name)
    banned={'sources','source','novelty','novelty-r2','fresh','preliminary-inputs',
            'reviewed-originals','preliminary-originals','reviewed','build','paper-render','renders'}
    if any(x in banned for x in p.parts): return False
    if p.suffix in {'.pdf','.html','.png','.jpg','.jpeg','.svg','.woff','.xml','.txt'}:
        return name=='paper.pdf'
    if p.name in {'MANIFEST.json','MANIFEST.sha256','README.md','release-files.json',
                  'reviewed-file-locations.json'}: return False
    return p.suffix in {'.lean','.py','.md','.json','.log','.toml','.tex'} or p.name.startswith('LICENSE')

def main():
    previous=HERE/'submission-manifest.json'
    if previous.exists():
        old=json.loads(previous.read_text())
        for row in old.get('papers',[]):
            if any(row.get(k) for k in ['doi','zenodo_url','mathdb_url','zenodo_deposit_id','zenodo_draft_id']):
                raise RuntimeError('Refusing to overwrite live draft/publication receipts; resume submissions instead.')
            meta=Path(row['metadata'])
            if meta.exists():
                state=json.loads(meta.read_text())
                if state.get('submitted') or state.get('publicly_uploaded'):
                    raise RuntimeError('Refusing to overwrite submitted metadata: '+str(meta))
    ledger=json.loads((CAMPAIGN/'ledger.json').read_text())
    assert ledger['discovery_count']==30 and ledger['historical_count_credit']==0
    assert set(SUMMARIES)==set(range(1,31))
    rows=[]
    for entry in ledger['accepted']:
        number=entry['number'];slug=Path(entry['path']).name;tag=f'D{number:03d}'
        folder=HERE/(tag+'-'+slug);folder.mkdir(exist_ok=True)
        canonical=CAMPAIGN/entry['path'];original=CAMPAIGN/entry['packet']
        original_blob=original.read_bytes();assert sha(original_blob)==entry['packet_sha256']
        with zipfile.ZipFile(io.BytesIO(original_blob)) as z:
            assert z.testzip() is None
            manifest_name=next(n for n in z.namelist() if PurePosixPath(n).name in {'MANIFEST.json','MANIFEST.sha256'})
            prefix=manifest_name.rsplit('/',1)[0]+'/'
            if manifest_name.endswith('.json'):
                original_manifest=json.loads(z.read(manifest_name))
            else:
                original_manifest={line[66:]:line[:64] for line in z.read(manifest_name).decode().splitlines() if line}
            included={};omitted={}
            for name, digest in original_manifest.items():
                blob=z.read(prefix+name);assert sha(blob)==digest
                assert (canonical/name).read_bytes()==blob
                (included if keep(name) else omitted)[name]=blob if keep(name) else digest
        config=json.loads(included['candidate.json'])
        assert included['paper.pdf']==(canonical/'paper.pdf').read_bytes()
        for mod in config['modules']:
            name='formal/'+mod['module']+'.lean'
            assert included[name]==(canonical/name).read_bytes()
        for name in ['verification/pins.json','verification/verify_candidate.py']:
            assert name in included
        urls=set()
        for name,blob in included.items():
            if PurePosixPath(name).suffix in {'.md','.tex','.json'}:
                for url in re.findall(r'https?://[^\s<>"\]})]+',blob.decode(errors='replace')):
                    if not any(x in url.lower() for x in ['access_token=','api_key=','secret=']):
                        urls.add(url.rstrip('.,;'))
        # Bibliographic source URLs also occur in omitted factual JSON records.
        for f in (canonical/'sources').rglob('*.json'):
            if f.stat().st_size>500000: continue
            try: source=json.loads(f.read_text())
            except (ValueError,UnicodeError): continue
            if isinstance(source,dict):
                for key in ['source_url','url','documented_by_source_url','first_stated_year_source_url']:
                    url=source.get(key)
                    if isinstance(url,str) and url.startswith(('http://','https://')) and not any(k in url.lower() for k in ['access_token=','api_key=','secret=']):urls.add(url)
        title,abstract=SUMMARIES[number]
        description=abstract+'\n\n'+COMMON+'\n\nRecorded prior-art/source-access limits: '+entry.get('novelty_limit','See the original independent review.')
        publication={'campaign':'2026-10-26/new-discoveries','outcome_number':number,'title':title,
            'creator':AUTHOR,'affiliation':None,'prepared_date':DATE,'publication_status':'PREPARED_NOT_SUBMITTED',
            'exact_counted_scope':entry['scope'],'related_mathdb_id':entry.get('mathdb_id',entry.get('related_mathdb_id')),
            'related_mathdb_ids':entry.get('mathdb_ids'),'source_target':entry.get('source_target',entry.get('source_conjecture')),
            'original_accepted_archive_sha256':entry['packet_sha256'],'formal_declarations':entry['formal_declarations'],
            'formal_modules':len(config['modules']),'formal_module_hashes':{m['module']:sha(included['formal/'+m['module']+'.lean']) for m in config['modules']},
            'full_original_archive_preserved_locally':True,'public_package_changes':'Bibliographic/publication/licensing wrapper and omission of raw third-party source copies only; every formal module, verifier, pins and manuscript byte remains accepted.',
            'prior_art_limits':entry.get('novelty_limit'),'disclosure':COMMON}
        included['PUBLICATION.json']=dumps(publication)
        included['INTERNAL-ACCEPTANCE.json']=dumps(entry)
        included['SOURCE-REFERENCES.json']=dumps({'source_urls':sorted(urls),'omitted_original_archive_members_sha256':omitted,
            'note':'Excluded raw third-party manuscripts, web captures, screenshots and historical duplicate files are not required by the Lean replay. Their original hashes and bibliographic URLs are retained; this public ZIP is an explicit subset plus publication wrapper, not the frozen internal research archive.'})
        included['README.md']=(f'# {title}\n\n'+abstract+'\n\n'+COMMON+
            '\n\n## Exact scope\n\n'+entry['scope']+'\n\n## Replay\n\n'
            'Use the pinned Lean version and compiled mathlib/dependency revisions in verification/pins.json. From this extracted package run:\n\n'
            '    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages\n\n'
            'The proof module bytes, candidate.json, pins and verifier are unchanged from the accepted/replayed research package. Only propext, Classical.choice and Quot.sound are permitted. '
            'Reports and metadata may preserve historical preacceptance status; INTERNAL-ACCEPTANCE.json records the later scoped decision. '
            'No additional claims follow merely from a publication or an empty database record.\n\n'
            '## Provenance and source availability\n\n'
            f'Accepted internal archive SHA-256: {entry["packet_sha256"]}. Its source copies remain locally preserved. '
            'SOURCE-REFERENCES.json lists bibliographic links and excluded-member hashes. No removed raw third-party article is an input to the Lean proof. '
            'The public package has its own manifest and checksum; it is not represented as byte-identical to the larger internal archive.\n\n'
            '## Prior-art limits\n\n'+entry.get('novelty_limit','See reviews.')+'\n').encode()
        included['PUBLIC-LICENSES.md']=(
            '# Public package licensing\n\nOriginal prose, including the manuscript and original research/review notes, is offered under '
            'Creative Commons Attribution 4.0 International (CC BY 4.0): https://creativecommons.org/licenses/by/4.0/ . '
            'Original code and Lean are offered under the accompanying MIT license. These grants apply only to rights held by Myeongjin Kang; '
            'existing third-party notices and licenses prevail for third-party material. Bibliographic quotations and mathematical statements retain their applicable status. '
            'Lean/mathlib and other external dependencies keep their own licenses and are not relicensed here. '
            'Raw third-party manuscripts and web captures are omitted from this public package.\n').encode()
        included['LICENSE-ORIGINAL-CODE-MIT.txt']=(
            'MIT License\n\nCopyright (c) 2026 Myeongjin Kang\n\n'
            'Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files '
            '(the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, '
            'publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, '
            'subject to the following conditions:\n\nThe above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.\n\n'
            'THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF '
            'MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE '
            'FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION '
            'WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.\n').encode()
        if (canonical/'acceptance.json').exists():included['POST-REPLAY-ACCEPTANCE.json']=(canonical/'acceptance.json').read_bytes()
        included['MANIFEST.json']=dumps({n:sha(b) for n,b in sorted(included.items())})
        prefix=tag.lower()+'-'+slug
        public_blob=archive_bytes(prefix,included);assert public_blob==archive_bytes(prefix,included)
        pdf_name=prefix+'.pdf';zip_name=prefix+'-lean-proof.zip'
        (folder/pdf_name).write_bytes(included['paper.pdf']);(folder/zip_name).write_bytes(public_blob)
        with zipfile.ZipFile(io.BytesIO(public_blob)) as z:
            assert z.testzip() is None
            pm=json.loads(z.read(prefix+'/MANIFEST.json'))
            for n,h in pm.items():assert sha(z.read(prefix+'/'+n))==h
            assert not any(n.endswith(('.olean','.ilean')) for n in z.namelist())
            assert [n for n in z.namelist() if n.endswith('.pdf')]==[prefix+'/paper.pdf']
        meta={'title':title,'creators':[{'name':'Kang, Myeongjin'}],'resource_type':'publication-preprint',
              'description':description,'paper_license':'CC-BY-4.0','original_code_license':'MIT','language':'eng',
              'prepared_date':DATE,'publication_date':DATE,'zenodo_files':[str((folder/pdf_name).resolve()),str((folder/zip_name).resolve())],
              'mathdb_files':[str((folder/pdf_name).resolve())],
              'mathdb_comment':'Supporting package DOI: PENDING_ZENODO_PUBLICATION. '+COMMON,
              'publicly_uploaded':False,'submitted':False,'campaign_outcome':number,
              'exact_counted_scope':entry['scope'],'prior_art_limits':entry.get('novelty_limit'),
              'accepted_archive_sha256':entry['packet_sha256'],'pdf_sha256':sha(included['paper.pdf']),
              'public_zip_sha256':sha(public_blob),'public_package_members':len(included),
              'omitted_original_members':len(omitted),'all_formal_module_bytes_unchanged':True}
        (folder/'submission-metadata.json').write_bytes(dumps(meta))
        (folder/'submission-text.txt').write_text(title+'\n\nAuthor: '+AUTHOR+'\nAffiliation: none\n\n'+description+'\n')
        rows.append({'number':number,'slug':slug,'title':title,'directory':folder.name,'metadata':str((folder/'submission-metadata.json').resolve()),
                     'pdf':pdf_name,'pdf_sha256':meta['pdf_sha256'],'public_zip':zip_name,'public_zip_sha256':meta['public_zip_sha256'],
                     'accepted_internal_archive_sha256':entry['packet_sha256'],'publication_status':'PREPARED_NOT_SUBMITTED',
                     'zenodo_url':None,'doi':None,'mathdb_url':None})
    manifest={'user_instruction':'then now submit it like the others','scope':'All30 accepted new-discovery outcomes; same Zenodo PDF+supporting ZIP then MathDB paper workflow as prior submissions',
              'status':'PREPARED_NOT_SUBMITTED_BROWSER_ACCESS_REQUIRED','author':AUTHOR,'affiliation':None,'papers':rows,
              'integrity_checks':'All accepted archive hashes/CRC/payloads checked; all public PDF/module/verifier/pin bytes identical; public ZIP deterministic/readback/manifest PASS; raw third-party source copies omitted with hashes and bibliographic references retained.',
              'access_blocker':'Zenodo preview opened but snapshot/evaluate timed out after15000ms each; alternate cua browser inventory empty. No public upload or submission has occurred.'}
    (HERE/'submission-manifest.json').write_bytes(dumps(manifest))
    (HERE/'README.md').write_text('# Thirty new-discovery submissions\n\nStatus: prepared, not publicly uploaded or submitted. User authorized the established Zenodo and MathDB route. '
        'A working authenticated browser connection is currently required. The full metadata and upload files for all30 are listed in submission-manifest.json.\n\n'
        'Accepted research PDFs and proof sources are unchanged. Public proof ZIPs contain original material, verification evidence and source references; raw third-party manuscripts/web captures are omitted. '
        'No publication creates another discovery count or certifies external peer review or worldwide priority.\n')
    print(json.dumps({'status':manifest['status'],'papers':len(rows),'public_packages':len(rows),'unchanged_PDFs':len(rows),
                      'uploaded':0,'manifest':str((HERE/'submission-manifest.json').resolve())},indent=2))

if __name__=='__main__':main()
