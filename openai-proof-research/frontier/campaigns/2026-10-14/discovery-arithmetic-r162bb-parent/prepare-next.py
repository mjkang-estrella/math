#!/usr/bin/env python3
"""Prepare Source135 discovery with inherited scope and isolation constraints."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162bc-parent';R=B/'fresh-arithmetic-discovery-r162bc';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bc-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'))
assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==789 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bb-brief.txt').read_bytes();assert sha(original)=='8bb0bd0d375ef095e8f4e230bbd9664dd99fd180b2fc900b4c4b4a099dc02494'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source134')].replace('Arithmetic discovery r162bb — confirmed generalized-star-height operative-proof discovery.','Arithmetic discovery r162bc — confirmed homogeneous-depth-five-IMM operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bb/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bc/.',1).replace('FRESH DISTINCT Source134','FRESH DISTINCT Source135',1).replace('Own r162bb I/O','Own r162bc I/O',1)
instructions='''Read the COMPLETE actual Source135 operative proof, actual wrapper, every mathematical include/figure and strongest primary/companion operations BEFORE selecting a full additional theorem. The ENTIRE source lower bound is ALREADY PAID:over EVERY characteristic-zero field,EVERY syntactically homogeneous Sigma-Pi-Sigma-Pi-Sigma circuit computing the(1,1) entry IMM(n,n) of a product of n independent n-by-n variable matrices requires at least n^(sqrt(n)/400) gates for ALL sufficiently large n,with one ABSOLUTE threshold independent of the field. Bottom linear forms may use ALL variables. Arbitrary finite fan-in,fan-out and shared gates are allowed. The ALL-FIELD block-expansion upper bound n^(sqrt(n)+4) for n>=2 and ALL stronger actual source operations are ALSO paid. Source truth is stipulated;do not audit or nominate it.

Read the full rank measure,circuit decomposition,moment and path-pairing calculations,completion and exact parameter budgets,not merely the abstract. Actual source interfaces may be stronger than the headline theorem. Retain gates versus wires versus formula size,homogeneity syntactic conventions,depth counting,shared subcomputations,arbitrary-support linear forms,field/characteristic dependence,all sufficiently large n and every absolute threshold. A restricted model cannot replace the full source result. Any characteristic transfer,nonhomogeneous or border/approximate extension,quantitative strengthening,uniformity/explicitness statement or other direction needs its OWN COMPLETE compatible nonroutine proof after the strongest source/primary composition. Do not select one merely from this list.

Perform sustained mathematical derivation after actual source and strongest primary reading. Choose ONE viable distinct operation;freeze every hypothesis,quantifier,constant,model and conclusion only if a full additional nonroutine proof is viable. Parent alone commissions independent adversarial correctness and separate actual-primary substantial-contribution reviews. A paid composition or unproved conditional bridge does not count. No desired-grade retry or narrowing/renaming/reopening an older target. This circuit family is distinct from preceding star-height work,without a project-history clearance or never-investigated claim. Older arithmetic IMM/matrix-multiplication and other scopes below remain immutable;compare actual overlaps before any claim.

R162BB is archived PREFREEZE/no nominee;no theorem or diagnostic selected/frozen. All SAME-alphabet uniform generalized-height13/4/3 constructions,actual stronger affine/clock/split/decoder/compiler interfaces and primary coding/counting/wreath operations are paid. A simultaneous TWO-block shift supplies for EVERY full table and EVERY tuple/input a usable coordinate in EACH block,with ONE beta and l=1024a²q^(2a-1). Coordinates may depend on input/tuple;not forall tuple exists ONE coordinate forall input. Source dependency proof and MT resampling pay existence and expected local explicit-binary-table construction,conservative CB^6 including scans/randomness/output,not deterministic succinct cost or full compiler. The attempted one-split route lacks ONE recoverable total update,compatible early/late all-input certificates,joint arbitrary-independent-tag/cross-pair soundness,exact whole-stencil/end decoding and SAME-alphabet height-one leaves. C2/parity/bounded-factor examples refute specified shortcuts only,not source episodes,all constructions or universal height-two claims;no frozen diagnostic. All40 canonical texts/421986 bytes read,43 blobs/55 entries authenticated,three PDFs authentication only;four full primary extracts/243807 bytes/77 pages,four rendered pages;late reads/recoveries and transitive gaps disclosed. Five exact completed exceptions,no optional history traversal,no full compiler. A missing-file attempt read no outside bytes. Bundled verifier REJECTS unique but unsorted file records;sealed author bytes unchanged. Parent independent checks and ONLY in-memory relaxation of ordering pass exact uniqueness/membership/hashes/lengths/modes/Git bindings/copies:78 payloads/81 files/21 subdirectories. Preserve this limitation;do not claim original verifier passed. No mathematical gate/count. All earlier full scopes/dispositions preserved.

'''
older=old[old.index('R162BA is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source135-selection.json').read_text())
assert sel['catalogue_extent']==[223610,225119] and len(sel['folders'])==1 and len(sel['entries'])==16
blobs=[e for e in sel['entries'] if e['type']=='blob'];assert len(blobs)==12
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162bb/private/MATH.md',B/'fresh-arithmetic-discovery-r162bb/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162bb/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162bb/private/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[223610,225119),EXACT Source135. Parent used ONE bounded14000-byte window[223610,237610),decoding ONLY FIRST TWO numeric-bold TITLE STRINGS135/136 and ONLY135 BODY. Source136 body/remainder were NOT decoded;the third heading supplied ONLY a byte boundary,not its title/body. ONE family BODY screened. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay. Navigation is not exhaustive clearance.\n\nConfirmed canonical folder and ACTUAL wrapper from complete-tree metadata:\n'
for folder in sel['folders']:
 candidates=[e for e in blobs if e['path'] in {folder+'/build/main.tex',folder+'/build/paper.tex'}];assert len(candidates)==1;w=candidates[0]
 section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='There are12 blobs/16 entries including the root:11 textual objects and one compiled PDF. Authenticate exact selected bytes/metadata;read ALL actual operative text,wrapper,includes,figure,bibliography and relied-upon dependencies. Follow build/paper.tex and its actual includes rather than guessing build/main.tex. Inspect every relied-upon pairing diagram and distinguish PDF/metadata authentication from semantic proof reading. Parent operative source reading:NONE. lean/docs/135.md is scoped comparator navigation only;no downstream formalization or end-to-end formalization inference.\n\nRead these FIVE exact COMPLETED originals(project-relative POSIX):\n'+'\n'.join(e['path'] for e in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older exception,review,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's proof evidence. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only in your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored arithmetic-circuit,iterated-matrix-product,homogeneous-depth-five,rank/derivative,moment,pairing,path and shared-gate mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Seal once with explicit detached anchors and a read-only verifier. BEFORE sealing,sort manifest records if the verifier requires sorting;assert uniqueness and test the SAME final verifier logic. After sealing,do not change any sealed file to fit a verifier. Check exact safe membership,hashes,lengths,modes and copies. Distinguish artifact checks from mathematical gates;report any bundled-verifier failure honestly.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
suffix=R.name.rsplit('-',1)[1]
extra=f'\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*{suffix[1:]}* *arithmetic*{suffix}*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {f'*arithmetic*{suffix[1:]}*',f'*arithmetic*{suffix}*','*structural*r220*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing and brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bc/.'
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=135,catalogue_extent=[223610,225119],canonical_folders=1,canonical_blobs=12,canonical_entries_including_roots=16,nonvendor_texts=11,vendor_runtime_blobs=0,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source136_body_not_decoded=True,title_navigation_windows=1,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=12,canonical_entries=16,all_guards_retained=True,distinct_family=True)))
