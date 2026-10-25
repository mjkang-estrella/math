#!/usr/bin/env python3
"""Prepare two isolated, whole-scope reviews of the unchanged author packet."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'fresh-arithmetic-discovery-r162cb'; E=B/'expanded-target-2026-10-17'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
author_brief=E/'fresh-arithmetic-r162cb-brief.txt';ab=author_brief.read_bytes()
assert sha(ab)=='77dd16362731744c01b61985c7fcb372eac90e47a40d34fb5c43ec2e2610e428'
old=ab.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
snap=json.loads((D/'private/intake/root-before.json').read_bytes())
assert sha((R/'STATEMENT.md').read_bytes())=='b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a'
assert sha((R/'private/PROOF.md').read_bytes())=='c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e'
semantic_top={'STATEMENT.md','FINAL.md','REPORT.md','WORKING.md','MANIFEST.json','verify.py'}
semantic_private={'private/FREEZE.json','private/PROOF.md','private/DERIVATION.md','private/SOURCE-INTERFACES.md','private/READING-LIMITS.md','private/source-bindings.json','private/source-receipt.json','private/read-extents.json','private/direct-bindings.json'}
inputs=[]
for rel,e in sorted(snap.items()):
 p=R/rel;a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
 permitted=rel in semantic_top or rel in semantic_private or rel.startswith('private/source/') or rel.startswith('private/primary/')
 inputs.append(dict(path=p.relative_to(P).as_posix(),relative_in_author=rel,**e,raw_integrity_read_permitted=True,semantic_read_permitted=permitted))
allow=D/'private/review-author-inputs.json';dump(allow,inputs);allow.chmod(0o600)
names=[]
for role in ['proof','contribution']:
 names.extend([(B/('arithmetic-r162cb-'+role+'-r1')).relative_to(P).as_posix(),(E/('arithmetic-r162cb-'+role+'-r1-brief.txt')).relative_to(P).as_posix()])
t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==837 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 hits={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(hits.values());checks.append(dict(task_index=i,brief=x['brief'],sha256=sha(a),matches=hits))
guard=dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),before_creation=True,namespaces=names,foreign_initial_briefs=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'review-isolation.json',guard)
for n in names:assert not (P/n).exists(),n
statement=(R/'STATEMENT.md').read_text()
roles={
 'proof':'''INDEPENDENT FULL CORRECTNESS REVIEW of the ENTIRE unchanged frozen statement and complete author proof. Reconstruct the deductions independently. Source operative proofs at the stipulated pin are TRUE;do not audit upstream truth. Check all source hypotheses,interfaces,quantifiers and boundary cases. Give PASS only if every frozen assertion follows and no essential verification remains incomplete;NEEDS_REPAIR for an actual proof defect,or INCOMPLETE for an essential unverified dependency. State precise surviving obligations. Do not replace the theorem by a weaker one,repair author files,or assign a contribution grade,acceptance or count.''',
 'contribution':'''INDEPENDENT FULL-SCOPE SUBSTANTIAL-CONTRIBUTION REVIEW,CONDITIONAL on correctness of the ENTIRE unchanged theorem. Do not inspect the correctness review or assign correctness PASS. Compare the strongest integrated actual source/primary/classical operations with every frozen conclusion. If those pay the full result,give a complete compatible derivation and TECHNICAL,even if the conclusion is impressive. If an identifiable additional nonroutine operation survives that full comparison,justify SUBSTANTIAL precisely. Give INCOMPLETE if an essential comparison is unresolved;unread literature,author labeling or failure of a naive method is not evidence of substantial contribution. No acceptance/count or priority claim.'''
}
details={
 'proof':'''Check one fixed successful extension-field placement throughout. Verify small-plane gadget and line-cover constants,all direction/group memberships and separation hypotheses;isolated-label removal and exact q+z_d counts;omitted lines miss every exceptional group;arbitrary selected special labels in the simultaneous quotient;source linearity and X disjoint from every embedded subplane;at most one new intersection and no duplicate edges. For an arbitrary quotient cover of size<=q,check unique ordinary representatives and forced-pencil inference including the strict occupancy inequality. Check infinity singleton/double cases with every additional label's actual weighted action,internal centers with both axes and h_p+a(p)<=s-1,external centers with at most one free resource,at most three cubic intersections and at most five witnesses per additional label. Check no cover case or label class is omitted. Verify exactly r vertices per part,nonisolation,simplicity and all s,n thresholds in their correct order. These are checks,not a presumption that the proof succeeds or fails.''',
 'contribution':'''The entire balanced-prime and extension-field source proofs are paid,including stronger deterministic reduction over finite fields,core representatives,merge/split and forced-pencil methods,prime-power deletion/change-of-measure,independent-trial extension incidence,all cover cases,implicit linearity and exact q+z_d counts. Do not treat mere merging or balancing as automatically nonroutine. Assess the FULL simultaneous quotient,cover preservation and intersection cap at the retained extension orders. Read the actual primary constructions:HS skeleton and matching-coupled variant;ABPS extremal construction/minimum-cover hypotheses;FHMW linear/MOLS examples;Bucic-Jain-Sivashankar wreath and augmentation;DKMS component equivalence/merging;SW prime-plane stability. Author limitations on individual routes are not exhaustive impossibility claims. A TECHNICAL reduction must retain one configuration,all constraints and parameter quantifiers;separate witnesses or a result about balance alone do not settle the full comparison.'''
}
records=[]
for role in ['proof','contribution']:
 root=B/('arithmetic-r162cb-'+role+'-r1');bp=E/('arithmetic-r162cb-'+role+'-r1-brief.txt')
 common=f'''R162CB independent {role} review,round1.
Write ONLY {root.relative_to(P).as_posix()}/.

{roles[role]}

Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default (STANDARD speed). This overrides obsolete Factory/18-of-20/speed and discovery instructions below. Campaign19/20,latestR041. EVERY command workdir {P}. Your root exists empty. All scratch,downloads,extracts,renders,copies,notes and seal stay there. No author edits,shared-index edits,git/staging/commits,nested agents,heavy installs,unbounded jobs,downstream formal/manuscript/release,publication/uploads/submissions/contacts or browser UI. Your assigned role verdict is authorized;discovery-only self-grading prohibitions below do not forbid it. Parent alone adopts acceptance/count.

Review the ENTIRE unchanged frozen theorem. Read STATEMENT,PROOF,DERIVATION,WORKING,SOURCE-INTERFACES,READING-LIMITS and FREEZE completely. Read BOTH actual Source162 proofs and every operative include at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Both actual wrappers are build/paper.tex:balanced18050bytes/Git93b277615495c01754b4575b045cba89a95f82a1;extension15377bytes/Git141ed64572de469c899d6d12d21790ee066128fa. Twenty canonical blobs,18non-PDFtexts291598bytes,six tree entries. Complete-tree sources/preprints-tree.json has13223entries4858136bytesSHA256eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b;ignore truncated tree.json. This metadata is not proof reading.

Exact author input allowlist: {allow.relative_to(P).as_posix()} (SHA256 {sha(allow.read_bytes())}). It admits all61 author files for raw-byte/full-mode integrity checks. ONLY records with semantic_read_permitted=true may be decoded/copied as operative input. Do NOT decode private/completed prior-round bodies,old originals or inherited control fixtures. Do NOT follow completed-bindings or execute author verify.py with bindings enabled:it reads older originals. It may be read as code;parent already ran it and separately verified exact membership,all source bindings and primary PDFs. Hash-only exclusions are not premises. Preserve all61 author bytes/modes. Exact allowlisted author input and your own root override broad path guards ONLY for those purposes.

Author root: {R.relative_to(P).as_posix()}. STATEMENT SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;PROOF SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. Detached FINAL/MANIFEST/REPORT:3749989702acf47470f1d7baeb1a85549aed8887cff161d6180546a3884ae820 /4e698a7e61eff0727f38936c1ece44d08e0aea277b12017fcd308e264698844a /bb7a7db802bad741c1d304454e3cb033dc6a5063f590844a86f24fda0cc37c18. No author repair or new freeze is authorized.

Read direct AGENTS.md,sources/upstream.json and ONLY acceptance-journal binary[4801,6347);never whole-journal read/hash. No catalogue screen is needed;at most exactbinary[263076,264581) is allowed,no extra titles/families. The exact original author assignment {author_brief.relative_to(P).as_posix()} (SHA256 {sha(ab)}) is admitted for instruction-context reading only. Its research objective is superseded by this review;its older exceptions and suggested history reads grant no additional body access. The complete original standing brief below is preserved verbatim,with these review overrides.

Parent read the complete author proof/evidence but assigns NO mathematical gate. Author reports both complete source proofs,5completeprimarypapers53pages plus DKMS pages1-8 and50-51,10pages;2already-readprimarypages visually checked AFTER freeze. Source truncation recoveries,late repeat reads,version dates,direct-binding capture timing and incomplete ancestry are disclosed. These are author read extents,not your own. Read the actual operative primary proofs necessary for your role;use the permitted copies or retrieve primary originals into your own root. Record actual versions,URLs,read extents,access failures,truncations/recoveries,late reads and unresolved ancestry. Do not infer novelty or correctness from metadata,abstracts,search snippets or another agent's read claims.

{details[role]}

NO optional original-history traversal in these review rounds. No query/read of the other review's prompt,files,metadata,findings,status or live state;no old scan replay,foreign role/status helpers or containing-namespace expansion. Neither reviewer sees the other's verdict. All earlier scopes/dispositions remain unchanged. No independent mathematical review of this nominee has yet occurred;no prior findings or author responses exist for this first round.

Keep durable substantive derivations. Seal your own review packet ONCE:exact safe membership,sorted unique records,SHA256,lengths,FULL file/directory modes,explicit detached FINAL/MANIFEST/outside REPORT anchors and a read-only verifier. Preflight SAME final logic;do not mutate a sealed byte to fit verification. Tiny copied controls suffice. Artifact tests are not mathematical gates. Final handoff states your full-scope role verdict,reasons,remaining obligations,actual reading limits and detached anchors.

ENTIRE UNCHANGED FROZEN STATEMENT (verbatim):

{statement}
END FROZEN STATEMENT.

'''
 text=common+isolation
 missing=rules(old)-rules(text)
 if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
 text+='\n'+marker+standing
 assert rules(old)<=rules(text) and text.split(marker,1)[1]==standing and len(text)<120000
 root.mkdir(mode=0o700);bp.write_text(text)
 records.append(dict(role=role,root=root.relative_to(P).as_posix(),brief=bp.relative_to(P).as_posix(),bytes=len(text.encode()),characters=len(text),sha256=sha(text.encode()),all_author_literal_guards_retained=True,standing_bytes_preserved=5570))
prep=dict(reviews=records,author_input_allowlist=allow.relative_to(P).as_posix(),author_input_allowlist_sha256=sha(allow.read_bytes()),author_files=61,semantic_author_files=sum(x['semantic_read_permitted'] for x in inputs),all_author_files_unchanged=True,other_review_inspection=False,optional_history_traversals=0,model='gpt-6-astra',reasoningEffort='high',serviceTier='default',count_change=0)
dump(D/'review-preparation.json',prep);print(json.dumps(prep))
