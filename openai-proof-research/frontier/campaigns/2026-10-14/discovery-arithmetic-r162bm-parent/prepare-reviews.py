#!/usr/bin/env python3
"""Prepare two isolated, same-scope review briefs without changing author inputs."""
from pathlib import Path
import fnmatch, hashlib, json, re, stat, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'fresh-arithmetic-discovery-r162bm'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {v for v in re.findall(r'\*[^\s,;()]*\*',s) if v not in {'*','**'}}
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
author_brief=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bm-brief.txt').read_bytes()
assert sha(author_brief)=='20d0475443c2d73001a13c2b28faaa6fa669759cab78f2123f4fdedad9a9958f'
old=author_brief.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
head=git('rev-parse','HEAD').decode().strip();t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[]
for role in ['proof','contribution']:
 names.extend([(B/f'arithmetic-r162bm-{role}-r1').relative_to(P).as_posix(),(B/f'expanded-target-2026-10-17/arithmetic-r162bm-{role}-r1-brief.txt').relative_to(P).as_posix()])
checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==817 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(v for v in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),v.casefold())) for n in names};assert all(matches.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
for n in names:assert not (P/n).exists(),n
guard=dict(head=head,namespaces=names,before_creation=True,foreign_initial_brief_checks=checks,legacy=legacy,no_foreign_live_queries=True)
dump(D/'review-prospective-isolation.json',guard)
snapshot=json.loads((D/'private/intake/root-before.json').read_bytes())
admitted=[]
for rel,e in snapshot.items():
 semantic=(rel in {'STATEMENT.md','FINAL.md','REPORT.md','MANIFEST.json','verify.py','private/PROOF.md','private/COMPARISON.md','private/PREFREEZE.md','private/WORKING.md','private/READING-LIMITS.md','private/freeze-anchor.txt','private/source-tree.json','private/source-authentication.json','private/primary-fetch.json','private/primary-fetch2.json','private/primary-fetch3.json','private/primary-fetch4.json'} or rel.startswith(('private/source/','private/primary/','private/renders/')))
 admitted.append(dict(path=(R/rel).relative_to(P).as_posix(),semantic_read_permitted=semantic,**e))
dump(D/'private/review-author-inputs.json',admitted)
statement=(R/'STATEMENT.md').read_text()
assert sha(statement.encode())=='6f1c7eed54c4bee7b80a56494fddfb0e5e0bcd66f0e4b9acc2a2fdb6458f5127'
common='''Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default (STANDARD speed). This overrides older Factory/18-of-20/speed lines. Campaign19/20,latestR041. EVERY shell command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. Write ONLY your exclusive review root,which exists empty. All scratch,downloads,copies,extracts,renders,research and final seal stay there. No author edits,shared-index edits,git/staging/commits,nested agents,heavy installations,unbounded jobs,downstream formal/manuscript/release work,publication/uploads/submissions/contacts or browser UI. Parent alone adopts acceptance/count. Your role-specific review verdict is authorized;the old standing brief's discovery-only ban on assigning a role grade does not prohibit your assigned independent review.

Review ENTIRE unchanged R162BM,not a weakened scope. All Source146 operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are STIPULATED TRUE;do not audit upstream truth. Read the entire author STATEMENT,PROOF,COMPARISON,feasibility and reading records. Independently reconstruct the mathematics against the COMPLETE actual Source146 operative proof:all eleven textual objects145989bytes,including actual build/paper.tex2705/Gitd685d6f3d32384a77d2de437b5660d2846015574,all seven sections,bridge figure and references. Authenticate exact pinned Git metadata. Sources/preprints-tree.json is the complete13223-entry4858136-byte nontruncated tree,SHA256eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Ignore truncated tree.json. Catalogue browsing is unnecessary;at most exact binary[241294,242223) is allowed,no title/family screen or whole catalogue read/hash.

All69 author files may be hashed and their full modes/membership recorded for integrity ONLY. The exact author-input metadata at frontier/campaigns/2026-10-14/discovery-arithmetic-r162bm-parent/private/review-author-inputs.json marks semantic_read_permitted entries. Only those entries may be semantically read/copied as operative author inputs. In particular do NOT decode prior-round private/inputs bodies,old completed comparisons or linked namespaces. Those hash-only exclusions are not mathematical premises. Do NOT run the author verifier with --project if that would semantically admit older completed originals;parent has verified it. You may read verify.py as code and independently authenticate your actual permitted inputs. Do not follow author initial-inputs metadata into older originals. Read direct AGENTS.md,sources/upstream.json and ONLY acceptance journal binary[4801,6347),never full journal read/hash. The complete original standing brief is embedded below. Named metadata and protected bodies remain PRIVATE/local under original rights.

The sole statement SHA256 is6f1c7eed54c4bee7b80a56494fddfb0e5e0bcd66f0e4b9acc2a2fdb6458f5127;author PROOF SHA256839d48acac9b0f3e433aa26d04081e205b499f538b6b0fc5ee04f945cb44f6b5. Author detached FINAL/MANIFEST/REPORT anchors:1b7719ac5b3f13b663d43917c3b417a39d035c729f923c2ec786ea0c3db10cdc /7b562aea83231352144c9628d01e147a58c6c2fc0c14d557c4a3b22e163d275f /bb6b47d085c26c4b968298f616a722006fd463f1df2231806a6186f1e1b5e9bd. Author root:frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bm. STATEMENT.md and private/PROOF.md are immutable;no automatic repairs or alternative theorem.

Treat author assertions as claims,not evidence of review success. Parent has read the full author packet but assigns no mathematical gate. Author reports complete canonical reading,99 touched primary pages(somepartial),four full papers plus two-page errata,13renders,incomplete primary ancestry. BXY2017 was read AFTER statement freeze but BEFORE extended drafting;explicitly preserve and assess that chronology limitation. Full Obata and RHTU,complete Mane+errata,partial Blumenthal and full BXY are available in permitted private/primary paths;these are navigation and copied inputs,not substitutes for your own actual reading/verification. Read strongest relevant primary operative proofs and dependencies needed for YOUR role;do not count search snippets/abstracts/metadata as proof reading. Record URLs,versions,exact extents,failed access,truncations/recoveries,late reads and unexamined ancestry honestly. No exhaustive-literature or priority claim. No optional original-history traversal is authorized in these review rounds;do not query other roles,status/activity helpers,old scans or peer bodies. Own root and the exact permitted author inputs override broad guards only for that exact purpose. Neither review can inspect the other review's prompt,files,findings,metadata,status or live state. Parent dispatch metadata is not an operative premise.

Special attention without assuming errors or success: actual orbit stationarity without independence;one-step upper mean and second moment;compensated semimetric and critical-scale quantifiers;joint HA,H^2A and cross-interval telescopes;clock-zero support for globally weighted weak limits INCLUDING affine boundaries;original graph/sweep transport of new observables with exact constants;four-point geometry recovered only after the clock vanishes;all affine leakage/cut truncation cases;positive local dilation subtraction;terminal strictness and invariant remainder;original normalized area,all large REAL parameters,natural logarithms. Ordinary O(1) additive error and relative asymptotics are already paid,not replacements for o(1).

Keep durable mathematical derivations during work. Seal your fresh review packet ONCE with exact safe membership,unique sorted records,SHA256,lengths,FULL modes,explicit detached FINAL/MANIFEST/outside REPORT anchors and a read-only verifier. Preflight the SAME logic before sealing;after sealing mutate no byte to fit a verifier. Tiny copied positive/negative integrity controls suffice. Integrity is not a mathematical gate. Final handoff must state your full-scope role verdict,its precise reasons/remaining obligation,actual reading limits,and detached anchors. Author originals must remain unchanged.

'''
roles={
'proof':'''Your task is INDEPENDENT ADVERSARIAL FULL CORRECTNESS REVIEW. Reconstruct every deduction and source interface for all frozen quantifiers. Give PASS only if the entire unchanged statement follows from the unchanged proof with no necessary repair or essential unverified dependency. Give NEEDS_REPAIR when a necessary mathematical correction/gap is established;identify exact lines/equations and a counterexample where possible,without claiming more than it proves. Give INCOMPLETE if an essential verification cannot be completed. Small diagnostics supplement a proof,never replace it. Do not assign contribution/acceptance/count. This is not a request to prove a nearby theorem or improve the author proof. Preserve every objection and do not silently repair it.\n\n''',
'contribution':'''Your task is INDEPENDENT FULL-SCOPE SUBSTANTIAL-CONTRIBUTION REVIEW,CONDITIONAL on correctness of the ENTIRE unchanged frozen theorem. Do not inspect the correctness review or assign a correctness PASS. Compare the strongest integrated actual source/primary/classical operations at full scope. If they already pay every conclusion,write the complete compatible derivation and give TECHNICAL (conditional on full correctness),even if the statement sounds strong. If a genuinely additional nonroutine operation remains beyond those reductions and the author supplies it,justify SUBSTANTIAL precisely. If an essential comparison cannot be completed,give INCOMPLETE with the exact missing assessment;do not manufacture a substantial gap out of unread literature or a failed naive argument. Track joint compatibility,not an inventory of individually familiar lemmas. The author's word "nonroutine" is a claim to investigate,not a premise. No acceptance/count or world-priority claim.\n\n'''}
for role,instruction in roles.items():
 root=B/f'arithmetic-r162bm-{role}-r1';bp=B/f'expanded-target-2026-10-17/arithmetic-r162bm-{role}-r1-brief.txt'
 text=f'R162BM independent {role} review,round1.\nWrite ONLY {root.relative_to(P).as_posix()}/.\n\n'+instruction+common+'THE ENTIRE UNCHANGED FROZEN STATEMENT FOLLOWS VERBATIM:\n\n'+statement+'\nEND FROZEN STATEMENT.\n\n'+isolation
 text+='\nAll inherited literal guards,including any outside the prior main isolation block,remain effective:\n'+' '.join(sorted(rules(old)))+'\n'
 text+='\nAdditional exact peer isolation: exclude ALL arithmetic-r162bm-'+('contribution' if role=='proof' else 'proof')+'-r1 paths and aliases,including prompts/metadata. No cross-review consultation.\n\n'+marker+standing
 assert rules(old)<=rules(text) and len(text)<120000
 root.mkdir(mode=0o700);bp.write_text(text)
 dump(D/f'{role}-brief-preparation.json',dict(brief=bp.relative_to(P).as_posix(),root=root.relative_to(P).as_posix(),bytes=len(text.encode()),sha256=sha(text.encode()),role=role,source=146,statement_sha256=sha(statement.encode()),full_scope_unchanged=True,all_inherited_literal_guards_retained=True,standing_bytes_preserved=5570,serviceTier='default',peer_review_excluded=True,optional_history_traversals=0))
print(json.dumps(dict(briefs_prepared=2,author_files=len(admitted),semantic_files=sum(x['semantic_read_permitted'] for x in admitted),foreign_initial_briefs_checked=len(checks),author_root_unchanged=True)))
