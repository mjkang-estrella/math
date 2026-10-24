#!/usr/bin/env python3
"""Prepare one configured distinct research round; never dispatch or mutate shared state."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
C=json.loads((D/'next-configuration.json').read_text())
current=C['current'];future=C['next']
N=B/f'discovery-arithmetic-{future}-parent'
R=B/f'fresh-arithmetic-discovery-{future}'
BP=B/f'expanded-target-2026-10-17/fresh-arithmetic-{future}-brief.txt'
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def dump(p,x):
    p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t
tasks=json.loads(raw_t)
assert tasks['newAccepted']==19 and tasks['target']==20
own=next(i for i,t in enumerate(tasks['tasks']) if t.get('clientRequestId')==f'twenty-20261023-fresh-arithmetic-{current}-codex-astra-r1')
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]
checks=[];legacy=[]
patterns=lambda s:{g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
for i,t in enumerate(tasks['tasks']):
    if i==own or t.get('status') not in {'running','queued','waiting'}:
        continue
    if 'brief' not in t:
        assert 'nativeTaskName' in t and 'taskId' not in t
        legacy.append(i);continue
    raw=(P/t['brief']).read_bytes();rules=patterns(raw.decode())
    matches={n:[g for g in sorted(rules) if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,legacy_limit='Historical native entries lack original briefs; no live query or reopening. Recorded status is not fresh liveness.',foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir()
dump(N/'prospective-isolation.json',guard)

old_raw=(B/f'expanded-target-2026-10-17/fresh-arithmetic-{current}-brief.txt').read_bytes()
marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old_raw.split(marker,1)[1]
assert len(standing)==5570
old=old_raw.decode()
prefix=old[:old.index('Catalogue access,if needed:')]
substitutions=[(f'Arithmetic discovery {current} — {C["old_title"]}.',f'Arithmetic discovery {future} — {C["new_title"]}.'),(f'Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-{current}/.',f'Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-{future}/.'),(f'This is {C["old_family"]}.',f'This is {C["new_family"]}.'),(f'Own {current} is excluded',f'Own {future} is excluded')]
for old_text,new_text in substitutions:
    assert prefix.count(old_text)==1,(old_text,prefix.count(old_text))
    prefix=prefix.replace(old_text,new_text,1)
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
direct=[D/'assessment.md',B/f'fresh-arithmetic-discovery-{current}/FINAL.md',B/f'fresh-arithmetic-discovery-{current}/packet/private/prefreeze-mathematics.md',B/f'fresh-arithmetic-discovery-{current}/packet/private/primary-understanding.md',B/f'fresh-arithmetic-discovery-{current}/packet/private/READING-LIMITS.md']
records=[]
for p in direct:
    raw=p.read_bytes();records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(N/'private/completed-direct-inputs.json',records)
selected=json.loads((D/f'private/intake/Source{C["source"]}-selection.json').read_text())
assert len(selected['folders'])==C['folders'] and len(selected['entries'])==C['entries']
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==C['blobs']
wrappers=[]
assert len(C['wrapper_paths'])==len(selected['folders'])
for folder,wrapper in zip(selected['folders'],C['wrapper_paths']):
    choices=[x for x in blobs if x['path']==wrapper and wrapper.startswith(folder+'/')]
    assert len(choices)==1,(folder,wrapper,len(choices))
    wrappers.append(choices[0])
lo,hi=C['catalogue_extent']
section=f'''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[{lo},{hi}),EXACT Source{C['source']} body. Parent decoded only the FIRST TWO numeric-bold title strings from ONE bounded14000-byte window starting{C['navigation_start']},then selected ONLY{C['source']} body as a distinct family. Source{C['skipped_source']}'s body was NOT decoded or selected. No child title locator,extra family,catalogue screen,ancestor hunt or whole-catalogue opening/decoding. {C['folders']} confirmed folders have{C['blobs']} blobs/{C['entries']} complete-tree entries including roots. All actual wrappers below were selected from complete-tree metadata. Parent source-body reading:NONE. Metadata is navigation,not a theorem/proof interface. {C['navigation_limits']}

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
'''
section+='\n'.join(p.relative_to(B).as_posix() for p in direct)
section+='''
These exact exceptions never authorize containing namespaces,links,other copied/source bundles,role/brief/status/activity aliases or peer findings. Protected completed bodies AND named metadata remain PRIVATE/local under original rights;any copies stay inside your own root. No prior exact-body exception propagates,including old I134/I198/I200,r105,r35,R041 or weighted Brunn-Minkowski rights. Do not repeat or broaden an old scan.

Confirmed canonical folders and actual wrappers:
'''
for folder,w in zip(selected['folders'],wrappers):
    section+=folder+'\n'+w['path']+f"\nbytes {w['size']}; Git blob {w['sha']}.\n"
section+='\n'+C['source_instructions']+'\n\n'
extra='\nFurther explicit prospective wildcard rules,including the completed round correction and BOTH new twins:\n'+' '.join(C['extra_guards'])+'\n\n'
brief=(prefix+C['previous_scope']+'\n\n'+section+isolation+extra+marker.decode()).encode()+standing
new_rules=patterns(brief.decode())
assert patterns(old)<=new_rules
assert set(C['extra_guards'])<=new_rules
assert f'*arithmetic*{future[1:]}*' in new_rules and f'*arithmetic*{future}*' in new_rules
assert brief.split(marker,1)[1]==standing
assert brief.decode().startswith(f'Arithmetic discovery {future} — {C["new_title"]}.')
BP.write_bytes(brief)
dump(N/'private/canonical-selection.json',selected)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=C['source'],catalogue_extent=C['catalogue_extent'],skipped_source_body_not_selected=C['skipped_source'],canonical_blobs=C['blobs'],canonical_entries_including_roots=C['entries'],completed_direct_inputs=5,parent_source_body_read=False,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=len(blobs),both_new_literal_twins_verified=True)))
