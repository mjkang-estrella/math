from pathlib import Path
import shutil,json,hashlib
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); own=root/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r93';p=own/'packet'
def copy_records(paths,kind):
 out=[]
 for rel,extent in paths:
  src=root/rel; dst=p/'private'/kind/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  out.append({'path':rel,'local':str(dst.relative_to(p)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'bytes':src.stat().st_size,'reading':extent})
 (p/'public'/f'{kind}.json').write_text(json.dumps(out,indent=2)+'\n')
copy_records([('AGENTS.md','complete'),('sources/upstream.json','complete'),('sources/CONTENTS.md','loaded in full; compact all-family headings and selected descriptions displayed; initial huge output truncated, not every full entry semantically read'),('sources/preprints-tree.json','complete parsed all13223 records; truncated=false; full metadata, not manuscript reading'),('frontier/NEW-TEN-2026-10-14.md','opening/current requirements and selected operative history; not entire long operational log')],'context')
a=[]
for n,calc in [(90,'automorphism-feasibility.md'),(91,'tensor-feasibility.md'),(92,'deck-feasibility.md')]:
 base=f'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r{n}'
 for name in ['REPORT.md','packet/public/report.md','packet/public/'+calc,'packet/public/other-screens.md','packet/public/reading-limits.md']:
  a.append((base+'/'+name,'actual body read before extended derivation; no entire linked chains'))
 a.append((f'frontier/campaigns/2026-10-14/discovery-arithmetic-r{n}-parent/intake.json','complete current intake'))
for rel,ext in [
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83/packet/public/slope-budget.md','complete before freeze; after initial feasibility; reread operative full argument before freeze'),
 ('frontier/iterations/i28-algebra-discovery.md','section3 relevant noMCM operations; combined display truncated in middle; not full iteration'),
 ('frontier/iterations/i31-nonconical-no-mcm.md','large combined display truncated early; ending sections6-9 and full-scope conclusion visible; not complete body'),
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r16/checkpoint.md','motivic all-n argument read; combined display clipped ending'),
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r48/checkpoint.md','relevant source040 history portions'),
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r75/packet/public/research.md','integral motives section read, not full research'),
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r24/payload/screen-044.md','complete'),
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r11/screen053.md','complete'),
 ('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r44/screen310.md','complete'),
 ('frontier/campaigns/2026-10-14/discovery-analytic-r125-parent/intake.json','complete before freeze; not linked annular proofs')]:a.append((rel,ext))
copy_records(a,'history')
# Preserve failed primary retrievals without overwriting successful version records.
f=p/'public/horrocks-attempts.json';a=json.loads(f.read_text());a.insert(0,{'url':'https://www.numdam.org/item/AST_1980__71-72__197_0/','failure':'HTTP404 in earlier primary attempt; restored from session chronology after overlapping metadata writes omitted it','receipt_limit':'retrospective failure record, no HTTP response body retained'});f.write_text(json.dumps(a,indent=2)+'\n')
# Successful original has its own record; normalize all successful originals into one index too.
f=p/'public/primary.json';a=json.loads(f.read_text());a.append(json.loads((p/'public/horrocks-volume.json').read_text()));f.write_text(json.dumps(a,indent=2)+'\n')
print({'history_copies':len(json.loads((p/'public/history.json').read_text())),'context_copies':5})
