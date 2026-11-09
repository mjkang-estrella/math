import pathlib,json,hashlib,zipfile
r=pathlib.Path(__file__).resolve().parent;f=r/'fresh-extracted';p=r/'packet'
rows=json.loads((r/'module-times.json').read_text());g=json.loads((r/'generation.json').read_text())
def sums(a):
 c=sum(x['build_seconds'] for x in a);k=sum(x['check_seconds'] for x in a)
 return {'compiler_seconds':round(c,2),'checker_seconds':round(k,2),'total_seconds':round(c+k,2)}
alltimes=sums(rows);pilots=[]
for n in [1000,5000]:
 a=[x for x in rows if not x['module'].startswith('MaskChain0') or int(x['module'][9:])<n//100]
 a=[x for x in a if x['module'] not in ['EndpointR7','AuditR7']]
 t=sums(a);h=g[f'hint_uses_{n}']
 pilots.append({'start_index':0,'end_exclusive':n,'hint_uses':h,**t,'hints_per_second':h/t['total_seconds'],'scope':'Full closed chain including all 4728 input entailments for the 5000-step packet, fixed geometry and normalization dependencies, and named dependency assembly; excludes final endpoint/audit. Not a heavy-window benchmark.'})
result={'status':'partial','endpoint':'Percolation.not_conjecture20_mask_after5000','statement':'Percolation.MaskChain.RemainingSuffixUnsatR7 → ¬ Percolation.Conjecture20','closed_mask_additions':5000,'unreplayed_suffix_zero_based':[5000,129671],'remaining_additions':124671,'historical_separate_list_frontier':13561,'historical_remaining_additions':116110,'modules_total':len(rows),'compiler_passes':len(rows),'checker_passes':len(rows),**alltimes,'peak_rss_kib':max(x[y] for x in rows for y in ['build_peak_rss_kib','check_peak_rss_kib']),'pilots':pilots,'required_heavy_1000_5000':'NOT MEASURED in round 7; do not substitute cheap prefix measurements','strategy_selection':'No full-certificate restart-versus-continuation cost decision is justified yet. This packet validates a separate restart prefix; inherited.zip preserves the older frontier.','unconditional_targets':'Not proved','acceptance_credit':0}
(r/'results.json').write_text(json.dumps(result,indent=2))
for name,m in [('axioms.txt','EndpointR7'),('metadata-audit.txt','AuditR7')]:
 (r/name).write_bytes((f/'logs'/f'build-{m}.log').read_bytes())
comp={}
with zipfile.ZipFile(r/'source-only.zip') as z:
 for name in z.namelist():
  if name.startswith('src/'):
   b=z.read(name);assert b==(f/name).read_bytes()==(p/name).read_bytes()
   comp[name]=hashlib.sha256(b).hexdigest()
(r/'fresh-source-comparison.json').write_text(json.dumps(comp,indent=2))
(r/'SUMMARY.md').write_text(f'''# Round 7: closed mask-chain implementation, partial

This packet proves concrete input-mask entailments and supplies named hint dependencies, closing normalized certificate additions [0,5000). All 4,728 input clauses used by that prefix have proved generator entailments and kernel-checked encoding equalities. No local-hint assumptions remain in its named clause theorems. Root decides acceptance; credit is zero.

Endpoint: `Percolation.not_conjecture20_mask_after5000 : Percolation.MaskChain.RemainingSuffixUnsatR7 → ¬ Percolation.Conjecture20`. Its exact remaining semantic obligation is unsatisfiability of the normalized generator together with the proved last clause, mask `(2495223039294576003288924160, 1208935042986666046259200)`. Exactly 124,671 certificate additions, zero-based [5000,129671), have not been replayed by this mask packet. NoMinimalTwoRound5 and the unconditional endpoint remain unproved.

The older 13,561-step list frontier remains separately preserved in inherited.zip, hash 9add6cc761e26a70637ea9a8555199187c705f121a3a25b1159ce2f22ec7637c. It has 116,110 unreplayed suffix additions. These frontiers are alternatives and are never added together.

Fresh strict replay: {len(rows)}/{len(rows)} compiler passes and {len(rows)}/{len(rows)} explicit-module leanchecker passes. Compiler total {alltimes['compiler_seconds']:.2f} s; checker total {alltimes['checker_seconds']:.2f} s; combined {alltimes['total_seconds']:.2f} s. These are GNU process wall times, excluding development, failures and shell/watchdog overhead. Peak process RSS: {result['peak_rss_kib']} KiB. Source scan and local metadata audit, including the expression builder, pass. Printed endpoint axioms are only propext, Classical.choice and Quot.sound.

The full-chain 5,000-step prefix measurement is {pilots[1]['total_seconds']:.2f} s for 10,146 hint uses, {pilots[1]['hints_per_second']:.3f} hints/s, including input proofs and fixed dependencies. Its first-1,000 conservative measurement is {pilots[0]['total_seconds']:.2f} s for 2,146 hints, {pilots[0]['hints_per_second']:.3f} hints/s; it charges all inputs prepared for 5,000. The windows overlap. These cheap-prefix rates are not heavy-window rates. The required heavy 1,000/5,000 windows [13561,14561) and [13561,18561) remain unmeasured, so no claim that the full packet fits four hours or that one restart strategy is cheaper is justified.

The session hands back a closed implementation prefix rather than a complete certificate. Continue with the heavy full-chain measurements before scaling. The input proofs are a significant cost absent from round 6's approximately 875-hints/s local-check pilot.

Development failures: builder structure syntax and monadic mkArrow corrections; input-proof indentation correction; an out-of-root development test invocation and an invalid checker search-path argument. All logs are retained. No limit was raised. The final packet omits experimental baseline/pilot modules and the historical list replay from its dependencies, while preserving the historical archive unchanged. Every retained original proof/definition/bridge module is byte-identical and hash-compared. No background job remains at handback.

Files: source-only.zip, inherited.zip, module-order.txt, module-times.json, results.json, progress.json, PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, NEXT.md, fresh-replay.log, fresh-extracted/logs/, retained-source-comparison.json, fresh-source-comparison.json, metadata-audit.txt, axioms.txt, and lane-owned scripts.
''')
(r/'module-order.txt').write_bytes((f/'module-order.txt').read_bytes())
print(json.dumps(result,indent=2))
