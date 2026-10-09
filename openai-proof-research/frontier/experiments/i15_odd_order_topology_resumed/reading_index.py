#!/usr/bin/env python3
"""Reproduce exact cited passages from hashed primary-source bytes."""
import json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[3];OLD=R/'frontier/sources/i15_odd_order_topology';NEW=R/'frontier/sources/i15_odd_order_topology_resumed'
def sha(b):return hashlib.sha256(b).hexdigest()
contracts=json.loads((OLD/'contracts.json').read_text())
(NEW/'contracts.json').write_text(json.dumps(contracts,indent=2)+'\n')
# These inclusive ranges use Python str.splitlines(): PDF page-break characters
# are line breaks. The retained exact passage hash removes any ambiguity.
ranges={
'bartels-lueck':[(1,80),(138,161)],
'elementary-amenable-four':[(1,140)],
'dovermann-schultz':[(1,57)],
'bak-morimoto':[(1,124)],
'arabadji-baykur-v3':[(1,65)],
'davis-leary':[(1,145)],
'avramidi-okun-schreve':[(335,368)],
'davis-hayden-huang-ruberman-sunukjian':[(1,40)],
'davis-book':[(11112,11205),(11855,11950)],
'davis-exotic':[(645,676)],
'krushkal-quinn':[(140,179)],
'allender-boolean':[(163,230)],
'block-weinberger':[(25,170)],
'davis-lueck':[(208,266)],
'hilman-kirstein-kremer':[(1,140)],
'kremer-2026-v1':[(1,190)],
}
# New reads include the definitions preceding the results, so "realizable"
# cannot silently change meaning to "has some individual representative".
new_ranges={'pesikoff-v1':[(1,115),(790,822)],'kremer-borel-v1':[(1,190)],'kang-park-taniguchi-published':[(1,122)],'lee-cyclic':[(1,45),(140,171)],'conner-raymond':[(393,418),(1910,2080)],'raymond-scott-publisher':[(1,98),(228,288),(386,425)]}
meta={}
for key in ['retained','new','final']:
 for x in json.loads((OLD/'literature'/f'{key}-manifest.json').read_text()):meta[x['name']]=x
retrieval=sum((json.loads((NEW/f).read_text()) for f in ['retrieval-manifest.json','additional-retrieval-manifest.json','final-retrieval-manifest.json']),[])
for x in retrieval:
 if x['path'].startswith('literature/') and 'error' not in x:meta[Path(x['path']).stem]=x
versions={'bartels-lueck':'retained arXiv 0901.0442v2 (PDF header); retrieved unversioned URL',
'elementary-amenable-four':'retained arXiv 2501.12512v2, 29 June 2026 (PDF header)',
'dovermann-schultz':'Version 2.0.0, June 2006 (PDF text)',
'arabadji-baykur-v3':'arXiv 2304.10399v3, 11 October 2023',
'hilman-kirstein-kremer':'retained arXiv 2409.02220v1 (PDF header)',
'kremer-2026-v1':'arXiv 2608.30620v1, submitted 31 August 2026; internal date September 1',
'davis-book':'author-hosted book; retained chapter production date July 9, 2007; unversioned URL',
'davis-lueck':'published author offprint Transactions AMS 377 (2024), 7557–7628',
'block-weinberger':'Comment. Math. Helv. 83 (2008), 21–33',
'krushkal-quinn':'Geometry & Topology 4 (2000), 407–430',
'davis-hayden-huang-ruberman-sunukjian':'author manuscript arXiv 2411.19400v2, submitted 9 December 2024; internal date December 10',
'conner-raymond':'published AMS scan, Bulletin AMS 83 (1977), 36–85, DOI 10.1090/S0002-9904-1977-14179-7',
'raymond-scott-publisher':'published Springer scan, Archiv der Mathematik 29 (1977), 643–654, DOI 10.1007/BF01220468; Theorem 2 checked visually on page 648',
'pesikoff-v1':'arXiv 2605.27537v1, 26 May 2026',
'kremer-borel-v1':'arXiv 2510.21550v1, 24 October 2025; internal date October 27',
'kang-park-taniguchi-published':'published version DOI 10.1007/s00222-025-01378-1, online 10 October 2025',
'lee-cyclic':'unversioned author-hosted manuscript; no date/version identified in PDF header; hash governs'}
records=[]
for base,table in [(OLD,ranges),(NEW,new_ranges)]:
 for name,rs in table.items():
  p=base/'literature'/(name+'.txt');ls=p.read_text().splitlines();pdf=p.with_suffix('.pdf')
  excerpts=[]
  for a,b in rs:
   passage='\n'.join(ls[a-1:b]);excerpts.append(dict(start_line=a,end_line=b,text=passage,sha256=sha(passage.encode())))
  records.append(dict(name=name,text_path=str(p.relative_to(R)),text_sha256=sha(p.read_bytes()),pdf_path=str(pdf.relative_to(R)),pdf_sha256=sha(pdf.read_bytes()),url=meta[name]['url'],version=versions.get(name,'retained primary author manuscript, unversioned URL; exact bytes and retrieval metadata govern'),passages=excerpts))
(NEW/'reading-index.json').write_text(json.dumps(dict(line_convention='Python str.splitlines, including form feeds',scope='Exact cited primary passages, not a claim of whole-book reading. Twenty old pairs verified; two unrelated algebra/group-theory comparators are not used for topology.',records=records),indent=2)+'\n')
print(json.dumps(dict(source_contracts=len(contracts),primary_texts=len(records),passages=sum(len(x['passages']) for x in records))))
