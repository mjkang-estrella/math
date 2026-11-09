from pathlib import Path
import re
L=Path(__file__).resolve().parent/'replay/fresh-6'
inv=''.join((L/(m+'-replay.log')).read_text() for m in ['Inventory','InventoryRank','InventoryHulls'])
audit=''.join((L/(m+'-replay.log')).read_text() for m in ['Audit','AuditRank','AuditHulls'])
a=set(re.findall(r'OWN_DECL (\S+)',inv));b=set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",audit))
print(len(a),len(b));print('missing',sorted(a-b));print('extra',sorted(b-a))
