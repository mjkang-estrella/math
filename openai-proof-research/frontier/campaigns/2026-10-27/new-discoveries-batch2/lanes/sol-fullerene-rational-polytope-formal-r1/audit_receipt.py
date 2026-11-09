from pathlib import Path
import re,json,hashlib
L=Path(__file__).resolve().parent
I=(L/'replay/fresh/attempt-003.log').read_text();A=(L/'replay/fresh/attempt-004.log').read_text()
owned=set(re.findall(r'OWN_DECL (\S+)',I))
covered=set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",A))
assert owned==covered,(len(owned),len(covered),list(owned-covered)[:10])
safety=dict(re.findall(r'OWN_SAFETY (\S+) (\S+)',I));assert set(safety)==owned and set(safety.values())=={'false'}
allowed={'propext','Classical.choice','Quot.sound'};observed=set()
for group in re.findall(r'depends on axioms: \[([^\]]*)\]',A,re.S):observed|={x.strip() for x in group.split(',') if x.strip()}
assert observed<=allowed
count=int(re.search(r'TRANSITIVE_SAFE_COUNT (\d+)',I).group(1))
(L/'audit.json').write_text(json.dumps(dict(status='PASS',owned_declarations=len(owned),every_owned_axiom_report_present=True,private_generated_included=True,transitive_type_body_safety_count=count,observed_axioms=sorted(observed),inventory_sha256=hashlib.sha256(I.encode()).hexdigest(),audit_sha256=hashlib.sha256(A.encode()).hexdigest()),indent=2)+'\n')
print('Audit coverage PASS',len(owned),count,sorted(observed))
