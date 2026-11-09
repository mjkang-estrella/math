import sys
sys.path.insert(0,'scripts')
from fetch import get
H='e51c7d81cdffe6e70999db34b8a564a99074807b'
B='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+H+'/'
items=[('omega-problem-halffreq.md',B+'Problems/bona-maga-richey-2026-half-frequency-balanced-borders.md'),
('omega-problem-crim.md',B+'Problems/crim-rectair-square-conjecture-two-refutation.md'),
('omega-BalancedBordersHalfFrequency.lean',B+'D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.lean'),
('omega-BonaMagaRicheyHalfFrequency.lean',B+'D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.lean'),
('omega-CrimGrundyRefutation.lean',B+'D5/S0/Certificates/Games/CrimGrundyRefutation.lean'),
('omega-ClosedSupply.lean',B+'D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ClosedSupply.lean')]
for it in items: print(get(it))
