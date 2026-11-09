from pathlib import Path
import re
s=(Path(__file__).resolve().parent/'primary/ipam-schedule').read_text()
for chunk in s.split('<div class="schedule-item talk">')[1:]:
 chunk=chunk.split('<div class="video">')[0];print(re.sub('<[^>]*>',' ',chunk));print(re.findall(r'https://helper[^" ]+',chunk))
