from pathlib import Path
D=Path(__file__).resolve().parents[1]
s=(D/'scripts/tournaments.c').read_text().replace('orb[8]','orb[9]').replace('n=5;n<=7','n=8;n<=8').replace('mp[8]','mp[9]').replace('sz[8]','sz[9]').replace('mx[8]','mx[9]').replace('cnt[8]','cnt[9]').replace('bad[8]','bad[9]').replace('witness[8]','witness[9]')
s=s.replace('for(unsigned m=0;m<(1u<<b);m++)for(k=5;k<=n;k++){','for(unsigned representative=0;representative<8*(1u<<21);representative++){ unsigned r=representative>>21; unsigned m=((representative&((1u<<21)-1))<<7)|((1u<<r)-1);for(k=5;k<=n;k++){')
s=s.replace('for(k=5;k<=n;k++){printf','}\n for(k=5;k<=n;k++){printf').replace('labelled=%u','labelled_space=%u reduced_representatives=16777216')
(D/'scripts/tournaments8.c').write_text(s)
