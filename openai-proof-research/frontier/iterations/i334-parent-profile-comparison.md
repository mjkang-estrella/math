# I334 comparison with the two existing production profiles

2026-10-13. Parent comparison deduction; no independent contribution verdict or priority claim. This supplements the frozen I334 candidate without modifying it.

The pinned source flow.tex lines 73–116 gives the earlier Chen et al. profile in the present natural-log convention:

    C_m(I)=max{ F(psi(m)+I)-m V(s), F(I) },
    m H(s)=(H(m)-I)s,   m<=s<1.

It also compares the source reserve B_m, which equals 2I when I<=c_m:=H(m)-(1-m²)L. The source final profile is max{B_m,F}. These facts do not establish the proposed global BP correction by themselves.

For fixed 0<m<1, the implicit-function theorem applies at I=0,s=m because H(m)+mV(m)>0. Differentiation gives

    s'(0)=m/[H(m)+mV(m)],
    d/dI [F(psi(m)+I)-mV(s)] at I=0
      =1+mH(m)/[(1-m²)V(m)(H(m)+mV(m))].

As m tends to 1, this derivative tends to 1: with eps=1-m, H(m)~(eps/2)log(1/eps), 1-m²~2eps, and V(m)~(1/2)log(1/eps). Therefore, for a fixed m sufficiently close to 1, the first branch has derivative strictly below F'(0)=2. Both vanish at I=0, so for all sufficiently small positive I the earlier hybrid profile C_m equals F(I). Also c_m>0 for such m, so the source reserve equals 2I<F(I) on a possibly smaller interval. The pointwise maximum of these already displayed profiles is just F(I) there.

The I334 proposal F(I)+c m² I² is strictly larger on this interval. Thus mere evaluation or maximization of these existing displayed profiles does not supply BP. This does not exclude an older proof-level strengthening, another prior theorem, or a different standard reduction. Those require the independent contribution audit, and the argument does not assert worldwide novelty.

Primary input read: pinned flow.tex lines 73–116, raw SHA256 9065dd3bd4bf33f66547e58c0a39c5841103f48d134cbe9eea392ec5289653c1. Parent also read the existing local extraction of Chen et al. arXiv:2609.24931v2, lines 2440–2650, including the full Lemma 9.2 and its explicit hybrid candidate; no complete-paper reading is claimed. The cached extraction is frontier/sources/i131_soft_summary_stability/external/chen-v2-html.txt, SHA256 522261bc5200556213b25697977f4cbea264eb4efbdcb8a5e53db206b1a0d276. No new full external body was retained.
