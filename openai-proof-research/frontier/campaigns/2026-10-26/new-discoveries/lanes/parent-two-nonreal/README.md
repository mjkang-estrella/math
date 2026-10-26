# Excluded: MathDB337925 is already publicly claimed in full

Credit: **0**. Do not formalize this as a new discovery.

Primary source: Wang–Zhang, *Piecewise interlacing zeros of polynomials*, arXiv1712.04225v2, equation(3.1), normalized initial conditions W0=1,W1=z, Conjecture5.2. Actual primary HTML and source PDF retrieved October26,2026. Parameters a,b,d<0<c; degree n, proposed at most two nonreal zeros.

The live API snapshot `sources/337925-live.json` contains a full submitted proof by Shivam Patel, dated August25,2026. It asserts the stronger localization of at least n−2 distinct real roots below −d/c and gives a complete symmetric-tridiagonal determinant/inertia argument. The entire body was read, and is copied verbatim for private provenance in `sources/posted-solution.txt`. The API status is claimed_progress, despite the search-index page saying open. No claim of independent verification of that submission is needed to exclude a duplicate endpoint from this campaign.

An independent elementary proof route was found before reading that live submission: let F0=1,F1=A and Fn=A Fn−1+B Fn−2, with A=ax+b,B=cx+d. The auxiliary polynomials have n simple real roots below −d/c by the usual sign/interlacing induction. The exact identity Wn=Fn+(z−A)Fn−1 holds for n≥1. At consecutive roots of Fn−1 the values of Wn alternate, forcing n−2 real roots. This is research reasoning only; it was not formalized or independently reviewed and earns no discovery credit because the same full endpoint was already posted.

Frozen snapshot SHA256: ea4a491f776b71876db844043074adf368149b4e736dbd886304597ec64aabd8.
Primary PDF SHA256: cf268a3953b721a095518578677dee3d572d0056521abcec86a29355f1ce3128.
