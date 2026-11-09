# CHECKPOINT — polynexus-product-formal-pi-r5 (2026-11-07, continuation)

Lane state after baseline rebuild + product module. All strict builds/checks
via check.sh/checker.sh/audit.sh under runner.py (-j1 -M3500 -DwarningAsError=true).

## Sealed modules (strict exit 0, checker exit 0, all-decl axiom audit exit 0)

- PolynexusDiag src d6377c54f2299cb67f79723bb00823c4cef12b5493d6b3f45f378b1b513cc2d6
  olean 6e86bfa28d463f0229dcfa3826d375e54e5f836aba10953f98b7383d0dfd3451 (== r4 record)
- PolynexusSrc  src cf772caae9c87ce564f2b454fdcd8ede6a5251e04d072acb1866b99f5d51e58f
  olean b95bc71191de1ddc94d29e0046c0f8e23981915f4e2015892d08cd20bd7963dc (== r4 record)
- PolynexusProd src 4e8c7f741550c2eb0a1b3e5ca9d780a5f8b17b4868f367b7083e0576fba439af
  olean abe98b2593f65dac35ed74d35b1fa9b212c1797744c6c46fb91e6f1b8e57a0ba
  PMulWit, PCnd_row_col_unique, PBlk_mul_summand_one/zero, PBlk_mul_entry
  (exact ordinary product entry = 1 iff coupled witness else 0), PMulWit_overlap.
  Audit: propext/Classical.choice/Quot.sound only (PBlk_mul_entry uses classical
  ite instance; allowed trio).

## Audit receipts (this lane)
audit/allDiag.lean, audit/allSrc.lean, audit/allProd.lean; receipts in receipt/.

## Paid so far
baseline rebuild+audit (3 modules), product entry theorem.

## Unpaid (exact)
- closure: H=max(b,c),U=min(b+e,c+f); product=0 / =B(A,C,E); nonzero iff overlap;
  zero-absorption; identity laws.
- source-level product translation d'',k'',m'' incl printed (24) bounds.
- NZ_n actual finite set; psi(n)=card of ordered pairs with nonzero product;
  T_n=sum_(ell) (n-ell+1)^2; 6T=n(n+1)(2n+1).
- zero-pair partition Left/Right + transpose involution; psi+2D=T^2.
- gap bijection; D_n=sum binom(n-a-b+2,2)(n-a+1)(n-b+1); binomial evaluation;
  720D=n(n-1)(n+1)(n+2)(19n^2+19n+6); 36T^2=...; 120psi=(n+1)^7-n^7-(n+1)^3+n^3; n=1 case.
- final results/352496.json, SUMMARY.md, manifest, frozen-after, receipt inventory.
