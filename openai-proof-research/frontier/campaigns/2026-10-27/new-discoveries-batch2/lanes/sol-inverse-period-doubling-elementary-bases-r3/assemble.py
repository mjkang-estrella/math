from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).parent
old=(L/'frozen/00-PROOF.md').read_text()
prefix=old.split('## 4. Every base and the original question')[0]
prefix=prefix.replace('# Ordinary solution proposed; HOLD pending independent review','# Revised elementary ordinary solution; HOLD pending independent review')
prefix=prefix.replace('in Proposition15','following Definition15')
prefix=prefix.replace('The new argument is the first-threshold endpoint calculation and the synchronized pumping contradiction below.','The inherited r242 argument is the first-threshold endpoint calculation and synchronized pumping contradiction. This revision adds the complete gap alphabet and elementary arbitrary-base reduction proposed by root; it does not claim a new discovery or campaign acceptance.')
prefix=prefix.replace('The scientific sources and exact copied hashes are in bindings.json.','Scientific input hashes are in bindings.json and immutable-source-references.json; the latter reuses verified frozen primary bodies without recursive duplication.')
tail='''## 4. From arbitrary-base automaticity to recognizable records

Suppose g is k-automatic for any integer k>=2, and put E(x) iff g_x=2. Define Next(x,y) exactly as in Section 3, now in base k. Define

    Gap(x,d): exists y (Next(x,y) and y=x+d).
    Record(x,d): Gap(x,d) and
        not exists z,e (z<x and Gap(z,e) and e>=d).
    V(d): d>5 and exists x Record(x,d).

These are first-order predicates over (N,+,<,E); no powers predicate is present. Record compares EVERY earlier consecutive gap, including earlier gaps ending after the current starting point if such existed; Next makes the definition unambiguous. It is the strict record predicate, so equal earlier gaps prevent another record.

For completeness, the regular-language closure here works in every base. Encode tuples LSD first, padding all coordinates to a common length and permitting arbitrarily many final all-zero columns. Addition is recognized by a finite carry automaton with initial and final carry zero, order by finite comparison, and E by reversal of its canonical DFA plus padding normalization. Boolean operations are taken relative to the universe of padded tuples representing nonnegative integers; use complete DFAs for complement. For existential elimination, project away the witness track, obtaining a regular language K. A witness might require more digits than the visible coordinates. Hence replace K by (K / Z*) Z*, where Z is the all-zero column in the remaining tracks and / is right quotient. This both deletes excess padding needed only for the witness and permits all further padding. Intersect with the nonempty tuple universe (or include the empty all-zero encoding consistently) after each operation. Right quotient by a regular language is regular, as seen by marking states from which some word of that language reaches a final state. This gives exactly all padded representations of the quantified relation, including witnesses of arbitrary length. Reversal gives MSB representations; regular canonical intersection then gives k-recognizability of the value set V. This is also the automaton construction in Charlier–Rampersad–Shallit Section 2, rather than an inference from decidability alone.

By the complete gap classification above, V={D_t:t>=3}. The Presburger filter d=4q+1 selects precisely the even t>=4: even t gives D_t=2^t+1 congruent 1 mod 4, odd t>=3 gives congruence 3. The translation

    P(n): exists d (V(d) and exists q (d=4q+1) and d=n+1)

therefore defines exactly {4^m:m>=2}. It uses only multiplication by the FIXED constant 4, expressed by repeated addition. There is no external predicate for powers of two in base k. Finite initial exceptions could equally be removed by a fixed cutoff, but none occur with this d>5 definition. Thus P is k-recognizable.

'''
ending='''## 6. All-base endpoint, without Durand

The elementary lemma applied to P shows k=2^h for some h>=1. A k-automatic g would then be 2-automatic. Here is the finite-language base conversion: for each output letter, take its regular language of canonical base-2^h integers and replace every digit by its h-bit binary block (a fixed word homomorphism). This regular image represents the same integers with fewer than h extra initial zeros. Take left quotient by 0* and intersect with canonical binary words; handle index zero separately as a singleton. These regular languages for the output fibers give a binary DFAO, contradicting Section 3. Equivalently this is the published Proposition 3 base-power equivalence. No general Cobham theorem is needed for this step.

Finally assume that the ZERO enumeration b were k-regular over Z for some integer k>=2. Published Proposition 3 gives regularity of its first difference g, and finite-valued k-regular sequences are k-automatic. The difference takes only values 1 and 2 by Section 1. The contradiction just established excludes this possibility for every k>=2. Thus b is not k-regular for any integer k>=2, the full negative answer to Problem 27. QED (ordinary proof proposed; independent review of this revision pending).

The accepted-for-mathematics r242/Durand route is preserved verbatim at frozen/00-PROOF.md and in its untouched original lane. This revision uses neither Durand/nonprimitive substitutions nor any S-unit theorem. Its ordinary source dependencies remain Table 1 and Proposition 3 (plus Proposition 10 for indexing checks); the synchronized construction is proved explicitly and corroborated by the cited primary logic body. No Lean endpoint, novelty clearance or new credit is asserted.
'''
proof=prefix+'## 3A. Complete gap structure and records\n\n'+(L/'GAP-LEMMAS.md').read_text().split('\n',1)[1]+'\n'+tail+'## 5. Elementary dependence lemma\n\n'+(L/'ELEMENTARY-BASE-LEMMA.md').read_text().split('\n',1)[1]+'\n'+ending
(L/'PROOF.md').write_text(proof)
print('Revised complete ordinary proof written; old proof preserved.')
