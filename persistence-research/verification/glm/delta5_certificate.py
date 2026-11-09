"""delta5_certificate.py — independent certificate that F_5 contains NO 7-smooth
member for any number of inserted 1s (any L >= 1, 0 <= e < L).

Method (distinct from glm2.stage0's meet-in-the-middle):
  * every member is odd (R_L odd, 4*10^e even) so t = 0 (also Lemma 1/parity);
  * if 9n = 3^(u+2) 7^w exactly, then mod M0 the value
        V(L mod 12, e mod 12) = 10^L + 36*10^e - 1 mod M0
    must lie in the image set {3^U 7^W mod M0 : 0 <= U < 9900, 0 <= W < 900},
    built here EXPLICITLY as a Python set (8,910,000 elements);
  * the certificate is the list of the 144 values V, none in the image.
Memory: the set is ~400 MB; run under the 3 GB cap.

Run under: bash -c 'ulimit -v 3000000; python3 -I delta5_certificate.py'
"""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from glm2 import M0, O3_0, O7_0


def main():
    t0 = time.time()
    image = set()
    x = 1
    pow3 = []
    for U in range(O3_0):
        pow3.append(x)
        x = x * 3 % M0
    x = 1
    pow7 = []
    for W in range(O7_0):
        pow7.append(x)
        x = x * 7 % M0
    for a in pow3:
        for b in pow7:
            image.add(a * b % M0)
    print(f"image set: {len(image)} elements ({time.time()-t0:.1f}s)", flush=True)
    p10 = [pow(10, i, M0) for i in range(12)]
    misses = []
    for e12 in range(12):
        for L12 in range(12):
            V = (p10[L12] + 36 * p10[e12] - 1) % M0
            if V in image:
                misses.append((L12, e12, V))
    print(f"144 residues checked: {len(misses)} in image ({time.time()-t0:.1f}s)")
    assert not misses, f"FOUND image hits: {misses}"
    with open("delta5_certificate.json", "w") as f:
        json.dump(dict(delta=5, M0=M0, O3_0=O3_0, O7_0=O7_0,
                       image_size=len(image),
                       residues=[(L12, e12) for e12 in range(12)
                                 for L12 in range(12)],
                       verdict="no (L mod 12, e mod 12) class survives stage 0; "
                               "F_5 has no 7-smooth member for any L >= 1, 0 <= e < L"),
                  f)
    print("CERTIFICATE OK: no stage-0 survivor for delta=5 -> F_5 has no 7-smooth "
          "member at any digit length (complete family decision).")


if __name__ == "__main__":
    main()
