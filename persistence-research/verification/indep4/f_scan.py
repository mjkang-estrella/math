# F: independent smooth-lattice scan.  All n = 2^i 3^j 7^k < 10^D with decimal digit product == 14112.   python3 -I f_scan.py D
import sys
D = int(sys.argv[1]); T = 14112
lim = 10 ** D; mem = []; cnt = 0
a = 1
while a < lim:
    b = a
    while b < lim:
        n = b
        while n < lim:
            cnt += 1
            s = str(n)
            if '0' not in s and '5' not in s:
                p = 1
                for ch in s:
                    p *= ord(ch) - 48
                    if p > T: break
                if p == T: mem.append(n)
            n *= 7
        b *= 3
    a *= 2
print('scanned', cnt, 'smooth numbers < 10^%d; members with digit product %d: %s' % (D, T, sorted(mem)))
