#!/usr/bin/env python3
# Independent reviewer arithmetic for ANS263 proof round 1. MIT.
# Exact rational margins only. This is NOT a proof of any analytic step;
# it checks the finite exponent bookkeeping the reviewer re-derived by hand.
# Uses assert: run WITHOUT -O.
from fractions import Fraction as Q
import json, sys


def margins(A=Q(99, 100), b=Q(1, 10000), w=Q(1, 100000)):
    """Every quantity here must be > 0 for the reviewer's re-derivation to close."""
    alpha = A - 15 * b             # net loss T^-15 against u^A           (proof eq. 3)
    alpha0 = A - 9 * b             # initial net loss T^-9                 (proof eq. 11)
    eta = 40 - 15 * w
    eta0 = 40 - 9 * w
    return {
        # (4): D/p * a^7 <= u^(1-A) needs A<1; the tilt-log term r^(-2.02)*r^7.
        'tilt_u_power': 1 - A,
        'tilt_log_r_power': Q(498, 100),
        # (6): patch errors / a^-7 are a^.1, a^2.8, a^.6, a^1.6; absorbed in theta's r^.02.
        'patch_sqrt_beta_minus_theta_r': Q(1, 10) - Q(2, 100),
        'patch_bf2_minus_theta_r': Q(6, 10) - Q(2, 100),
        # (7) Coulomb duality: theta^(1/4) * T^(-5/2), paired branch by branch.
        'duality_u': (1 - A) / 4 - Q(5, 2) * b,
        'duality_r': Q(2, 100) / 4 - Q(5, 2) * w,
        # (7) noisy-array sandwich r^.01 T^-4 and fine smear r^.2 T^-4 (T >= r^w branch).
        'sandwich_obs': Q(1, 100) - 4 * w,
        'sandwich_fine': Q(2, 10) - 4 * w,
        # ell_j / t -> 0 : r^.01 / T, T >= r^w.
        'obs_below_master': Q(1, 100) - w,
        # (8) negative field: theta * T^-3.
        'negfield_u': (1 - A) - 3 * b,
        'negfield_r': Q(2, 100) - 3 * w,
        # (9) potential: theta^(1/2) * T^(-1/2).
        'potential_u': (1 - A) / 2 - b / 2,
        'potential_r': Q(2, 100) / 2 - w / 2,
        # (12)-(13): geometric sum increasing in r_j requires 7 alpha/2 - 3 > 0, i.e. alpha > 6/7.
        'bad_band_u': Q(7, 2) * alpha - 3,
        'bad_band_r': eta / 2 - 3,
        # (13): lambda exponent 1 - 7 alpha0/3 must be NEGATIVE; store its negation.
        'init_lambda_u': Q(7, 3) * alpha0 - 1,
        'init_lambda_r': eta0 / 3 - 1,
        # alpha <= 1 so that u <= u^alpha absorbs the cap failure C(u + r^40).
        'alpha_le_1': 1 - alpha,
    }


def closes(d):
    return all(v > 0 for k, v in d.items() if k != 'alpha_le_1') and d['alpha_le_1'] >= 0


def tf_constant():
    # k = (5T/3)^(-3/2) with T = (3/10)(3 pi^2)^(2/3): k = 2^(3/2)/(3 pi^2).
    # A_* = 81 pi^2 / 8.  Track rational coefficient c and pi-power p, with sqrt(2)
    # appearing as 2^(3/2) in k and 8^(3/2)=2^(9/2) in A_*^(3/2): net 2^(3/2-9/2)=2^-3.
    # k A_*^(3/2) = [2^(3/2) / (3 pi^2)] * [81^(3/2) pi^3 / 2^(9/2)] = 729 pi / (3 * 8)
    kA = Q(729, 3 * 8)              # coefficient of pi
    assert kA == Q(243, 8)
    total = Q(4, 3) * kA            # (4 pi/3) k A^(3/2) a^-3: coefficient of pi^2
    assert total == Q(81, 2)
    # 4 pi k A_*^(1/2) = 12: [2^(3/2)/(3 pi^2)] * 4 pi * 9 pi / 2^(3/2) = 12.
    assert Q(4 * 9, 3) == 12
    # Newton: (1/4pi) \int dS/|d w - z| = 1/max(d,|z|); exterior weight 1 - r/|x| >= 1/2 for |x|>=2r.
    for r, x in ((Q(1), Q(2)), (Q(1), Q(5)), (Q(3), Q(6))):
        assert 1 - r / x >= Q(1, 2)
    assert 1 - Q(1) / Q(3, 2) < Q(1, 2)   # threshold 1.5 r would not give the factor 1/2
    return {'kA32_over_pi': str(kA), 'tail_coefficient_over_pi2': str(total)}


def geometric_prefactor(g):
    # sum_{j<=J} r_j^g with r_j = 2^(j-J) r_J is bounded by r_J^g / (1 - 2^-g) for g>0.
    # Rational controls for g = 1/2 approximations are avoided; use integer exponent controls.
    for J in (1, 5, 30):
        s = sum(Q(1, 2) ** ((J - j) * g) for j in range(J + 1))
        assert s < 1 / (1 - Q(1, 2) ** g)
    return True


def main():
    d = margins()
    assert closes(d), {k: str(v) for k, v in d.items() if v <= 0}
    assert d['bad_band_u'] == Q(1839, 4000)
    assert d['duality_u'] == Q(9, 4000)
    assert all(geometric_prefactor(g) for g in (1, 2, 3))
    tf = tf_constant()
    # Negative controls: each mutation must break a margin the reviewer relies on.
    mutations = {
        'A_equals_1_no_tilt_gain': margins(A=Q(1)),
        'A_too_small_bad_band': margins(A=Q(85, 100)),
        'b_too_large': margins(b=Q(1, 100)),
        'w_too_large_vs_obs_width': margins(w=Q(1, 100)),
    }
    failed = {}
    for name, m in mutations.items():
        assert not closes(m), name
        failed[name] = sorted(k for k, v in m.items() if (v <= 0 if k != 'alpha_le_1' else v < 0))
    print(json.dumps({
        'status': 'PASS_ARITHMETIC_ONLY',
        'margins': {k: str(v) for k, v in d.items()},
        'tf': tf,
        'negative_controls_break': failed,
        'limits': 'Exact rational bookkeeping of reviewer-rederived exponents; no analytic, source-contract or novelty validation.',
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    if sys.flags.optimize:
        print('FAIL: run without -O (assertions required)', file=sys.stderr)
        sys.exit(1)
    main()
