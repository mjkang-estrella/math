#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Reviewer arithmetic for ANS263 contribution gate. Exact rationals; not a proof.
# Question: is the integrated-annulus L2 device in author eq. (12) needed, or does
# the source E pointwise-density L2 route (with its packet-volume loss) also close
# once the adaptive width T>=u^b is used?  Also records which margins are binding.
from fractions import Fraction as Q
import json

A, b, w = Q(99, 100), Q(1, 10000), Q(1, 100000)
alpha = A - 15 * b            # author bad-band exponent on u=Dr^7
eta = 40 - 15 * w             # author bad-band exponent on r
alpha0 = A - 9 * b

out = {}
# Author integrated route: E int 1_bad mu <= r^-3 (u^alpha + r^eta)^(1/2).
# u-term: D^(alpha/2) r^(7alpha/2-3); geometric in r iff 7alpha/2-3>0; top scale r~s
# gives s^3 * s^-3 * e^(alpha/2).
out['integrated_r_exponent'] = 7 * alpha / 2 - 3
assert out['integrated_r_exponent'] > 0
# Source-E pointwise route: ||mu_j(y)||_2 <= C (rT)^-3 r^-3, volume r^3, so an extra
# T^-3 <= u^(-3b) (using T>=u^b) or <= r^(-3w) (using T>=r^w).
pw_u = alpha / 2 - 3 * b
out['pointwise_u_power'] = pw_u
out['pointwise_r_exponent'] = 7 * pw_u - 3
assert pw_u > 0 and 7 * pw_u - 3 > 0           # closes as well
out['pointwise_r_branch'] = eta / 2 - 3 - 3 * w
assert out['pointwise_r_branch'] > 0
# Necessary threshold for either route: 7*alpha/2>3  <=> alpha>6/7.
out['six_sevenths_margin'] = alpha - Q(6, 7)
assert alpha > Q(6, 7)
# Initialization: s^3 Z u0^alpha0 = eps^(7 alpha0) e^alpha0 lambda^(1-7alpha0/3); need alpha0>3/7.
out['init_lambda_power'] = 1 - 7 * alpha0 / 3
assert out['init_lambda_power'] < 0
# Wrong control: A=0.85 (alpha=.8485<6/7) must fail the summation margin.
# (A first draft used A=.86, which gives .8585>6/7 and wrongly passed; retained as a note.)
bad_alpha = Q(85, 100) - 15 * b
assert 7 * bad_alpha / 2 - 3 < 0
out['wrong_control_A_0_85_r_exponent'] = 7 * bad_alpha / 2 - 3
print(json.dumps({k: str(v) for k, v in out.items()} | {
    'status': 'PASS_ARITHMETIC_ONLY',
    'reading': 'Both integrated and pointwise budgets close; the integrated device is a convenience, not a necessity.'}, indent=1))
