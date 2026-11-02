#!/usr/bin/env python3
"""Exact scalar certificate at x = B = (261/256)^256 (MultiAgency extension of
Chen/Euler's bound-111 checker, which floors x to 141).

The bound-111 paper itself states C(B) > C(141); this evaluates the same
closed form at the rational x = B exactly. All x-independent checks are
carried over verbatim from check_scalar.py (upstream authorship preserved);
new checks are marked _B. Arithmetic certificate only — the structural
argument (OpenAI + Shea) remains prose, unformalized.
"""
from fractions import Fraction as F
import json

rho, h, t, kappa = F(93, 256), F(3, 4), F(23, 2**18), F(164)
mu, nu = F(105, 8), F(113, 8)
u, w, v, d = F(1, 864), F(1, 4000), F(1, 624), F(253, 250)
K, B = kappa + nu, F(261, 256)**256
p = rho + (1 - rho)*t
A = rho*(3 + 4*v/3)
zeta = (1 - p)/(1 + p)
log_lower = 2*sum((zeta**(2*j + 1)/F(2*j + 1) for j in range(4)), F(0))
b_y = (F(2, 3)*u*(1/rho - 1) + w)/(1 + u) + 2*v
gamma = rho/4 - b_y/d
epsilon, a0 = mu*rho/kappa + u/d, 1/d


def C_of(x):
    L = epsilon + K*t + (K*t + K*rho/kappa)/(x - 1)
    s = (1 - h)*(gamma - L/h)
    return (1 - t)*((x - 1)/x)**2*t*s/(5*K), s, L


C141, s141, L141 = C_of(F(141))
CB, sB, LB = C_of(B)
Cstar = F(4084754449786906742230661, 8009094702029267287249256448000000)

checks = {
    # x-independent (verbatim from upstream check_scalar.py)
    "p_exact": p == F(24383141, 67108864),
    "p_quarter_bound": p > F(3, 4)**4,
    "generator_tilt": A**8*p**105 < (u*v)**8,
    "witness_tilt": (1 - p)**8*p**113 < (w*v)**8,
    "log_lower": log_lower > d,
    "gamma_exact": gamma == F(69959099203, 812800834560),
    "epsilon_exact": epsilon == F(69328715, 2294341632),
    "positive_gamma": 0 < gamma <= rho/4,
    "maximum_branch_cancellation": (1 - t)*(gamma*kappa + a0)/K < F(1, 4),
    "phase_denominator": 256*(F(261, 256) - 1) == 5,
    # upstream reproductions at x=141
    "positive_s141": s141 == F(3932831273804099, 747774506088529920) and s141 > 0,
    "C141_exact": C141 == F(165971304277649481670619, 324956758716416046811841770291200),
    "strict_improvement_upstream": C141 > Cstar,
    # new: the evaluation at B
    "B_greater_than_141": B > 141,
    "B_exact": B == F(261, 256)**256,
    "sB_positive": sB > 0,
    "sB_exceeds_s141": sB > s141,
    "CB_exceeds_C141": CB > C141,
    "CB_exceeds_Cstar": CB > Cstar,
}
assert all(checks.values()), {k: val for k, val in checks.items() if not val}
rel = (CB - C141)/C141
print(json.dumps({
    "checks": checks,
    "C141_upstream": str(C141),
    "CB_new": str(CB),
    "CB_decimal": format(float(CB), '.17g'),
    "C141_decimal": format(float(C141), '.17g'),
    "relative_gain_over_C141": str(rel),
    "relative_gain_decimal": format(float(rel), '.6g'),
    "difference_CB_minus_Cstar": str(CB - Cstar),
    "status": "scalar checks pass at x=B; arithmetic certificate only",
}, indent=2))
