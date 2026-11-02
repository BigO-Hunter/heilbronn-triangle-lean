#!/usr/bin/env python3
"""Exact scalar certificate only; this does not prove the universal matroid interface."""
from fractions import Fraction as F
import json

rho, h, t, kappa = F(93,256), F(3,4), F(23,2**18), F(164)
mu, nu = F(105,8), F(113,8)
u, w, v, d = F(1,864), F(1,4000), F(1,624), F(253,250)
K, B = kappa+nu, F(261,256)**256
p = rho+(1-rho)*t
A = rho*(3+4*v/3)
zeta = (1-p)/(1+p)
log_lower = 2*sum((zeta**(2*j+1)/F(2*j+1) for j in range(4)), F(0))
b_y = (F(2,3)*u*(1/rho-1)+w)/(1+u)+2*v
gamma = rho/4-b_y/d
epsilon, a0 = mu*rho/kappa+u/d, 1/d
L141 = epsilon+K*t+(K*t+K*rho/kappa)/140
s141 = (1-h)*(gamma-L141/h)
C141 = (1-t)*F(140,141)**2*t*s141/(5*K)
Cstar = F(4084754449786906742230661,8009094702029267287249256448000000)
checks = {
    "p_exact": p == F(24383141,67108864),
    "p_quarter_bound": p > F(3,4)**4,
    "generator_tilt": A**8*p**105 < (u*v)**8,
    "witness_tilt": (1-p)**8*p**113 < (w*v)**8,
    "log_lower": log_lower > d,
    "B_greater_than_141": B > 141,
    "gamma_exact": gamma == F(69959099203,812800834560),
    "epsilon_exact": epsilon == F(69328715,2294341632),
    "positive_gamma": 0 < gamma <= rho/4,
    "positive_s141": s141 == F(3932831273804099,747774506088529920) and s141 > 0,
    "maximum_branch_cancellation": (1-t)*(gamma*kappa+a0)/K < F(1,4),
    "C141_exact": C141 == F(165971304277649481670619,324956758716416046811841770291200),
    "strict_improvement": C141 > Cstar,
    "difference_exact": C141-Cstar == F(116935879834753076315538659,159228811771043862937802467442688000000),
    "phase_denominator": 256*(F(261,256)-1) == 5,
}
assert all(checks.values()), checks
print(json.dumps({"checks":checks, "C141":str(C141), "Cstar":str(Cstar),
                  "difference":str(C141-Cstar), "status":"scalar checks pass; arithmetic certificate only"}, indent=2))

