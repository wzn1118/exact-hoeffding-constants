#!/usr/bin/env python3
"""Fully rational proof of the failure of parity-sharpened curvature."""
from fractions import Fraction
from math import comb
N,k,m=15,7,3
z=Fraction(7,6)
weights=[Fraction(comb(k,j)*comb(N-k,m-j))*z**j for j in range(m+1)]
S=sum(weights)
mu=sum(j*w for j,w in enumerate(weights))/S
var=sum((j-mu)**2*w for j,w in enumerate(weights))/S
B=Fraction(m*(N-m),4*(N-1))
ratio=var/B
upper=Fraction(3*N*N,3*N*N+1)
assert mu==Fraction(26313,17555)
assert var==Fraction(197927856,308178025)
assert ratio==Fraction(307887776,308178025)
assert ratio-upper==Fraction(111969701,208328344900)>0
# atanh(1/N) > 1/N+1/(3N^3) => rho_N< upper exactly
print('PASS: exact rational tilted moments and strict symbolic upper-bound comparison')
print('N,k,m,z:',N,k,m,z)
print('tilted mean:',mu,'variance:',var,'curvature ratio:',ratio)
print('ratio - atanh upper:',ratio-upper)
