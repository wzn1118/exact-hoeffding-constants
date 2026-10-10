#!/usr/bin/env python3
"""Re-derive the fixed-(m,s) hypergeometric proxy asymptotic coefficients.

Exact polynomial and rational identities; requires SymPy. All parameters are
symbolic. Numerical computations are not used to certify the theorems.
"""
import sympy as S
from sympy.functions.combinatorial.numbers import stirling
m,s,e=S.symbols('m s e')
N=1/e
k=(N-s)/2
fac=[S.prod((m-i)*(k-i)/(N-i) for i in range(j)) for j in range(5)]
raw=[S.cancel(sum(stirling(j,h,kind=2)*fac[h] for h in range(j+1))) for j in range(5)]
mean=raw[1]
k2=S.factor(raw[2]-mean**2)
k3=S.factor(raw[3]-3*mean*raw[2]+2*mean**3)
k4=S.factor(raw[4]-4*mean*raw[3]+12*mean**2*raw[2]-3*raw[2]**2-6*mean**4)
expected_k2=m*S.Rational(1,4)*(1-s**2*e**2)*(1-m*e)/(1-e)
expected_k3=expected_k2*s*e*(1-2*m*e)/(1-2*e)
assert S.cancel(k2-expected_k2)==0
assert S.cancel(k3-expected_k3)==0
assert S.simplify(S.limit(k4,e,0)+m/S.Integer(8))==0
assert S.simplify(S.limit((k4+m/S.Integer(8))/e,e,0)-m*(m-1)/2)==0
print('PASS: exact 2nd and 3rd cumulant identities; 4th-cumulant coefficients')
# t*(e) = 4se + O(e^2), and 5th cumulant vanishes at e=0.
t=4*s*e
sigma_approx=k2+(k3*t)/3+(k4*t*t)/12
R=S.cancel(4*sigma_approx/(m*(1-m*e)))
series=S.series(R,e,0,4).removeO().expand()
target=1+e+(1-s*s/S.Integer(3))*e**2+(1-(2*m-1)*s*s/S.Integer(3))*e**3
assert S.simplify(series-target)==0,(S.factor(series-target))
L=S.series(1/((1/e-1)*S.atanh(e)),e,0,4).removeO()
assert S.simplify(L-(1+e+S.Rational(2,3)*e**2+S.Rational(2,3)*e**3))==0
print('PASS: unrestricted symbolic m,s third-order proxy expansion')
assert S.simplify((L-series).subs(s,1).coeff(e,3)-2*(m-1)/3)==0
print('PASS: exact singleton-minus-fixed-m third-order coefficient')
