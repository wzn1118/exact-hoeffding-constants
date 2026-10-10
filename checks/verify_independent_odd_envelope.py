#!/usr/bin/env python3
"""Exact algebraic certificates for the parity-uniform Laplace envelope."""
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

j, r, d, z = s.symbols('j r d z')
m, N = j+3, 2*(j+3)+r
M, a = m*(N-m)/(N-1), (N-2*m)/(N-2)
delta = (N-2*m)/N
b = (N-m)/(N-2)
c = (N-m)*(3*N*N-4*N-4*m*(N-1))/((N-1)*(N-2)**2)
E = 1-d*d+4*b*d*z-c*z*z
W = N-4+3*N*d*d-4*N*a*d*z+((N+1)*a*a-M)*z*z
lam = (m*m-m*N+3*m+N*N-4*N)/(2*(N-m))
alp = (N-4-lam)/delta**2
A0, B0, C0 = 3*N+lam+alp, -2*N*a-2*lam*b, (N+1)*a*a-M+lam*c
assert s.cancel(W-(lam*E+alp*(delta**2-d*d)+A0*d*d+2*B0*d*z+C0*z*z)) == 0
print('PASS: quadratic positivity certificate')
U = N*N-2*N-m*m-m*N+3*m
V = m**3-6*m*m-2*m*N*N+14*m*N-3*m+N**3-7*N*N+6*N
assert s.cancel(A0*C0-B0**2-N*N*U*V/((N-2*m)**2*(N-2)**2*(N-1))) == 0
print('PASS: positive determinant factorization')
forms = [
 (2*(N-m)*lam, 3*j*j+3*j*r+13*j+r*r+5*r+12),
 (2*(N-m)*(N-4-lam), j*j+3*j*r+3*j+r*r+5*r),
 (U, j*j+3*j*r+5*j+r*r+7*r+6),
 (V, j**3+4*j*j*r+3*j*j+4*j*r*r+10*j*r+r**3+5*r*r),
]
for lhs,rhs in forms:
    assert s.cancel(lhs-rhs) == 0
    assert all(c >= 0 for c in s.Poly(rhs,j,r).coeffs())
print('PASS: nonnegative coefficient decompositions')

K = QQ.frac_field('j','r')
jr, rr = K.gens
R, dd, zz = ring('d,z',K)
lift = lambda q: R.ground_new(q)
n = 2*(jr+3)+rr
mm = jr+3
half = QQ(1,2)
k = lift(n)*(1-dd)*half
p = k/lift(n)
mu = lift(mm)*p
mm0 = mm*(n-mm)/(n-1)
aa = (n-2*mm)/(n-2)
u = mu+lift(mm0)*zz*half
P = (lift(mm0)*(1-(1-2*p)**2)*QQ(1,4)
     +lift(aa)*(1-2*p)*(u-mu)-lift(aa*aa/mm0)*(u-mu)**2)
Ap = u*(u+lift(n-mm)-k)
Cp = (k-u)*(lift(mm)-u)
Aprime = 2*u+lift(n-mm)-k
Cprime = 2*u-k-lift(mm)
F = -lift(n-1)*P*P+(Ap+Cp-Aprime*Cp+Cprime*Ap)*P+Ap*Cp
Pprime = lift(aa)*(1-2*p)-lift(2*aa*aa/mm0)*(u-mu)
G = n*n*(mm-1)*(n-mm-1)/(4*(n-2)**2*(n-1))
W0 = (lift(n-4)+lift(3*n)*(1-2*p)**2
      -lift(4*n*aa)*(1-2*p)*zz+lift((n+1)*aa*aa-mm0)*zz*zz)
assert F+lift(n)*(u-mu)*P*Pprime+lift(G)*(u-mu)**2*W0 == 0
print('PASS: universal variance-curve residual identity')

E0 = (1-(1-2*p)**2+lift(4*(n-mm)/(n-2))*(1-2*p)*zz
      -lift((n-mm)*(3*n*n-4*n-4*mm*(n-1))/((n-1)*(n-2)**2))*zz**2)
admissibility = u*(lift(mm)-u)/lift(mm)-P
assert admissibility-lift(mm*(mm-1)/(4*(n-1)))*E0 == 0
print('PASS: Poisson-binomial admissibility identity')
