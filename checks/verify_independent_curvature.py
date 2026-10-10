#!/usr/bin/env python3
"""Exact polynomial certificates for the uniform tilted-curvature theorem."""
import sympy as s

j, h, r, x = s.symbols('j h r x')
N, m = 2*j+h+r, j+h
L, T, D, S = N-j-1, N-1, h-r, h+r
u, v = s.symbols('u v')
B = j*(N-j)/(4*T)
D0 = (j-u)*(m-u)-v*(j+m-2*u-1)
F = ((D0-v*(r+2*u))*(v+u*u)+r*D0*u
     +(j+m)*v*(r+2*u)*u-j*m*v*(r+2*u))
A = j*j*(j-1)-T*x*x
E = L*(L+1)-2*j
rhs = A*(D-x)**2+(L+1)*(2*j*D*x+E*x*x)
assert s.cancel(-16*T*F.subs({u:(j+x)/2,v:B})-rhs) == 0
print('PASS: stationary curvature identity')

a, S0 = s.symbols('a S0')
j0, L0 = a+3, a+2+S0
E0 = L0*(L0+1)-2*j0
K = s.expand(E0**2*((j0-1)*L0-1)-4*S0**2*L0*(L0+j0))
expected = (
    a*a*(a+1)*(a+3)**3
    +a*(a+3)**2*(5*a*a+16*a+10)*S0
    +(10*a**4+80*a**3+213*a*a+202*a+35)*S0**2
    +(10*a**3+64*a*a+117*a+52)*S0**3
    +(5*a*a+22*a+19)*S0**4+(a+2)*S0**5
)
assert s.expand(K-expected) == 0
assert all(c >= 0 for c in s.Poly(K,a,S0).coeffs())
q_bound = s.expand((j0-1)*L0**2-2*L0-j0)
assert all(c >= 0 for c in s.Poly(q_bound,a,S0).coeffs())
print('PASS: all-degree coefficient positivity and small-A threshold')
