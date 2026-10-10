#!/usr/bin/env python3
"""Symbolic cumulants, optimal-tilt coefficients, proxy expansions, and imbalance identities."""
import sympy as S
from sympy.functions.combinatorial.numbers import stirling

m,s,e=S.symbols('m s e')
def trunc(x,n=5):
    return S.series(S.expand(x),e,0,n).removeO().expand()
def mul(a,b):
    return trunc(a*b)

fac=[S.Integer(1)]
for j in range(1,7):
    f=S.Integer(1)
    for i in range(j):
        f=mul(f,(m-i)*(1-(s+2*i)*e)/2*sum((i*e)**h for h in range(5)))
    fac.append(f)
raw=[S.Integer(1)]+[S.expand(sum(stirling(j,h,kind=2)*fac[h] for h in range(j+1))) for j in range(1,7)]
kap=[0]
for j in range(1,7):
    kap.append(trunc(raw[j]-sum(S.binomial(j-1,h-1)*mul(kap[h],raw[j-h]) for h in range(1,j))))
expected={
 2:m/S.Integer(4)*(1-(m-1)*e-(m+s*s-1)*e**2+(m-1)*(s*s-1)*(e**3+e**4)),
 3:m*s/S.Integer(4)*(e-3*(m-1)*e**2+(2*m*m-9*m-s*s+7)*e**3),
 4:-m/S.Integer(8)+m*(m-1)*e/2+m*(-6*m*m+19*m+4*s*s-13)*e**2/8,
 5:-m*s*e/2,
 6:m/S.Integer(4),
}
for j,depth in [(2,5),(3,4),(4,3),(5,2),(6,1)]:
    assert S.expand(trunc(kap[j],depth)-expected[j])==0,(j,'cumulant')
print('PASS: factorial-moment recursion gives all stated cumulant coefficients (free m,s).')

t=4*s*e+4*s*(m-1)*e**2+4*s*(6*m+s*s-6)*e**3/3
Qt=kap[3]/3+kap[4]*t/6+kap[5]*t*t/20+kap[6]*t**3/90
assert S.expand(trunc(Qt,4))==0
Q=kap[2]+kap[3]*t/3+kap[4]*t*t/12+kap[5]*t**3/60+kap[6]*t**4/360
R=trunc(mul(trunc(Q),4/m*sum((m*e)**h for h in range(5))))
target=1+e+(1-s*s/3)*e**2+(1-(2*m-1)*s*s/3)*e**3+(1-(4*m*m-2*m-1)*s*s/3-4*s**4/45)*e**4
assert S.expand(R-target)==0
L=S.series(e/((1-e)*S.atanh(e)),e,0,5).removeO()
gap=2*(m-1)*e**3/3+2*(m-1)*(2*m+1)*e**4/3
assert S.expand(L-R.subs(s,1)-gap)==0
print('PASS: third-order optimizer, fourth-order proxy, and fourth-order gap (free m,s).')

N,d=S.symbols('N d')
k=N*(1-d)/2
fs=[S.prod((m-i)*(k-i)/(N-i) for i in range(j)) for j in range(5)]
rs=[S.cancel(sum(stirling(j,h,kind=2)*fs[h] for h in range(j+1))) for j in range(5)]
k2=S.factor(rs[2]-rs[1]**2)
k3=S.factor(rs[3]-3*rs[1]*rs[2]+2*rs[1]**3)
k4=S.factor(rs[4]-4*rs[1]*rs[3]+12*rs[1]**2*rs[2]-3*rs[2]**2-6*rs[1]**4)
B=m*(N-m)/(4*(N-1))
D=N*N-N-3*m*(N-m)
c=-B*D/(2*(N-3)*(N-1))
b=B*(N-2*m)/(N-2)
assert S.cancel(k2-B*(1-d*d))==0
assert S.cancel(k3-B*(1-d*d)*d*(N-2*m)/(N-2))==0
assert S.cancel(k4.subs(d,0)-c)==0
A=S.cancel(4*N/(m*(N-m))*(B+b*b/(3*c)))
extra=2*N*N*(N-4)*(m-1)*(N-m-1)/(3*(N-2)**2*(N-1)*D)
assert S.cancel(A-N/(3*(N-1))-extra)==0
T=4*(N-2*m)*(N-3)*(N-1)/((N-2)*D)
assert S.cancel(T+2*b/c)==0
print('PASS: exact finite-N imbalance coefficient and strictly positive separation (free N,m).')

# Verify the compact-proportion correction without asymptotic optimization.
p,z=S.symbols('p z', positive=True)
q=1-p
Z=q+p*z
d0=q-p
bracket=1-(p*z*z+q)/(Z*Z)
assert S.cancel(bracket.subs(z,(q/p)**2)+d0*d0/(p*q))==0
x=S.symbols('x')
g=x/S.atanh(x)
h=g/x**2*(x/((1-x*x)*S.atanh(x))-1)
assert S.limit(h,x,0)==S.Rational(2,3)
print('PASS: flipped-binomial correction and removable balanced coefficient 2/3.')
print('PASS: all fourth-order symbolic identities.')
