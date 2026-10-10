#!/usr/bin/env python3
"""Exact independent algebraic certificates for the global curvature and Laplace envelopes.

All symbolic identities are derived from explicitly reconstructed polynomial
expressions. This module imports no other manuscript checking scripts.
"""
import itertools
import math
import sympy as S

j, h, r, u, v, x, z = S.symbols('j h r u v x z', real=True)

# I. Curvature: reconstruct the tilt-elimination resultant from the ODE.
m = j + h
N = 2*j + h + r
T = N-1
L = N-j-1
D = h-r
B = j*(N-j)/(4*T)
Q = (j-u)*(m-u)-v*(j+m-2*u-1)
Z = v*(r+2*u)
# Substitute the stationary variance tilt relation z=Z/Q in the Riccati equation.
F = S.expand((Q-Z)*(v+u*u)+r*Q*u+(j+m)*Z*u-j*m*Z)
assert S.factor(S.Poly(F,v).coeff_monomial(v*v)+(N-1)) == 0
assert S.factor(F.subs(v,0)-u*(j-u)*(r+u)*(m-u)) == 0
E=L*(L+1)-2*j
A=j*j*(j-1)-T*x*x
cert=A*(D-x)**2+(L+1)*(2*j*D*x+E*x*x)
assert S.factor(-16*T*F.subs({u:(j+x)/2,v:B})-cert) == 0
print('PASS independent curvature stationary elimination and factor identity')

a,s=S.symbols('a s', nonnegative=True)
J=a+3; LL=J-1+s; TT=LL+J; EE=LL*(LL+1)-2*J
K=S.Poly(S.expand(EE**2*((J-1)*LL-1)-4*s*s*LL*TT),a,s)
assert K.total_degree()==6
assert all(c>=0 for _,c in K.terms())
assert S.factor(K.as_expr().subs({a:0,s:0}))==0
print('PASS independent curvature positivity polynomial in a=j-3, s=h+r')

# II. Laplace: reconstruct polynomial certificates in normalized variables.
n, mm, d, z0 = S.symbols('n mm d z0', real=True)
p=(1-d)/2
k=n*p
M=mm*(n-mm)/(n-1)
at=(n-2*mm)/(n-2)
mu=mm*p
y=M*z0/2
uu=mu+y
Afun=uu*(uu+n-k-mm)
Cfun=(k-uu)*(mm-uu)
# Derivatives of A,C with respect to the tilted mean.
Ader=2*uu+n-k-mm
Cder=2*uu-k-mm
G=n*n*(mm-1)*(n-mm-1)/(4*(n-2)**2*(n-1))
P=M*(1-d*d)/4+at*d*y-at*at/M*y*y
Pder=at*d-2*at*at/M*y
F2=-(n-1)*P**2+(Afun+Cfun-Ader*Cfun+Cder*Afun)*P+Afun*Cfun
W=n-4+3*n*d*d-4*n*at*d*z0+((n+1)*at*at-M)*z0*z0
# Compare coefficients of d,z0, as rational functions in the integer parameters.
def cert_zero(expr, vars=(d,z0)):
    polynomial=S.Poly(S.expand(expr), *vars)
    for monom, coeff in polynomial.terms():
        if S.cancel(coeff)!=0:
            raise AssertionError(f'coefficient {monom} = {S.factor(coeff)}')

cert_zero(F2+n*y*P*Pder+G*y*y*W)
print('PASS independent Laplace residual identity F(u,P)+n*y*P*P\'= -G*y^2*W',flush=True)

margin=(n-2*mm)/n
b=(n-mm)/(n-2)
c=(n-mm)*(3*n*n-4*n-4*mm*(n-1))/((n-1)*(n-2)**2)
E2=1-d*d+4*b*d*z0-c*z0*z0
cert_zero(uu*(mm-uu)/mm-P-mm*(mm-1)/(4*(n-1))*E2)
print('PASS independent Laplace Bernoulli admissibility identity',flush=True)

lam=(mm**2-mm*n+3*mm+n*n-4*n)/(2*(n-mm))
alpha=(n-4-lam)/margin**2
A0=3*n+lam+alpha
B0=-2*n*at-2*lam*b
C0=(n+1)*at*at-M+lam*c
certificate2=lam*E2+alpha*(margin**2-d*d)+A0*d*d+2*B0*d*z0+C0*z0*z0
cert_zero(W-certificate2)
U=n*n-2*n-mm*mm-mm*n+3*mm
V=mm**3-6*mm**2-2*mm*n*n+14*mm*n-3*mm+n**3-7*n*n+6*n
assert S.cancel(A0*C0-B0**2-n*n*U*V/((n-2*mm)**2*(n-2)**2*(n-1)))==0
print('PASS independent Laplace SOS identity and positive determinant identity',flush=True)

jj, rr=S.symbols('jj rr', nonnegative=True)
sub={n:2*(jj+3)+rr,mm:jj+3}
numpos={
 'lambda numerator':3*jj*jj+3*jj*rr+13*jj+rr*rr+5*rr+12,
 'alpha numerator':jj*jj+3*jj*rr+3*jj+rr*rr+5*rr,
 'U factor':jj*jj+3*jj*rr+5*jj+rr*rr+7*rr+6,
 'V factor':jj**3+4*jj*jj*rr+3*jj*jj+4*jj*rr*rr+10*jj*rr+rr**3+5*rr*rr,
}
actual={
 'lambda numerator':2*(n-mm)*lam,
 'alpha numerator':2*(n-mm)*(n-4-lam),
 'U factor':U,
 'V factor':V,
}
for name,expr in numpos.items():
    assert S.cancel(actual[name].subs(sub)-expr)==0,name
    assert all(c>=0 for _,c in S.Poly(expr,jj,rr).terms()),name
print('PASS independent Laplace quadrant coefficient identities',flush=True)

# III. Verify the coefficient-level Jacobi ODE independently on integer test inputs.
z=S.Symbol('z')
for degree in range(1,7):
    for hh,rr0 in itertools.product(range(0,4), repeat=2):
        M0=degree+hh
        Q0=sum(S.binomial(degree,i)*S.ff(M0,i)*S.factorial(rr0+degree)/S.factorial(rr0+i)*z**i for i in range(degree+1))
        ode=S.expand(z*(1-z)*S.diff(Q0,z,2)+(rr0+1+(degree+M0-1)*z)*S.diff(Q0,z)-degree*M0*Q0)
        assert ode==0,(degree,hh,rr0)
print('PASS independent Jacobi generating-polynomial differential equation (96 exact cases)')

# IV. Hypergeometric Laplace and curvature comparison: separate direct finite-sum test.
# Stresses negative and positive tilts; not used in any symbolic proof above.
for n0 in range(7,19):
    for m0 in range(3,n0//2+1):
        for k0 in range(m0,n0//2+1):
            if n0<=2*m0: continue
            ps=[math.comb(k0,i)*math.comb(n0-k0,m0-i)/math.comb(n0,m0) for i in range(m0+1)]
            m1=m0*k0/n0
            M1=m0*(n0-m0)/(n0-1)
            at1=(n0-2*m0)/(n0-2)
            p1=k0/n0
            for t in [-5,-2,-1,-.25,.25,1,2,5]:
                xs=[i*t+math.log(q) for i,q in enumerate(ps)]
                peak=max(xs)
                logmgf=peak+math.log(sum(math.exp(xx-peak) for xx in xs))-t*m1
                q=p1*math.exp(at1*t)+(1-p1)
                rhs=M1/(at1*at1)*(math.log(q)-p1*at1*t)
                assert logmgf<=rhs+2e-10,(n0,k0,m0,t,logmgf,rhs)
print('PASS direct finite-sum Laplace stress test N=7..18')
print('ALL independent certificate checks passed')
