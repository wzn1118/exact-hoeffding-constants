"""Symbolic curvature identities, coefficient positivity, and Jacobi factorization."""
import sympy as s
from math import factorial, comb

j,h,r,u,v,x = s.symbols('j h r u v x')
m=j+h; N=2*j+h+r;T=N-1;L=N-j-1;D=h-r
A=j*j*(j-1)-T*x*x
E=L*(L+1)-2*j
Q0=(j-u)*(m-u)-v*(j+m-2*u-1)
z=v*(r+2*u)/Q0
F=s.cancel(((1-z)*(v+u*u)+(r+(j+m)*z)*u-j*m*z)*Q0)
B=j*(N-j)/(4*T)
assert s.simplify(s.Poly(F,v).coeff_monomial(v*v)+T)==0
assert s.simplify(F.subs(v,0)-u*(j-u)*(r+u)*(m-u))==0
left=16*T*F.subs({v:B,u:(j+x)/2})
right=-A*(D-x)**2-(L+1)*(2*j*x*D+E*x*x)
assert s.factor(left-right)==0
print('PASS: stationarity polynomial, constant term, complete-square identity (all symbolic).')

a,S = s.symbols('a S')
J=a+3;LL=J-1+S;TT=LL+J;EE=LL*(LL+1)-2*J
K=s.expand(EE**2*((J-1)*LL-1)-4*S*S*LL*TT)
by_S=s.Poly(K,S)
coeff_by_s={exps[0]:s.factor(co) for exps,co in by_S.terms()}
assert set(coeff_by_s)==set(range(6))
assert all(c>=0 for _,c in s.Poly(K,a,S).terms())
expected={
 0:a**2*(a+1)*(a+3)**3,
 1:a*(a+3)**2*(5*a*a+16*a+10),
 2:10*a**4+80*a**3+213*a*a+202*a+35,
 3:10*a**3+64*a*a+117*a+52,
 4:5*a*a+22*a+19,
 5:a+2
}
assert all(s.expand(coeff_by_s[k]-expected[k])==0 for k in range(6))
assert s.factor(LL**2*(J-1)-2*LL-J).subs({a:0,S:0})==1
print('PASS: universal two-variable positivity certificate (all coefficients exact).')
for deg in range(1,9):
 for hh in range(0,4):
  for rr in range(0,4):
   zz=s.symbols('zz')
   original=sum(s.binomial(deg,i)*s.ff(deg+hh,i)*s.ff(rr+deg,deg-i)*zz**i for i in range(deg+1))
   jac=factorial(deg)*(1-zz)**deg*s.jacobi(deg,rr,hh,(1+zz)/(1-zz))
   assert s.cancel(original-jac)==0,(deg,hh,rr)
print('PASS: Jacobi identity for 128 parameter combinations.')
print('PASS: all symbolic identities.')
