import sympy as S
n,m,k,d,y,z,v,u,j,r=S.symbols('n m k d y z v u j r')
M=m*(n-m)/(n-1); a=(n-2*m)/(n-2); mu=m*(1-d)/2; V=M*(1-d*d)/4
P=V+a*d*y-a*a/M*y*y
A=u*(u+n-k-m); C=(k-u)*(m-u)
F=-(n-1)*v*v+(A+C-S.diff(A,u)*C+S.diff(C,u)*A)*v+A*C
J=S.together(F.subs({u:mu+y,k:n*(1-d)/2,v:P})+n*y*P*S.diff(P,y))
G=n*n*(m-1)*(n-m-1)/(4*(n-2)**2*(n-1))
W=(n-4)+3*n*d*d-4*n*a*d*z+((n+1)*a*a-M)*z*z
assert S.factor(J+G*y*y*W.subs(z,2*y/M))==0
print('PASS variance-curve residual identity')
b=(n-m)/(n-2); c=(n-m)*(3*n*n-4*n-4*m*(n-1))/((n-1)*(n-2)**2)
E=1-d*d+4*b*d*z-c*z*z
D0=m*(m-1)/(4*(n-1))
assert S.factor(((mu+y)*(m-mu-y)/m-P).subs(y,M*z/2)-D0*E)==0
print('PASS Poisson-binomial admissibility identity')
delta=(n-2*m)/n
lam=(m*m-m*n+3*m+n*n-4*n)/(2*(n-m))
alpha=(n-4-lam)/delta**2
AA=3*n+lam+alpha;BB=-2*n*a-2*lam*b;CC=(n+1)*a*a-M+lam*c
assert S.factor(W-lam*E-alpha*(delta**2-d*d)-AA*d*d-2*BB*d*z-CC*z*z)==0
print('PASS quadratic certificate identity')
U=n*n-2*n-m*m-m*n+3*m
Vv=m**3-6*m*m-2*m*n*n+14*m*n-3*m+n**3-7*n*n+6*n
assert S.factor(AA*CC-BB*BB-n*n*U*Vv/((n-2*m)**2*(n-2)**2*(n-1)))==0
print('PASS positive determinant factorization')
polys=[2*(n-m)*lam,2*(n-m)*(n-4-lam),U,Vv]
expected=[3*j*j+3*j*r+13*j+r*r+5*r+12,j*j+3*j*r+3*j+r*r+5*r,j*j+3*j*r+5*j+r*r+7*r+6,j**3+4*j*j*r+3*j*j+4*j*r*r+10*j*r+r**3+5*r*r]
for poly,ex in zip(polys,expected):
 assert S.factor(poly.subs(n,2*m+r).subs(m,j+3)-ex)==0
print('PASS all-degree nonnegative-coefficient certificates')
P_u=P.subs(y,u-mu).subs(d,1-2*k/n)
P0=k*m*(m-1)*((n-m)*(n-2)-k*(m-1))/((n-m)*(n-2)**2*(n-1))
Pm=m*(n-k)*(m-1)*(k*(m-1)+(n-2*m)*(n-1))/((n-m)*(n-2)**2*(n-1))
assert S.factor(P_u.subs(u,0)-P0)==0
assert S.factor(P_u.subs(u,m)-Pm)==0
print('PASS endpoint positivity identities')
# Singular-free differential identity for the true variance function
# ztilt=(A+v)/(C+v), du/dt=v => d/du log(ztilt)=1/v
# rearrangement yields (C-A)*v*v_u=F.
vu=S.symbols('vu'); expanded=S.expand(v*((S.diff(A,u)+vu)*(C+v)-(S.diff(C,u)+vu)*(A+v))-(A+v)*(C+v))
assert S.factor(expanded-((C-A)*v*vu-F))==0
assert S.factor(C-A+n*(u-m*k/n))==0
print('PASS differential identity and its orientation')
