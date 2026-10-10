"""Exact identities for the slice reduction and the variance--proxy parity gap."""
import sympy as s
n,m,t,x,p=s.symbols('n m t x p',positive=True)
a,b,c=s.symbols('a b c',real=True)
eta=[1/((a-b)*(a-c)),1/((b-a)*(b-c)),1/((c-a)*(c-b))]
assert s.factor(sum(eta))==0
assert s.factor(a*eta[0]+b*eta[1]+c*eta[2])==0
print('PASS: the three-coordinate direction preserves sum and squared norm to first order.')
levels=[(n-m)*t/n,-m*t/n]
assert s.factor(m*levels[0]+(n-m)*levels[1])==0
assert s.factor(m*levels[0]**2+(n-m)*levels[1]**2-m*(n-m)*t**2/n)==0
print('PASS: the two-level squared norm and variational normalization.')
assert s.simplify(s.diff(x-(1-x*x)*s.atanh(x),x)-2*x*s.atanh(x))==0
L=x/((1-x)*s.atanh(x));D=1+x
assert s.series(L-D,x,0,5).removeO()==2*x**2/3+2*x**3/3+s.Rational(26,45)*x**4
print('PASS: exact parity-gap integral identity and fourth-order coefficients.')
q=1-p
assert s.factor(q+p*(q/p)**2-q/p)==0
podd=(n-1)/(2*n)
assert s.factor(1-2*podd-1/n)==0
norm=(1-1/n)**2+(n-1)/n**2
assert s.factor(norm-(n-1)/n)==0
print('PASS: the explicit odd nonzero-tilt equality and contrast norm.')
z=s.symbols('z')
central=4*m*(n-m)/n
raw=m*(1-(2*m-n)/n)**2+(n-m)*(-1-(2*m-n)/n)**2
assert s.factor(raw-central)==0
print('PASS: cube-vertex variance formula for each success count.')
