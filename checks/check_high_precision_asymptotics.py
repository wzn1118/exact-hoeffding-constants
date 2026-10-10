#!/usr/bin/env python3
"""90-digit calculations of the optimal tilt and variance proxy."""
import mpmath as mp
mp.mp.dps=90

def proxy_from_masses(N,m,k,guess):
    masses=[mp.binomial(k,i)*mp.binomial(N-k,m-i)/mp.binomial(N,m) for i in range(m+1)]
    assert abs(mp.fsum(masses)-1)<mp.mpf('1e-75')
    mu=mp.mpf(m)*k/N
    def psi(t):
        return mp.log(mp.fsum(masses[i]*mp.exp(t*(i-mu)) for i in range(m+1)))
    def dp(t):
        weights=[masses[i]*mp.exp(t*(i-mu)) for i in range(m+1)]
        return mp.fsum((i-mu)*weights[i] for i in range(m+1))/mp.fsum(weights)
    # Divide out the removable third-order zero of the stationarity numerator.
    def stationary(t):
        return (t*dp(t)-2*psi(t))/t**3
    tilt=mp.findroot(stationary,(guess*mp.mpf('.8'),guess*mp.mpf('1.2')),tol=mp.mpf('1e-65'))
    R=4*N*(2*psi(tilt)/tilt**2)/(m*(N-m))
    return tilt,R

for m,s in [(1,1),(2,1),(3,1),(5,3)]:
    for N in [101,501,1001,2001]:
        e=mp.mpf(1)/N
        tilt,R=proxy_from_masses(N,m,mp.mpf(N-s)/2,4*s*e)
        tilt3=4*s*e+4*s*(m-1)*e**2+4*s*(6*m+s*s-6)*e**3/3
        R4=1+e+(1-mp.mpf(s*s)/3)*e**2+(1-mp.mpf((2*m-1)*s*s)/3)*e**3+(1-mp.mpf((4*m*m-2*m-1)*s*s)/3-mp.mpf(4*s**4)/45)*e**4
        print('ASYM',m,s,N,'N^4 tilt residual',mp.nstr((tilt-tilt3)*N**4,12),'N^5 proxy residual',mp.nstr((R-R4)*N**5,12))

for N,m in [(5,2),(15,3),(51,20)]:
    D=N*N-N-3*m*(N-m)
    T=mp.mpf(4*(N-2*m)*(N-3)*(N-1))/((N-2)*D)
    A=mp.mpf(N)/(3*(N-1))+mp.mpf(2*N*N*(N-4)*(m-1)*(N-m-1))/(3*(N-2)**2*(N-1)*D)
    d=mp.mpf('1e-5')
    tilt,R=proxy_from_masses(N,m,N*(1-d)/2,T*d)
    measured=(mp.mpf(N)/(N-1)-R)/(d*d)
    assert abs(measured-A)<mp.mpf('1e-6')
    print('FINITE IMBALANCE',N,m,'exact A',mp.nstr(A,15),'PMF A',mp.nstr(measured,15))
print('PASS: high-precision finite-population coefficient evaluations.')
