#!/usr/bin/env python3
"""Symbolic certificates and a frozen high-precision hypergeometric tail matrix."""

import csv
import hashlib
import json
from fractions import Fraction
from math import comb, ceil
from pathlib import Path

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / 'research/tail_bounds/benchmark_cases.json'


def symbolic_checks():
    N, m, k, u = sp.symbols('N m k u')
    p, M, a = k/N, m*(N-m)/(N-1), (N-2*m)/(N-2)
    mu, d = m*p, 1-2*p
    P = M*p*(1-p)+a*d*(u-mu)-a*a*(u-mu)**2/M
    B = u*(m-u)/m
    theta = p+a*(u-mu)/M
    c, h, b = 1/m-a*a/M, (1-a)*d, (m-M)*p*(1-p)
    assert sp.factor(P-M*theta*(1-theta)) == 0
    assert sp.factor(P-B-(c*(u-mu)**2-h*(u-mu)-b)) == 0
    assert sp.factor(c-(m-1)*(3*N*N-4*N-4*m*(N-1))/(m*(N-m)*(N-2)**2)) == 0
    assert sp.factor(1-a*m/M-N*(m-1)/((N-2)*(N-m))) == 0
    L, R = k-m, N-k-m
    assert sp.factor(u*(k-u)/k-B-L*u*u/(m*k)) == 0
    assert sp.factor((m-u)*(N-k-m+u)/(N-k)-B-R*(m-u)**2/(m*(N-k))) == 0
    assert sp.factor((k-u)*(N-m-k+u)/(N-m)-B-(L*u*u+R*(m-u)**2+m*L*R)/(m*(N-m))) == 0
    # The local KL expansion has opposite third-order signs on the two tails.
    z, p0 = sp.symbols('z p0', positive=True)
    D = z*sp.log(z/p0)+(1-z)*sp.log((1-z)/(1-p0))
    assert sp.simplify(sp.diff(D,z,2)-1/(z*(1-z))) == 0
    assert sp.simplify(sp.diff(D,z,3).subs(z,p0)+(1-2*p0)/(p0*p0*(1-p0)**2)) == 0
    print('PASS: variance-switch, support, KL curvature and four symmetry identities')


def binary_kl(z, p):
    assert 0 <= z <= 1 and 0 < p < 1
    return (z*mp.log(z/p) if z else 0)+((1-z)*mp.log((1-z)/(1-p)) if z != 1 else 0)


def fraction_mp(v):
    return mp.mpf(v.numerator)/v.denominator


class Law:
    def __init__(self, N, k, m):
        self.N, self.k, self.m = N, k, m
        self.p = mp.mpf(k)/N
        self.mu = self.p*m
        self.M = mp.mpf(m*(N-m))/(N-1)
        self.a = mp.mpf(N-2*m)/(N-2)
        self.den = comb(N,m)
        self.nums = [comb(k,i)*comb(N-k,m-i) for i in range(m+1)]
        assert sum(self.nums) == self.den
        self.weights = [mp.mpf(n)/self.den for n in self.nums]
        self.logs = [mp.log(w) for w in self.weights]
        c = 1/mp.mpf(m)-self.a**2/self.M
        h = (1-self.a)*(1-2*self.p)
        b = (m-self.M)*self.p*(1-self.p)
        discriminant = mp.sqrt(h*h+4*c*b)
        self.rlo = self.mu+(h-discriminant)/(2*c)
        self.rhi = self.mu+(h+discriminant)/(2*c)
        assert 0 < self.rlo < self.mu < self.rhi < m

    def IP(self,v):
        return self.M/self.a**2*binary_kl(self.p+self.a*(v-self.mu)/self.M,self.p)

    def IB(self,v):
        return self.m*binary_kl(v/self.m,self.p)

    def dp(self,v):
        z = self.p+self.a*(v-self.mu)/self.M
        return mp.log(z*(1-self.p)/(self.p*(1-z)))/self.a

    def db(self,v):
        return mp.log(v*(1-self.p)/(self.p*(self.m-v)))

    def J(self,v):
        if self.rlo <= v <= self.rhi:
            return self.IP(v)
        r = self.rlo if v < self.rlo else self.rhi
        return self.IB(v)+self.IP(r)-self.IB(r)+(v-r)*(self.dp(r)-self.db(r))

    def tilt(self,t):
        z = [l+t*i for i,l in enumerate(self.logs)]
        shift = max(z)
        w = [mp.exp(x-shift) for x in z]
        total = mp.fsum(w)
        mean = mp.fsum(i*x for i,x in enumerate(w))/total
        return shift+mp.log(total), mean

    def exact_rate(self,v):
        if v == 0:
            return -self.logs[0]
        if v == self.m:
            return -self.logs[-1]
        if v == self.mu:
            return mp.mpf(0)
        left, right = mp.mpf(-1), mp.mpf(1)
        while self.tilt(left)[1] > v:
            left *= 2
        while self.tilt(right)[1] < v:
            right *= 2
        for _ in range(150):
            mid = (left+right)/2
            if self.tilt(mid)[1] < v:
                left = mid
            else:
                right = mid
        t = (left+right)/2
        return t*v-self.tilt(t)[0]

    def four_rates(self,v):
        N,k,m,p = self.N,self.k,self.m,self.p
        return [self.IB(v), k*binary_kl(v/k,mp.mpf(m)/N),
                (N-m)*binary_kl((k-v)/(N-m),p),
                (N-k)*binary_kl((m-v)/(N-k),mp.mpf(m)/N)]

    def factorial(self,threshold,side):
        k = self.k if side == 'upper' else self.N-self.k
        d = threshold if side == 'upper' else self.m-threshold
        assert 1 <= d <= min(k,self.m)
        current, candidates = Fraction(1), [Fraction(1)]
        for j in range(d):
            current *= Fraction((k-j)*(self.m-j),(self.N-j)*(d-j))
            candidates.append(current)
        r = Fraction(self.N*d-k*self.m,self.N+d-k-self.m)
        index = ceil(r)
        assert 1 <= index <= d
        assert candidates[index] == min(candidates)
        return candidates[index]


def display(v):
    return mp.nstr(v,42)


def main():
    config = json.loads(CONFIG.read_text())
    mp.mp.dps = config['precision_decimal_digits']
    symbolic_checks()
    rows = []
    counterexamples = []
    for N,k,m in config['cases']:
        assert N >= 7 and 3 <= m <= k <= N//2 and N > 2*m
        law = Law(N,k,m)
        values = sorted(set([mp.mpf(i) for i in range(m+1)]+[
            law.rlo, law.rhi, law.mu, law.rlo/2, (law.rhi+m)/2,
            (law.rlo+law.mu)/2, (law.rhi+law.mu)/2]))
        for v in values:
            if v == law.mu:
                assert abs(law.IP(v))+abs(law.J(v))+abs(law.IB(v)) < mp.mpf('1e-60')
                continue
            side = 'upper' if v > law.mu else 'lower'
            threshold = int(mp.ceil(v)) if side == 'upper' else int(mp.floor(v))
            nums = law.nums[threshold:] if side == 'upper' else law.nums[:threshold+1]
            exact = Fraction(sum(nums),law.den)
            ip,ib,j,irate = law.IP(v),law.IB(v),law.J(v),law.exact_rate(v)
            r4 = max(law.four_rates(v))
            kappa = mp.mpf(1) if N%2 == 0 else 1/(N*mp.atanh(mp.mpf(1)/N))
            uniform_rate = 2*(v-law.mu)**2/(law.M*kappa)
            tol = mp.mpf('1e-38')
            assert irate > j and j > ib
            assert j+tol >= ip >= uniform_rate-tol
            assert abs(r4-ib) < tol
            if v < law.rlo or v > law.rhi:
                assert j > max(ip,ib)
            else:
                assert abs(j-ip) < tol
            exact_log = mp.log(fraction_mp(exact))
            assert exact_log <= -irate+tol
            factorial = law.factorial(threshold,side)
            lattice_rate = law.exact_rate(mp.mpf(threshold))
            assert mp.log(fraction_mp(factorial)) <= -lattice_rate+tol
            assert exact <= factorial
            if ip < ib:
                counterexamples.append([N,k,m,display(v),display(ip),display(ib)])
            x = v-law.mu
            variance = law.M*law.p*(1-law.p)
            abs_x = abs(x)
            z = abs_x/variance
            bennett = variance*((1+z)*mp.log1p(z)-z)
            bernstein = abs_x**2/(2*(variance+abs_x/3))
            assert ip > bennett >= bernstein-tol
            rows.append({
                'N':N,'k':k,'m':m,'side':side,'v':display(v),'lattice_threshold':threshold,
                'exact_tail_fraction':str(exact),'exact_log_tail':display(exact_log),
                'exact_chernoff_log_diagnostic':display(-irate),
                'scaled_kl_log_bound':display(-ip),'piecewise_kl_log_bound':display(-j),
                'four_binomial_kl_best_log_bound':display(-r4),
                'uniform_optimal_quadratic_log_bound':display(-uniform_rate),
                'hoeffding_log_bound':display(-2*x*x/m),
                'serfling_log_bound':display(-2*N*x*x/(m*(N-m+1))),
                'exact_variance_bennett_log_bound':display(-bennett),
                'exact_variance_bernstein_log_bound':display(-bernstein),
                'optimized_factorial_fraction':str(factorial),
                'optimized_factorial_log_bound':display(mp.log(fraction_mp(factorial))),
                'r_minus':display(law.rlo),'r_plus':display(law.rhi),
                'interpretation':'finite high-precision check, not a kernel proof'})
        # Independent integral reconstruction at each support endpoint.
        def P(u):
            return law.M*law.p*(1-law.p)+law.a*(1-2*law.p)*(u-law.mu)-law.a**2*(u-law.mu)**2/law.M
        # The singular endpoint kernels simplify to m/(m-u) and m/u.
        low_integral = mp.quad(lambda u: law.m/(law.m-u),[0,law.rlo])+mp.quad(lambda u: u/P(u),[law.rlo,law.mu])
        high_integral = mp.quad(lambda u: (law.m-u)/P(u),[law.mu,law.rhi])+mp.quad(lambda u: law.m/u,[law.rhi,law.m])
        assert abs(low_integral-law.J(mp.mpf(0))) < mp.mpf('1e-45')
        assert abs(high_integral-law.J(mp.mpf(m))) < mp.mpf('1e-45')
    assert counterexamples
    out = ROOT/'checks/results'
    out.mkdir(parents=True,exist_ok=True)
    with (out/'piecewise_kl_matrix.csv').open('w',newline='') as f:
        writer = csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summary = {'matrix_sha256':hashlib.sha256(CONFIG.read_bytes()).hexdigest(),
               'rows':len(rows),'cases':len(config['cases']),'precision':mp.mp.dps,
               'outside_envelope_cases_not_evaluated':config['outside_envelope_cases'],
               'scaled_kl_weaker_than_binomial_rows':len(counterexamples),
               'representative_counterexamples':counterexamples[:5],
               'assertions':'exact_tail <= factorial <= exact_Chernoff < piecewise_KL; piecewise_KL strictly improves four binomial KL; dominates uniform quadratic',
               'proof_level':'symbolic identities and finite numerical verification; analytic proof is in minimum_variance_tail.tex'}
    (out/'piecewise_kl_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(f'PASS: {len(rows)} frozen parameter/threshold checks at {mp.mp.dps} digits')
    print('PASS: exact integer tails and optimized factorial moments with valid endpoint order')
    print('PASS: both improper endpoint integrals match the piecewise closed form')
    print('PASS: all four symmetry KL rates and uniform quadratic comparisons')
    print('PASS: strict comparison with exact-variance Bennett and Bernstein bounds')
    print(f'PASS: {len(counterexamples)} scaled-only losses to binomial KL corrected by the piecewise rate')


if __name__ == '__main__':
    main()
