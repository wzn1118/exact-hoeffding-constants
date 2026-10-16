# A1：奇数总体 Bernoulli 包络的 KL/Chernoff 推导

设 `H ~ Hyp(N,k,m)`，并处于论文包络的参数域

`N >= 7, 3 <= m <= k <= floor(N/2), N > 2m`。

记

`p = k/N`, `q = 1-p`, `M = m(N-m)/(N-1)`, `a = (N-2m)/(N-2)`，

以及 `Y = H-mp`、`psi(t)=log E exp(tY)`。在该参数域内 `0 < p <= 1/2`、`0<a<1`，论文证明

`psi(t) <= U(t) := (M/a^2)[log(q+p exp(a t))-p a t]`。

## 上尾

对 `x >= 0` 和 `t >= 0`，Markov 不等式与包络给出

`P(Y >= x) <= exp(-t x + U(t))`。

令 `r = a x/M`、`theta = p+r`。若 `theta in [p,1]`，令 `s=a t`，则

`-t x + U(t) = (M/a^2)[log(q+p exp(s))-theta s]`。

函数右侧在 `s >= 0` 上的驻点满足

`p exp(s)/(q+p exp(s)) = theta`，

因此

`exp(s*) = theta q/[p(1-theta)]`,

`t* = (1/a) log[theta(1-p)/(p(1-theta))]`。

代回得到

`P(Y >= x) <= exp(-(M/a^2) D(theta || p))`,

其中

`D(theta || p) = theta log(theta/p) + (1-theta)log((1-theta)/(1-p))`。

当 `theta=p` 时 `t*=0`、指数为零，结论退化为 `P(Y>=0)<=1`。当 `theta=1` 时取 `t -> +infinity`，得到端点值 `exp(-(M/a^2) log(1/p))`；这里不把 `log(0)` 当作有限实数使用，而是按极限解释。

`theta` 只需在事件可能非空的范围内使用。由于 `H <= m`，有

`Y <= m(1-p)`。

若 `x > m(1-p)`，上尾事件为空，概率为零；不再构造 `theta`。若 `0 <= x <= m(1-p)`，则 `theta <= 1`，因为

`a m(1-p) / M = a(N-1)(1-p)/(N-m) < 1-p`。

所以所有非零上尾事件都落在合法的 `theta in [p,1]` 内。

## 下尾

对 `t <= 0` 或等价地对 `s=-a t >=0` 处理 `-Y`。令

`r = a x/M`, `theta_- = p-r`。

若 `theta_- in [0,p]`，同样的 Legendre 优化给出

`P(Y <= -x) <= exp(-(M/a^2)D(theta_- || p))`。

有限驻点为

`t* = (1/a) log[theta_-(1-p)/(p(1-theta_-))] <= 0`。

当 `theta_-=0` 时按 `t -> -infinity` 的极限解释。若 `x>mp`，由 `H>=0` 可知下尾事件为空；若 `0<=x<=mp`，则 `theta_->=0`，因为

`a m p/M = a(N-1)p/(N-m) < p`。

因此所有非零下尾事件均对应合法 `theta_- in [0,p]`。

## 双侧事件和阈值

对 `x>0`，由并集界

`P(|Y| >= x) <= P(Y>=x)+P(Y<=-x)`。

上下两项分别只在对应的真实支持非空时保留；超出支持的一项直接记为零。非整数 `x` 不需要取整，因为事件由 `H` 的整数支持自动决定，Chernoff 推导对任意实数阈值成立。

## 与二次界的局部比较

当 `x downarrow 0` 时，

`D(p+r || p) = r^2/[2p(1-p)] + O(r^3)`，

故 KL 指数为

`x^2/[2M p(1-p)] + O(x^3)`。

在本参数域，sharp curvature 给出的统一二次 MGF 系数为 `M/4`，其 Chernoff 指数为 `2x^2/M`。因此当 `p<1/2` 时，KL 包络在零点附近严格改善统一二次界；`p=1/2` 时二者二阶项相同，严格差异必须从高阶项或非零阈值比较。

以上结论只使用已证明的 Laplace 包络和真实支持，不把数值扫描当作解析证明，也不声称对包络参数域外成立。
