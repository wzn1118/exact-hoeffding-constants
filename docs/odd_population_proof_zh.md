# 奇数总体的统一 Bernoulli 包络与精确常数

## 结论

对所有奇数 \(N\ge3\)，
\[
\boxed{\max_{1\le k,m<N}\frac{4N}{m(N-m)}
\sigma^2_{\mathrm{opt}}(H_{N,k,m})
=\frac1{(N-1)\operatorname{artanh}(1/N)}.}
\]
等号恰在
\[
m\in\{1,N-1\},\qquad k\in\{(N-1)/2,(N+1)/2\}
\]
取得。结合 Lee–Kim [LeeKim] 的变分归约，即得到相同的 \(C_N^\star\) 闭式。

下面的论证对每个有限 \(N,m,k\) 成立，不使用固定 \(m\) 的极限或依赖 \(m\) 的阈值。

## 1. 更强的统一 Laplace 比较

先考虑
\[
N\ge7\text{ 为奇数},\qquad 3\le m\le k\le\frac{N-1}{2}.
\]
记
\[
p=\frac{k}{N},\ q=1-p,\ d=1-2p,\quad
M=\frac{m(N-m)}{N-1},\quad a=\frac{N-2m}{N-2}>0.
\]
我们证明所有实数 \(t\) 都满足
\[
\boxed{\log\mathbb E e^{t(H-mp)}
\le\frac{M}{a^2}\{\log(q+pe^{at})-pat\},} \tag{1}
\]
且 \(t\ne0\) 时严格。

变量代换 \(s=at\) 后，这将给出
\[
\sigma^2_{\mathrm{opt}}(H)
<M\sigma^2_{\mathrm{opt}}(\mathrm{Bern}(p)). \tag{2}
\]

## 2. 把倾斜方差视为倾斜均值的函数

设 \(u(t)=\mathbb E_tH\)、\(v(t)=\operatorname{Var}_t(H)\)。支持 \(\{0,\ldots,m\}\) 上所有质量严格为正，故
\[
u'(t)=v(t)>0,
\]
且 \(u(t)\) 将实轴一一映满 \((0,m)\)。所以可写 \(v(t)=V(u(t))\)。在两端 \(V(0)=V(m)=0\) 按连续延拓解释。令 \(\mu=mp\)，则
\[
V(\mu)=Mpq.
\]

### 2.1 实根可行性约束

概率生成多项式正比于
\[
(1-z)^mP_m^{(N-k-m,k-m)}\left(\frac{1+z}{1-z}\right).
\]
两个 Jacobi 参数非负，正交性使其全部零点位于 \((-1,1)\)，从而生成多项式全部零点为负实数。每个倾斜后的分布因此都是 \(m\) 个独立 Bernoulli 变量之和。若相应参数为 \(p_i\)，则
\[
u=\sum_i p_i,\quad V=\sum_i p_i(1-p_i)
\le u-\frac{u^2}{m}.
\]
因此
\[
\boxed{V(u)\le\frac{u(m-u)}m.} \tag{3}
\]

### 2.2 精确微分恒等式

定义
\[
A(u)=u(u+N-k-m),\qquad C(u)=(k-u)(m-u),
\]
\[
F(u,v)=-(N-1)v^2+[A+C-A'C+C'A]v+AC.
\]
相邻质量递推给出
\[
e^t=\frac{A(u)+V(u)}{C(u)+V(u)}.
\]
对 \(u\) 求对数导数，利用 \(dt/du=1/V\)，得到
\[
\frac{A'+V'}{A+V}-\frac{C'+V'}{C+V}=\frac1V.
\]
由于 \(C-A=-N(u-\mu)\)，整理为
\[
\boxed{F(u,V)+N(u-\mu)VV'=0.} \tag{4}
\]
恒等式 (4) 在中心 \(u=\mu\) 处同样成立。

## 3. 二次方差包络及全参数正性证书

定义
\[
P(u)=Mpq+ad(u-\mu)-\frac{a^2}{M}(u-\mu)^2. \tag{5}
\]
下面证明 \(V(u)\le P(u)\)，且仅在 \(u=\mu\) 等号。

记
\[
y=u-\mu,\qquad z=\frac{2y}{M},\qquad
G=\frac{N^2(m-1)(N-m-1)}{4(N-2)^2(N-1)}>0,
\]
并设
\[
W(d,z)=N-4+3Nd^2-4Nadz+[(N+1)a^2-M]z^2.
\]
代入 (4) 的左边，有精确恒等式
\[
\boxed{F(u,P)+NyPP'=-Gy^2W(d,z).} \tag{6}
\]

以下在可能接触 \(V=P\) 的可行域证明 \(W>0\)。

令
\[
\delta=\frac{N-2m}{N},\qquad b=\frac{N-m}{N-2},
\]
\[
c=\frac{(N-m)[3N^2-4N-4m(N-1)]}{(N-1)(N-2)^2},
\quad E(d,z)=1-d^2+4bdz-cz^2.
\]
直接化简有
\[
\frac{u(m-u)}m-P(u)=\frac{m(m-1)}{4(N-1)}E(d,z). \tag{7}
\]
所以任一接触点 \(V=P\) 都由 (3) 满足 \(E\ge0\)。参数范围还给出 \(0<d\le\delta\)。

现在定义
\[
\lambda=\frac{m^2-mN+3m+N^2-4N}{2(N-m)},\quad
\alpha=\frac{N-4-\lambda}{\delta^2},
\]
\[
A_0=3N+\lambda+\alpha,\quad
B_0=-2Na-2\lambda b,\quad
C_0=(N+1)a^2-M+\lambda c.
\]
我们使用如下精确证书：
\[
\boxed{W=\lambda E+\alpha(\delta^2-d^2)
+A_0d^2+2B_0dz+C_0z^2.} \tag{8}
\]
其行列式为
\[
A_0C_0-B_0^2
=\frac{N^2U_0V_0}{(N-2m)^2(N-2)^2(N-1)}, \tag{9}
\]
其中
\[
U_0=N^2-2N-m^2-mN+3m,
\]
\[
V_0=m^3-6m^2-2mN^2+14mN-3m+N^3-7N^2+6N.
\]

令 \(j=m-3\ge0\)、\(r=N-2m\ge1\)，则
\[
\begin{aligned}
2(N-m)\lambda
&=3j^2+3jr+13j+r^2+5r+12>0,\\
2(N-m)(N-4-\lambda)
&=j^2+3jr+3j+r^2+5r>0,\\
U_0&=j^2+3jr+5j+r^2+7r+6>0,\\
V_0&=j^3+4j^2r+3j^2+4jr^2+10jr+r^3+5r^2>0.
\end{aligned} \tag{10}
\]
于是 \(\lambda,\alpha>0\)，\(A_0>0\)，且 (9) 严格为正。因此 (8) 的最后二次型正定。在 \(E\ge0\)、\(0<d\le\delta\) 下，前两项非负，且向量 \((d,z)\ne0\)，故
\[
\boxed{W(d,z)>0.} \tag{11}
\]
以上恒等式给出全参数正性。

## 4. 过零方向排除任何全局越界

首先两个支持端点满足
\[
P(0)=\frac{km(m-1)[(N-m)(N-2)-k(m-1)]}
{(N-m)(N-2)^2(N-1)}>0,
\]
\[
P(m)=\frac{m(N-k)(m-1)[k(m-1)+(N-2m)(N-1)]}
{(N-m)(N-2)^2(N-1)}>0.
\]
第一式的括号由 \(k\le N-m\) 至少为 \((N-m)(N-m-1)>0\)。第二式显然为正。

设 \(f(u)=V(u)-P(u)\)。于是
\[
f(0)<0,\quad f(m)<0,\quad f(\mu)=0.
\]
若 \(u\ne\mu\) 是 \(f\) 的零点，则 \(V=P>0\)。结合 (4)、(6)、(11)，
\[
\boxed{f'(u)=\frac{G(u-\mu)W(d,z)}{NP(u)}.} \tag{12}
\]
所以中心左侧的每个零点导数严格为负，右侧的每个零点导数严格为正。

- 若左侧出现 \(f>0\)，其某个正区间的左端点必须是导数非负的零点，与 (12) 矛盾。
- 若右侧出现 \(f>0\)，其某个正区间的右端点必须是导数非正的零点，也与 (12) 矛盾。

因此 \(f\le0\)。任一非中心零点还必须是局部极大值，导数应为零，再次矛盾。综上，
\[
\boxed{V(u)\le P(u),\quad\text{等号当且仅当 }u=\mu.} \tag{13}
\]
此式成立于整个区间 \((0,m)\)。

## 5. 正负倾斜都成立的积分比较

写 \(y(t)=u(t)-\mu\)，并令
\[
\mathcal P(y)=Mpq+ady-a^2y^2/M.
\]
(13) 给出 \(y'\le\mathcal P(y)\)，\(t\ne0\) 时严格。
初值问题 \(Y'=\mathcal P(Y),Y(0)=0\) 的显式解是
\[
Y(t)=\frac{M}{a}\left(\frac{pe^{at}}{q+pe^{at}}-p\right).
\]
令
\[
\Delta(t)=\mathcal P(y(t))-y'(t)>0\quad(t\ne0),
\quad h(t)=ad-\frac{a^2}{M}(y(t)+Y(t)).
\]
差值 \(e=y-Y\) 满足 \(e'=he-\Delta,e(0)=0\)，故
\[
e(t)=-\exp\left(\int_0^t h\right)
\int_0^t\exp\left(-\int_0^s h\right)\Delta(s)\,ds.
\]
从而
\[
y(t)<Y(t)\ (t>0),\qquad y(t)>Y(t)\ (t<0).
\]
由于 \(\psi'(t)=y(t)\)，分别按正确积分方向积分，所有 \(t\ne0\) 都有
\[
\psi(t)<\int_0^tY(s)\,ds
=\frac{M}{a^2}[\log(q+pe^{at})-pat].
\]
即得 (1)。

Bernoulli 精确代理为
\[
\sigma^2_{\mathrm{opt}}(\mathrm{Bern}(p))
=\frac{d}{4\operatorname{artanh}d}.
\]
因此 (1) 先给出非严格形式的 (2)。为得到严格性，注意真实代理目标在零处可连续延拓，在两端无穷远趋零，故最大值在有限点取得。非零最大点由 (1) 给出严格性；零点则由
\[
pq=\frac{1-d^2}{4}<\frac{d}{4\operatorname{artanh}d}
\]
给出严格性。最后一式来自
\(\operatorname{artanh}d<d/(1-d^2)\)。这证明了最优代理比较 (2) 的严格性。

函数 \(g(d)=d/\operatorname{artanh}d\) 严格递减，所以 \(d\ge1/N\) 推出
\[
\boxed{\frac{4N}{m(N-m)}\sigma^2_{\mathrm{opt}}(H)
<\frac{N}{N-1}g(d)
\le\frac1{(N-1)\operatorname{artanh}(1/N)}.} \tag{14}
\]

## 6. 单次、两次抽样以及所有有限边界

### 6.1 Bernoulli 公式的短证明

取 \(p<1/2\)，\(b=\frac12\log(q/p)>0\)，\(f(x)=\log\cosh x\)。因为 \(f'(x)/x=\tanh(x)/x\) 在正半轴严格递减，由积分和偶对称得到
\[
f(x)-f(b)\le\frac{f'(b)}{2b}(x^2-b^2)\quad(x\in\mathbb R).
\]
把 \(x=t/2-b\)、\(f'(b)=q-p\) 代入
\[
\log(q+pe^t)-pt=f(t/2-b)-f(b)+(q-p)t/2
\]
即得代理 \((q-p)/(4b)\)。在 \(t=4b\) 取得等号，故这是精确最优代理。

因此 \(m=1\) 的规范化代理为 \(Ng(d)/(N-1)\)，只在规范域的 \(k=(N-1)/2\) 取得 \(L_N\)。

### 6.2 两次抽样

设 \(m=2\)、\(2\le k\le(N-1)/2\)。记质量为 \(p_0,p_1,p_2\)，则
\[
p_0=\frac{(N-k)(N-k-1)}{N(N-1)},\quad
p_1=\frac{2k(N-k)}{N(N-1)},\quad
p_2=\frac{k(k-1)}{N(N-1)}.
\]
置 \(A=p_1\)、\(B=2\sqrt{p_0p_2}\)、\(b=\frac12\log(p_0/p_2)\)。有
\[
1\le A/B=\sqrt{\frac{k(N-k)}{(k-1)(N-k-1)}}\le2.
\]
对 \(f(x)=\log(A+B\cosh x)\)，
\[
f'''(x)=\frac{B\sinh x(A^2-AB\cosh x-2B^2)}{(A+B\cosh x)^3}\le0
\quad(x>0).
\]
所以 \(f'(x)/x\) 递减，由与 Bernoulli 相同的积分法得到最优代理
\[
\sigma^2_{\mathrm{opt}}(H)=\frac{2d}{\log(p_0/p_2)},
\]
其中等号倾斜为 \(t=\log(p_0/p_2)\)。
令
\[
A_1=2\operatorname{artanh}d,\quad
B_1=2\operatorname{artanh}\frac{Nd}{N-2}.
\]
则 \(\log(p_0/p_2)=A_1+B_1\)。由 \(\operatorname{artanh}x/x\) 严格递增，
\[
B_1>\frac N{N-2}A_1,
\]
因此
\[
\sigma^2_{\mathrm{opt}}(H)
<\frac{(N-2)d}{(N-1)A_1}
=\frac{2(N-2)}{N-1}\sigma^2_{\mathrm{opt}}(\mathrm{Bern}(p)).
\]
即两次抽样也满足同样的严格代理包络。

### 6.3 对称归约及等号

成功数补集或抽样数补集只会对中心化变量取负，代理不变，抽样数补集也保持分母 \(m(N-m)\) 不变。所以先归约到 \(k,m\le(N-1)/2\)。若 \(k<m\)，用转置对称时须保留分母因子：
\[
R_{N,k,m}
=\frac{k(N-k)}{m(N-m)}R_{N,m,k}<L_N.
\]
前面的因子严格小于 1，转置后的参数位于已证明的规范域。

规范域中 \(m\ge2\) 全部严格；\(m=1\) 只在 \(k=(N-1)/2\) 等号。恢复补集即得到开头陈述的全部等号情形。

\(N=3\) 的规范域只有 \(k=m=1\)；\(N=5\) 只涉及 \(m=1,2\)。因此所有有限边界也已解析覆盖。

## 7. 全参数结论

(14) 是每个有限 \(N,m,k\) 的统一不等式，既覆盖 \(m_N\to\infty\) 且 \(m_N=o(N)\)，也覆盖 \(m_N/N\) 不趋零的区域。比较式中的各个系数均为有限总体的精确表达式。

证明中的方差界 \(V(u)\le P(u)\) 随倾斜均值变化。主稿的精确曲率反例说明了该界与常数曲率界的区别。

结合 Lee–Kim [LeeKim] 的变分归约，最终为
\[
\boxed{C_N^\star=\frac{1}{(N-1)\operatorname{artanh}(1/N)}
=\frac{2}{(N-1)\log((N+1)/(N-1))}\quad(N\ge3\text{ 奇}).}
\]

计算文件：`checks/verify_odd_envelope.py` 给出自由符号恒等式核验；`checks/check_exact_odd_envelope.py` 与 `checks/check_high_precision_envelope.py` 分别给出精确有理和高精度计算。
