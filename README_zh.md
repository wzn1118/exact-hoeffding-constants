# 有限交换序列的精确 Hoeffding 常数

**Zinan Wang · 2026 年 10 月 11 日修订**

[英文主论文（28 页）](manuscript.pdf) · [技术补充（6 页）](supplementary_refinements.pdf) · [独立投稿 LaTeX 源码](submission/manuscript.tex)

## 主定理

对任意有限总体规模，中心化有界交换序列的最优 Hoeffding 系数为

\[
C_N^\star = \begin{cases}
\dfrac{N}{N-1}, & N\text{ 为偶数},\\[4pt]
\dfrac{1}{(N-1)\operatorname{artanh}(1/N)}, & N\text{ 为奇数}.
\end{cases}
\]

主论文集中论述 Lee–Kim 两水平归约、全参数倾斜方差界、奇偶统一的 Laplace 包络、精确常数和奇数总体的等号分类。四阶渐近展开进入附录。固定样本成功数极值、紧成功率区间上的解析收缩以及次要曲率反例与积分恒等式移入独立技术补充，保留完整证明。

## 完整复现

连续集成现在执行全部 `run_all.sh` 数学测试，涵盖偶数总体包络检查，并保存 `checks/logs/verify_even_envelope_extension.log` 等逐项日志。自动构建同时生成 28 页主论文和 6 页补充论文，检查校验和后将产物同步到 `main`。

```bash
python3 -m pip install -r requirements.txt
python3 checks/sync_submission.py
bash run_all.sh
python3 checks/refresh_checksums.py
sha256sum -c SHA256SUMS.txt
```

主论文、补充论文和单文件投稿源码分别位于 `manuscript.pdf`、`supplementary_refinements.pdf` 与 `submission/manuscript.tex`。源码入口为 `source/manuscript.tex` 和 `source/supplement.tex`。

版权所有 © 2026 Zinan Wang。原创文字、源码及验证脚本保留全部权利，详见 `LICENSE`、`COPYRIGHT.md` 和第三方文献声明 `THIRD_PARTY_NOTICES.md`。

## 证明核验与文献对照

- [全局曲率与 Laplace 包络的证明证书](docs/proof_certification_2026-10-11.md)
- [逐定理文献与原创性对照](docs/theorem_priority_2026-10-11.md)
- 独立代数核验：`python3 checks/verify_independent_certificates.py`；日志：`checks/logs/verify_independent_certificates.log`。
