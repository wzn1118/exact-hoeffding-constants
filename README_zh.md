# 有限交换序列的精确 Hoeffding 常数

**Exact Hoeffding Constants for Finite Exchangeable Sequences**  
作者：Zinan Wang · 修订日期：2026-10-11

版权归作者所有，详见 `LICENSE` 和 `COPYRIGHT.md`。第三方文献的许可见 `THIRD_PARTY_NOTICES.md`。

[最新英文论文 PDF](manuscript.pdf) · [独立投稿 LaTeX 源码](submission/manuscript.tex) · [参考文献目录](refs/README_zh.md)

## 主定理

对任意有限总体规模，最优 Hoeffding 常数为

\[
C_N^\star=
\begin{cases}
N/(N-1),&N\text{ 为偶数},\\
[(N-1)\operatorname{artanh}(1/N)]^{-1},&N\text{ 为奇数}.
\end{cases}
\]

偶数情形由最大归一化方差确定，奇数情形的最优值在明确的非零 Laplace 倾斜处取得。本次修订将两水平归约提前，统一升阶乘与降阶乘的记号，并将核心 Bernoulli Laplace 包络比较推广至适当参数范围内的偶数总体；同时保留奇数情形的极值分类及四阶展开。

## 正式版本

- `manuscript.pdf`：当前 33 页论文 PDF，由 LaTeX 源码自动构建。
- `source/`：完整分模块证明与主稿。
- `submission/manuscript.tex`：自包含单文件投稿源码。
- `checks/`：证明校验与生成脚本。
- `refs/`：参考文献记录与获得授权的文献副本。
- `SHA256SUMS.txt`：文件校验清单。

旧版投稿 ZIP 已从最新树中清理。Git 历史仍保留历次提交，方便追踪论文的数学修订。

## 构建

```bash
python3 -m pip install -r requirements.txt
python3 checks/sync_submission.py
bash build_manuscript.sh
bash run_all.sh
python3 checks/refresh_checksums.py
sha256sum -c SHA256SUMS.txt
```

正式稿通过 [GitHub Actions](.github/workflows/publish-manuscript.yml) 自动构建和同步 PDF。
