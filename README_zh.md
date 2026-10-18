# 超几何集中不等式：精确常数、有限样本极值与分段 KL 界

**Zinan Wang — The University of Manchester（曼彻斯特大学）**  
**Xinhao Yang — University of Southern California（南加州大学）**

本仓库在 `main` 统一维护 Main+A+B 数学成果。正式英文论文共 37 页、参考文献 20 条，包含有限交换序列的精确 Hoeffding 常数、全参数固定样本超几何极值定理，以及标准定义域内完整的分段 KL 上下尾界。

## 正式论文

**[完整论文 PDF](submission/current/manuscript.pdf)** · [LaTeX 源码](submission/current/manuscript.tex) · [arXiv 上传包](submission/current/arxiv-source.zip) · [干净投稿包](submission/current/clean-submission.zip) · [完整复现包](submission/current/complete-reproducibility.zip)

当前 `main` 包含 **357 个 Lean 文件**，其中 334 个为数学工程文件、23 个为公理审计/历史文件。完整复现包同时收录对应表、数值检验程序及固定依赖。Lean 4 的主要复现命令为：

```bash
lake exe cache get
lake build ExactHoeffding
```

统一投稿稿位于 [`submission/current/`](submission/current/)，早期论文与研究记录按原始目录保存。

[英文仓库首页](README.md) · [投稿说明](submission/README.md) · [形式化证明范围](LEAN_PROOF_STATUS.md)


完整定理—Lean 对应表：`submission/current/theorem_lean_concordance.md`。
