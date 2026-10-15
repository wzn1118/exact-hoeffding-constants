# 有限交换序列的精确 Hoeffding 常数

**Zinan Wang · 2026 年 10 月 15 日修订**

[英文主论文（28 页）](manuscript.pdf) · [技术补充（6 页）](supplementary_refinements.pdf) · [完整论文与 arXiv 投稿包](submission/README.md)

## 主定理

对任意有限总体规模，中心化有界交换序列的最优 Hoeffding 系数为

\[
C_N^\star = \begin{cases}
\dfrac{N}{N-1}, & N\text{ 为偶数},\\[4pt]
\dfrac{1}{(N-1)\operatorname{artanh}(1/N)}, & N\text{ 为奇数}.
\end{cases}
\]

主论文集中论述 Lee–Kim 两水平归约、全参数倾斜方差界、奇偶统一的 Laplace 包络、精确常数和奇数总体的等号分类。四阶渐近展开进入附录。固定样本成功数极值、紧成功率区间上的解析收缩以及次要曲率反例与积分恒等式移入独立技术补充，保留完整证明。

## arXiv 投稿文件

[投稿说明](submission/README.md)列出单入口源码包、合并全文及独立参考文献包。`submission/combined_all.tex` 合并主稿与全部技术补充，共用一份参考文献。运行以下命令可重新打包，并在空目录中解压、编译投稿源码：

```bash
python3 checks/package_submission.py
```

投稿包与文献包的文件清单、校验和及编译报告随包保存。全文与技术补充的 30 项命名结果均有完整 Lean 对应；总构建与公理审计通过 252 个项目模块中的 1518 条公开定理。逐项映射见 `formal_status/manuscript_concordance.md`，审计日志见 `checks/logs/full_closure/final_all_manuscript_umbrella_audit.log`。

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
