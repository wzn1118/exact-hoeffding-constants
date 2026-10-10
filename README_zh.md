# 有限交换序列的精确 Hoeffding 常数

**Exact Hoeffding Constants for Finite Exchangeable Sequences**  
作者：Zinan Wang　日期：2026-10-10

**Copyright (c) 2026 Zinan Wang. All rights reserved.**

原创论文、作者编写的 LaTeX 源码、说明文档和验证代码保留作者所有权及全部版权；本仓库没有为这些原创材料授予开源或 Creative Commons 许可。具体条款见 `LICENSE` 和 `COPYRIGHT.md`。公开访问不转让作者所有权，GitHub 平台条款及法律规定的权利继续适用。

第三方文献全文保留原作者权利，分别按 CC BY 4.0 提供；见 `THIRD_PARTY_NOTICES.md`。上述版权声明不覆盖第三方文献，也不改变正文对已有结果和方法的归属。

## 论文

`manuscript.pdf` 为完整英文主稿。`source/manuscript.tex` 为 LaTeX 入口。

本文确定所有总体规模的精确常数：

\[
C_N^\star=\begin{cases}
N/(N-1),&N\text{ 为偶数},\\
[(N-1)\operatorname{artanh}(1/N)]^{-1},&N\text{ 为奇数}.
\end{cases}
\]

偶数总体的最佳指数常数等于最大归一化方差；奇数总体则严格超过方差常数，并在明确的非零倾斜处取得等号。正文包括全参数曲率证明、奇数统一包络、完整的 Lee–Kim two-level 归约证明、超几何等号分类、四阶最优代理展开及固定样本规模的成功数极值定理。

## 文件

- `source/`：主稿、证明章节与文后书目。
- `docs/`：中文证明、数学结果及文献关系、阅读索引。
- `refs/`：16 项文献的 BibTeX、JSON、来源目录与四篇 CC BY 4.0 全文。
- `checks/`：十项数学计算脚本和文档一致性检查。
- `checks/logs/`：数学计算及编译记录。
- `build_manuscript.sh`：编译论文。
- `run_all.sh`：执行全部数学计算并编译。
- `SHA256SUMS.txt`：文件校验表。
- `submission/`：自包含的单文件 LaTeX 源码及源码 ZIP。
- `LICENSE`、`COPYRIGHT.md`：作者权利声明。
- `THIRD_PARTY_NOTICES.md`：第三方全文的作者、版本与许可。
- `CITATION.cff`：引用信息。

## 文献版本

三点代理公式归引 Atouani–Marchal–Arbel (2025), Theorem 3.2 和 Corollary 3.3。其在本稿中的应用是两次抽样的超几何专门化与极值计算。

Gottschling–Caprio 的条目统一为 *Hoeffding-Style Concentration Bounds for Exchangeable Random Variables*，arXiv:2603.10190v2（2026-06-24），书目、链接与所附 PDF 对应同一版本。

## 使用

环境：Python 3.10+、SymPy、mpmath，以及包含文稿宏包的 pdfLaTeX。

```bash
python3 -m pip install -r requirements.txt
bash run_all.sh
```

仅编译主稿：

```bash
bash build_manuscript.sh
```

生成的中间文件位于 `build/`，最终 PDF 位于根目录。文件校验：

```bash
sha256sum -c SHA256SUMS.txt
```
