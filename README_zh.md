# 有限交换序列的精确 Hoeffding 常数

**Zinan Wang · 2026 年 10 月 11 日修订**

[主论文 PDF（28 页）](manuscript.pdf) · [技术补充 PDF（6 页）](supplementary_refinements.pdf) · [单文件投稿源码](submission/manuscript.tex)

## 精确常数

对任意有限总体规模，有界交换序列的中心化线性对比满足最优 Hoeffding 系数公式
\[
C_N^\star=\begin{cases}
N/(N-1),&N\text{ 为偶数},\\
[(N-1)\operatorname{artanh}(1/N)]^{-1},&N\text{ 为奇数}.
\end{cases}
\]

主论文集中呈现两水平归约、全参数倾斜方差界、奇偶统一的 Laplace 包络、精确常数和奇数总体的等号分类。四阶展开收至附录。固定样本成功数极值与精确失衡系数、紧成功比例区间解析收缩、次要曲率例子与积分恒等式收至独立的技术补充，保留完整论证。

## 可复现性

CI 已改为实际执行全部 `run_all.sh` 数学测试，而非仅编译 PDF。包括偶数总体包络在内的十一项检查均须通过；运行日志保存到 `checks/logs/`，包含 `verify_even_envelope_extension.log`。同时验证 27–30 页主稿要求、补充文稿、文献引用和 SHA256 文件哈希。

```bash
python3 -m pip install -r requirements.txt
python3 checks/sync_submission.py
bash run_all.sh
python3 checks/refresh_checksums.py
sha256sum -c SHA256SUMS.txt
```

论文和补充材料从 `source/manuscript.tex` 与 `source/supplement.tex` 编译。版权归作者所有，详见 `LICENSE`、`COPYRIGHT.md` 和 `THIRD_PARTY_NOTICES.md`。
