# 《Exact Minima of Finite Absolute Cosine Sums》文献与创新性核查

**结论：已确认重要的局部先例和证明思路先例；尚未找到先于目标论文的完整一般定理，但关键全文仍有缺口，不能把本报告解释为“已经确认原创”。**

本报告核查 Ruixi Sun 的 arXiv:2609.05545v1，检索截止日为 2026 年 9 月 9 日。目标是固定连续频率的逐点极小化

\[
S_n(x)=\sum_{k=1}^{n}|\cos(kx)|,\qquad M_n=\min_{x\in\mathbb R}S_n(x),
\]

以及所有达到极小值的点。核查基准为 v1 的 Theorem 1 与 Lemmas 1–5；这是一份文献与贡献边界审查，并不替代对整篇证明的独立审稿。[^0]

最影响投稿表述的发现有三项。第一，1980 年 Kvant 的 M590 解答已有二项极小值，并把四项锐不等式列为附加习题；后者在 \(x=\pi/6\) 取等号是直接代入所得。因此两个例外值都有更早的公开先例。第二，2022 年 HDD 292 的问题帖已包含主要约化框架，不能仅归功于“初始凹性观察”。第三，最接近的 Alzer–Liu–Shi 2013 论文及其 2026 年后续论文，目前只核对到出版社摘要和参考文献，尚不能排除其全文中的附加定理。[^1][^2][^5][^9]

较稳妥的贡献定位是：**在既有问题与约化基础上，补全所需的有限估计，给出覆盖所有正整数的统一结论、例外处理和完整等号分类。** 不宜声称首次研究绝对余弦和、首次发现全部特殊值，或首次提出整个凹性—排列证明路线。

## 核查尺度与覆盖边界

以下 18 条是按本问题相关性筛选的核心文献与公开记录；其中有期刊论文、书中章节和问题帖，不能统称为 18 篇研究论文。每条区分对象、结论、关系和阅读深度。

- **F：原文定理已核对**。读到关键定义、定理和适用条件；不代表逐行复核了全文所有证明。
- **S：历史扫描已核对**。关键数学式和原刊页码经图像核验。
- **A：摘要或可见原文片段**。能判断已展示结果，不能排除不可见部分。
- **I：间接核对**。从后续原始论文的引用定位，原作未取得；不得当成全文已读。

检索采用公式与文字变体、作者/题名/DOI 精确检索、原文参考文献回溯和被引线索核对。覆盖 arXiv、可被搜索引擎索引的 Scholar/MathSciNet/zbMATH 页面，以及 Project Euclid、JSTOR、Springer、Elsevier、Wiley、AMS、Cambridge、SIAM、Taylor & Francis 的定向查询；另追踪 MathNet、Numdam、期刊档案和俄语竞赛资料。**没有完成 Google Scholar、MathSciNet 或 zbMATH 的登录后全库系统检索**，各出版社的搜索覆盖也不等于全文覆盖。抓取日期、网页上线日期与原始出版年份分别处理。

## 18 条核心文献与公开记录

### 1. Gusyatnikov：M590 及其解答（1979/1980）

**P. B. Gusyatnikov（П. Б. Гусятников），《Задача М590 / Решение задачи М590》〔Problem M590 / Solution to Problem M590〕。** *Квант (Kvant)*：题目 1979 年第 10 期，第 26 页；解答 1980 年第 8 期，第 32–34 页。无已核实 DOI。[官方题目与解答](https://www.kvant.digital/problems/m590/)，[原刊第 33 页](https://www.kvant.digital/data/kvant_1980_8/jpg/0033.jpg)，[第 34 页](https://www.kvant.digital/data/kvant_1980_8/jpg/0034.jpg)。

**S；部分重叠，直接影响局部 novelty。** 给出 \(M_2=1/\sqrt2\) 及加权二项下界 \(a|\cos x|+|\cos2x|\ge\min\{1,a/\sqrt2\}\)，\(a\ge0\)。第 34 页另列 \(S_4\ge1+\sqrt3/2\) 为习题，还涉及倍频和及较弱的连续频率界。必须区分：四项不等式已刊出，其证明并未在该解答中展开。未在该文看到目标的完整一般结论。[^1]

### 2. HDD 292：完全相同的一般不等式问题（2022）

**HDD 292，*Showing that \(|\cos x|+|\cos2x|+\cdots+|\cos nx|\ge\lfloor n/2\rfloor\), where \(n\ne2,4,6\)*。** Math StackExchange，2022 年 8 月 6 日，问题 4506961。[原帖](https://math.stackexchange.com/questions/4506961/showing-that-cos-x-cos-2x-cdots-cos-nx-geq-lfloor-fracn2-rfloor)，[修订历史](https://math.stackexchange.com/posts/4506961/revisions)。无 DOI。

**F；同一问题及实质性方法重叠，未发现完整解答。** 两次修订均在 2022 年；当前正文、评论与官方接口均未显示回答。主张和思路已公开，但这不等于已有一般证明。原帖与论文的对应关系见下一节。[^2]

### 3. Christmas Bunny、Speyer 等：倍频绝对余弦和（2013/2018）

**Christmas Bunny（提问）；David E Speyer、achille hui、Dap 等（回答），*Showing that \(|\cos x|+|\cos2x|+\cdots+|\cos2^n x|\ge n/(2\sqrt2)\)*。** Math StackExchange，问题 306728，2013 年 2 月 18 日起；Dap 回答发表于 2018 年 2 月 6 日。[原帖及回答](https://math.stackexchange.com/questions/306728/showing-that-cos-x-cos-2x-cdots-cos-2nx-geq-dfracn2-sqrt2)。无 DOI。

**F；部分重叠及方法相关。** Speyer 给出二项极小值和分段凹性分析；Dap 证明更强的倍频和下界 \(\sum_{k=0}^n|\cos(2^kx)|\ge n/2\)。频率是 \(1,2,4,\ldots\)，并非 \(1,2,3,\ldots\)。相关配对思想有更早的 Kvant 先例；不能把这组回答当成目标的直接一般化。[^3]

### 4. Nigel1（目标论文记作 Ivan）：同一函数的闭式求和问题（2015）

**Nigel1（当前显示名；目标论文记作 Ivan），*Summation of the absolute value of the variable*。** Math StackExchange，2015 年 11 月 19 日，问题 1536892。[原帖](https://math.stackexchange.com/questions/1536892/summation-of-the-absolute-value-of-the-variable)。无 DOI。

**F；同一函数、不同问题，背景相关。** 问题是求 \(S_N(x)\) 的闭式，而非全局极小值；当前无回答。署名差异可能来自账号改名，不足以认定误引；投稿时宜使用可追踪的问题编号，并注明访问时显示名。[^4]

### 5. Alzer–Liu–Shi：交错加权绝对三角和（2013）

**Horst Alzer, Xiuping Liu, Xiquan Shi，*Inequalities for Alternating Trigonometric Sums*。** *Results in Mathematics* **63** (2013), 1215–1223；online first 2012-06-19。DOI：[10.1007/s00025-012-0264-8](https://doi.org/10.1007/s00025-012-0264-8)。[出版社摘要与文献表](https://link.springer.com/article/10.1007/s00025-012-0264-8)。

**A；部分重叠，最接近的期刊文献之一。** 研究 \(\sum_{k=1}^n(-1)^{k+1}(n-k+1)|\cos(kx)|\) 及对应正弦/混合和的锐界，并推广 Kelly 不等式。已展示的对象带交错符号及三角权重。**全文尚未取得，未排除其一般定理或附带推论。**[^5]

### 6. Kelly：更一般的度量不等式来源（1970）

**John B. Kelly，*Metric inequalities and symmetric differences*。** In O. Shisha (ed.), *Inequalities II*, Academic Press, New York, 1970, pp. 193–212。无已核实 DOI。[书籍目录扫描](https://external.dandelon.com/download/attachments/dandelon/ids/DE0049C95BCE9AD2EAC1FC12579B900569774.pdf)。

**I；潜在一般定理来源，需优先取得原文。** 后续原始论文引用其 \(\sum(-1)^{k+1}(n-k+1)|\sin(kx)|\ge0\)。目录定位 §9 “Cases of Equality” 起于 p.206，§10 “Trigonometric Inequalities” 起于 p.211。不能仅检查这个正弦推论；还需检查它所依赖的一般度量定理。尚无证据证明其覆盖目标。[^6]

### 7. Tureckii：绝对正弦和的早期锐界（1954）

**A. H. Tureckii（А. Х. Турецкий），*On a function deviating least from zero*；俄文题名 «Об одной функции, наименее уклоняющейся от нуля»。** *Belorussk. Gos. Univ. Uč. Zap. Ser. Fiz.-Mat.*，1954，pp.41–43；Alzer 1992 引为卷 16，原始刊号仍需核实。无已核实 DOI 或原论文 URL。

**I；部分重叠，原文缺口。** Alzer 1992 引述其 \(\sum_{k=1}^n(n+1-k)|\sin(kx)|\le(n+1)^2/4\)。这是加权正弦上界，不能直接替代本题余弦下界。1955 年俄文书目搜索索引另出现“19”，可能涉及 OCR 或不同编号体系；不要未经核验改卷号。[引述来源](https://journals.math.tku.edu.tw/index.php/TKJM/article/view/4538)。[^7]

### 8. Alzer：连接早期绝对值不等式的短文（1992）

**Horst Alzer，*A short note on two inequalities for sine polynomials*。** *Tamkang Journal of Mathematics* **23**(2) (1992), 161–163。DOI：[10.5556/j.tkjm.23.1992.4538](https://doi.org/10.5556/j.tkjm.23.1992.4538)。[期刊页](https://journals.math.tku.edu.tw/index.php/TKJM/article/view/4538)，[原文](https://journals.math.tku.edu.tw/index.php/TKJM/article/download/4538/1575/10345)。

**F；方法及引用链相关。** 给出 Lukács、Fejér 正弦多项式不等式的初等证明，并讨论后者等号。末页列出 Tureckii 与 Kelly 的绝对正弦和结果，是取得老文献前最有用的公开连接文献；本身未给目标极小值。[^8]

### 9. Alzer–Volkmer：目标预印本之前的新论文（2026）

**Horst Alzer, Hans W. Volkmer，*Inequalities for Sine Sums*。** *Results in Mathematics* **81** (2026), article 143，2026-07-02 发表。DOI：[10.1007/s00025-026-02696-3](https://doi.org/10.1007/s00025-026-02696-3)。[出版社](https://link.springer.com/article/10.1007/s00025-026-02696-3)。

**A；部分重叠，须补全文。** 摘要给出 \(\sum(n-k+1)(n-k+2)|\sin(kx)|\le C(n+1)^3\)，最佳 \(C=(9+\sqrt{41})\sqrt{14+6\sqrt{41}}/432\)。可见结果是加权上界；其参考文献确实引用第 5、6 条，属于真实的后向/前向连接。不能从一项摘要定理排除整篇文章。[^9]

### 10. Alzer–Kwong：平方和，应与一次绝对值区分（2017）

**Horst Alzer, Man Kam Kwong，*On inequalities for alternating trigonometric sums*。** *Publicationes Mathematicae Debrecen* **90**(1–2) (2017), 205–216。DOI：[10.5486/PMD.2017.7575](https://doi.org/10.5486/PMD.2017.7575)。[期刊全文](https://publi.math.unideb.hu/paper/2134/download/)。

**F；仅方法/背景相关，直接覆盖风险低。** Theorem 1 是 \(\sum(-1)^{k-1}\sin^2(kx)/k\ge-1/8\)，其余定理涉及正余弦平方的参数组合。加权推论要求 \(ka_k\) 或 \((2k-1)b_k\) 递减；平权不满足。**引言应明确写成平方三角和，避免将其描述为另一篇一次绝对值和论文。**[^10]

### 11. Glazyrin–Park：确能导出锐加权余弦界的一般定理（2020）

**Alexey Glazyrin, Josiah Park，*Repeated Minimizers of p-Frame Energies*。** *SIAM Journal on Discrete Mathematics* **34**(4) (2020), 2411–2423。DOI：[10.1137/19M1282702](https://doi.org/10.1137/19M1282702)。[arXiv v3 原文](https://arxiv.org/pdf/1901.06096v3)，[机构书目](https://scholarworks.utrgv.edu/mss_fac/124/)。

**F；部分重叠，已完成直接特化检查。** 平面 p-frame 能量下界在 \(p=1\) 时，确实导出本报告下文的 \(\sum(n+1-k)|\cos(kx)|\ge\lfloor n^2/4\rfloor\)。但相邻两个加权下界不能直接相减成目标下界；因此不是已发现的完整覆盖定理。核对版本为 arXiv v3 的 Theorem 4.2。[^11]

### 12. Belov：另一个“精确极小值与唯一性”问题（1993/1994）

**A. S. Belov，*On an extremal problem on the minimum of a trigonometric polynomial*。** *Russian Academy of Sciences. Izvestiya Mathematics* **43**(3) (1994), 593–606；俄文原刊 *Izv. RAN. Ser. Mat.* **57**(6) (1993), 212–226。DOI：[10.1070/IM1994v043n03ABEH001582](https://doi.org/10.1070/IM1994v043n03ABEH001582)。[原始文献页及全文入口](https://www.mathnet.ru/eng/im834)。

**F；方法/背景相关，重要的相似题名排除项。** 精确求解 \(\min_{a_k\ge1}[-\min_x\sum a_k\cos(kx)]\)，并证明最优多项式唯一。绝对值位置、系数是否参与优化、唯一性对象都与本题不同；并非目标的加权推广。[^12]

### 13. Odlyzko：带符号余弦和与单位圆多项式（1982）

**A. M. Odlyzko，*Minima of Cosine Sums and Maxima of Polynomials on the Unit Circle*。** *Journal of the London Mathematical Society*, second series, **26**(3) (1982), 412–420。DOI：[10.1112/jlms/s2-26.3.412](https://doi.org/10.1112/jlms/s2-26.3.412)。[出版社摘要](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/jlms/s2-26.3.412)。

**A；背景/方法相关。** 优化非负系数限制下的带符号余弦和负极小值；摘要含 \(O(n^{1/3}(\log n)^{1/3})\) 构造及多项式乘积估计。“极小值的绝对值”不能误读为“逐项绝对值之和的极小值”。本次未取得完整正文；已展示结果不提供目标精确公式。[^13]

### 14. Chidambaraswamy：含权重与相移，但取积分范数（1972）

**J. Chidambaraswamy，*On the Mean Modulus of Trigonometric Polynomials and a Conjecture of S. Chowla*。** *Proceedings of the American Mathematical Society* **36**(1) (1972), 195–200。DOI：[10.2307/2039059](https://doi.org/10.2307/2039059)。[JSTOR 原刊记录](https://www.jstor.org/stable/2039059)。

**A（含原文索引片段）；背景/方法相关。** 给出指数及带相移余弦多项式的平均模下界，涉及频率差的最大表示次数；并在该次数有界时推出负值估计。相移出现在总和内部，而绝对值在总和外部并积分。它不是对逐项绝对值函数的普遍下界；连续频率也不满足统一有界的差表示次数条件。[^14]

### 15. McGehee–Pigno–Smith：Littlewood 的积分下界（1981）

**O. Carruth McGehee, Louis Pigno, Brent Smith，*Hardy's inequality and the L1-norm of exponential sums*。** *Annals of Mathematics*, second series, **113**(3) (1981), 613–618。DOI：[10.2307/2007000](https://doi.org/10.2307/2007000)。[期刊记录](https://annals.math.princeton.edu/1981/113-3/p09)。

**F；背景相关。** Hardy 型系数估计推出单位系数指数和的积分 \(L^1\) 范数至少为 \(c\log N\)。读到原文重印中的定理。平均值下界不蕴含每个 \(x\) 处的下界，也不给本题极小点；宜与下一条合并为一个背景句引用。[^15]

### 16. Konyagin：Littlewood 问题的独立解决（1981/1982）

**S. V. Konyagin，*On a problem of Littlewood*。** *Mathematics of the USSR-Izvestiya* **18**(2) (1982), 205–225；俄文原刊 *Izv. Akad. Nauk SSSR Ser. Mat.* **45**(2) (1981), 243–265。DOI：[10.1070/IM1982v018n02ABEH001386](https://doi.org/10.1070/IM1982v018n02ABEH001386)。[MathNet 原始记录](https://www.mathnet.ru/eng/im1556)。

**A；背景相关。** 对互异整数频率指数和证明积分平均模的对数级下界。原刊年份和英译年份需区分。与第 15 条一样，研究对象是总和的积分范数，不是本题逐项绝对值的点态极小化。[^16]

### 17. Pichorides：Littlewood 理论的前驱（1980）

**S. K. Pichorides，*On the L1 norm of exponential sums*。** *Annales de l'Institut Fourier* **30**(2) (1980), 79–89。DOI：[10.5802/aif.785](https://doi.org/10.5802/aif.785)。[期刊原文入口](https://aif.centre-mersenne.org/articles/10.5802/aif.785/)。

**F；历史/方法相关。** 对具有 \(N\) 个模至少为 1 的非零系数的指数多项式，给出 \(c\log N/(\log\log N)^2\) 级积分下界。后来的 Littlewood 解答改进其数量级。本题没有因此成为直接推论；短篇引言可省略本条，但引用链应保留。[^17]

### 18. Kolountzakis：可选择子序列的余弦负值定理（1994）

**Mihail N. Kolountzakis，*A Construction Related to the Cosine Problem*。** *Proceedings of the American Mathematical Society* **122**(4) (1994), 1115–1119。DOI：[10.1090/S0002-9939-1994-1243831-8](https://doi.org/10.1090/S0002-9939-1994-1243831-8)。[JSTOR 原刊记录](https://www.jstor.org/stable/2161179)，[作者书目](https://eigen-space.org/publ/)。

**F（作者上传原文）；方法/背景相关。** 从给定频率或非负权重中选择子集，使某点的带符号余弦和足够负；含加权版本。它的结论是“存在子集、存在角度”，目标需要固定所有频率并控制“每个角度”。量词不能交换，未见目标锐界或等号分类由此直接得到。[^18]

## 已有贡献与论文贡献的对应

以下是对公式的比对，不是对作者独立发现过程的推断。

| 论文组成 | 已核对的公开先例 | 应如何描述 |
|---|---|---|
| 非例外下界及例外指标集合 | HDD 292，2022 | 问题本身已有来源 |
| Lemma 1 的有理断点约化 | 2022 原帖 | 明确归属已有约化 |
| 模 \(2q\) 折叠、周期公式 | 原帖及当日更新 | 整理并证明已有思路 |
| Lemma 3 的 \(A(q,r)\) 下界及闭式 | 当日更新中有等价公式 | 不应称作新约化 |
| Lemma 4–5 的完整严格估计 | 长区间仅断言、未展示证明；短区间明确留待解决 | 属于可主张的补全工作 |
| 所有 \(n\) 的统一等号分类 | 未定位到完整先例 | 可陈述本文给出，避免未经限定的首创声明 |

上述方法归属依据原帖及其两次修订；当前无回答不排除删帖、站外解答或更早题集。[^2] 特殊值的历史归属应另引第 1 条，不能因为一般证明是新增的，就把所有小例子的计算一并归为新发现。

## 一般定理能否直接推出本题

### 1. 需要区分三个不同的函数量

\[
\min_x\sum|\cos(kx)|,\qquad
\int\left|\sum a_k\cos(m_kx+\phi_k)\right|dx,\qquad
-\min_x\sum b_k\cos(m_kx).
\]

它们分别对应逐点向量 \(\ell^1\) 范数、三角多项式的积分 \(L^1\) 范数、带符号多项式的负极小值。Littlewood 文献主要处理第二个，Odlyzko/Belov 一线主要处理第三个。[^12][^13][^15][^16] 这是实质性的数学区别，不能仅凭关键词相似认定相同结果。

独立计算给出 \(\int_0^{2\pi}S_n(x)\,dx=4n\)，但一个已知平均值不能决定最小值。同样，虽有
\[
S_n(x)=\max_{\varepsilon_k\in\{-1,1\}}\sum\varepsilon_k\cos(kx),
\]
也不能擅自交换 \(\min_x\) 和 \(\max_\varepsilon\)。

### 2. p-frame 一般定理的实际特化

取平面单位向量 \(v_j=(\cos(jx),\sin(jx))\)，\(j=0,\ldots,n\)。直接计算
\[
\sum_{i\ne j}|\langle v_i,v_j\rangle|
=2\sum_{k=1}^n(n+1-k)|\cos(kx)|.
\]
将其代入 Glazyrin–Park 的 Theorem 4.2，得到锐界
\[
T_n(x):=\sum_{k=1}^n(n+1-k)|\cos(kx)|\ge\left\lfloor\frac{n^2}{4}\right\rfloor.
\]
\(x=\pi/2\) 达到该界。这里的特化与取等验证是本报告的数学推导。[^11]

虽然 \(T_n-T_{n-1}=S_n\)，**两个下界不能相减**。例如 \(n=2,x=\pi/4\) 时，两条加权界都成立，然而 \(S_2=1/\sqrt2<1\)。这排除了“通过相邻差分即可得到目标定理”的推法；不意味着已经排除所有可能的新组合证明。

### 3. 带符号、加权、相移与一般频率的检查

Belov 的系数优化在 \(n=1\) 时值为 1，本题则为 0；其“唯一”针对系数多项式，而非目标的极小角度。[^12] Alzer–Kwong 的平方、权重及单调条件均不能直接去掉。[^10] 已展示的这些定理没有同时保留本题的函数、量词和等号信息。

以下是独立的适用性检查，可用于继续审查未知文献：

- \(|\sin(k(x+\pi/2))|\) 只在奇数 \(k\) 时变成 \(|\cos(kx)|\)，偶数 \(k\) 仍是绝对正弦。统一平移不能消除该障碍。
- 对任意频率集合的同样正下界不可能无条件成立：频率全为奇数、\(x=\pi/2\) 时所有项都为零。真正涵盖目标的一般定理必须使用连续频率的算术结构或等价条件。
- 写成 \(\min_{t\in[-1,1]}\sum|T_k(t)|\) 只是 Chebyshev 变量替换；经典首一多项式的最大范数极小化是另一个问题。
- 把 \(|\cos t|\) 展为 Fourier 级数会引入无限多谐波和混合系数；不能未经条件核验套用有限非负系数定理。
- 即使找到正确的数值下界，也须逐步追踪每个比较的等号，才能判断是否同时涵盖 minimizer 分类。

对第 5、6、7、9 条，结论仍是“尚未取得足够全文证据”，不是“已证明不能覆盖”。

## 按相关性分层的文献地图

| 层级 | 文献 | 与目标的连接 | 投稿用途 |
|---|---|---|---|
| A：直接先例 | 1 Kvant；2 HDD 292 | 小例子、同一一般问题、实质约化 | 引言必须优先处理 |
| B：逐项绝对值的一般族 | 5、6、7、9；11 p-frame | 权重、交错、正弦、几何能量 | 核查能否特化；未读原文不能排除 |
| C：同函数/相关方法 | 3、4、8、10 | 闭式求和、倍频、正性、平方和 | 按实际使用选择引用 |
| D：不同极值对象 | 12、13、14、18 | 系数优化、平均模、子集选择 | 防止错误 novelty 对比 |
| E：Littlewood 背景 | 15、16、17 | 积分 \(L^1\) 理论 | 一两句定位即可 |

已经核实的引用连接包括：**Tureckii/Kelly → Alzer 1992；Kelly → Alzer–Liu–Shi 2013 → Alzer–Volkmer 2026；Pichorides 1980 → McGehee–Pigno–Smith 1981；Odlyzko → Belov 的带符号极值研究。** “同属一层”不表示彼此引用；特别是 Kvant 与 HDD 292 之间，本次未建立直接引用关系。[^5][^8][^9][^12][^15]

## Novelty risk assessment

这里的“风险”区分已发生的贡献重叠与尚未解决的检索缺口，不给出无法校准的百分比。

| 待评估主张 | 判断 | 依据与影响 |
|---|---|---|
| “首次提出该一般问题” | 已有明确先例 | 第 2 条；应改为解决已有问题 |
| “全部例外值首次求出” | 不成立 | 第 1 条的二项结果及四项锐界 |
| “主要约化路线是新方法” | 归属表述风险高 | 第 2 条已包含关键框架 |
| “已有人发表完整全 \(n\) 定理” | 本次未找到 | 不能由部分重合推成完整重复 |
| “更一般旧定理可直接推出全结果” | 已查若干排除项；关键缺口未清除 | 第 5、6、7、9 条仍需全文 |
| “完整全 \(n\) 等号分类已有先例” | 本次未定位 | 不应把单个小 \(n\) 的等号也笼统视为新 |
| “可证明全球首次完整解答” | 证据不足 | 公开搜索与历史文献覆盖有限 |

**综合判断：完整证明的新增性仍有合理空间，但结论应暂定；已确认的局部与方法先例必须体现在稿件中。** 主要剩余工作是近邻文献的全文核查与俄语题集回溯，不是继续累积更多泛泛的 Littlewood 引用。

若后续发现旧定理已给出所有 \(n\ge7\) 的目标下界，即使它没有写三个小例子，也会明显缩小论文的新增范围；若只给弱常数、渐近式、有限网格值或数值猜测，则不能认定已解决本题。仅有正确猜测也不等同于完整证明。

## 可用于 introduction 的英文草稿

以下措辞陈述本文完成什么，不作未经充分支持的绝对优先权声明。可配合附带的 `related_work.tex` 和 `related_work.bib` 使用；不必把本报告的全部 18 条都放进短篇引言。

Special cases of the present problem have earlier precedents. In his solution to Problem M590, Gusyatnikov gives the two-term minimum and states the sharp four-term inequality as an additional exercise [1]. The general inequality, excluding \(n=2,4,6\), was posed by HDD 292 in 2022, together with the reduction to rational break points and finite trigonometric sums [2]. We complete the required estimates and give a unified statement for all positive integers, including the exceptional values and all equality cases.

Inequalities involving termwise absolute values have also been studied for alternating sums with triangular weights by Alzer, Liu and Shi [5], and for weighted absolute sine sums by Alzer and Volkmer [9]. The alternating square-sum inequalities of Alzer and Kwong [10] concern a related, but different, family.

The position of the absolute value is essential here. Classical work on minima of signed cosine sums, such as Odlyzko [13], and the integral \(L^1\) inequalities associated with Littlewood's problem, established independently by McGehee, Pigno and Smith [15] and Konyagin [16], concern different extremal functionals. These results do not directly determine the pointwise minimum of the fixed, unweighted sum considered in this note.

建议在约化部分再明确标注第 2 条的来源；仅在引言引用一次，未必足以让读者看清已知步骤与新增估计的边界。关于第 5、9 条，草稿只陈述已核实的研究对象，未声称其所有结果都与本题无关。

## 推荐继续手工核查的高风险引用链

### 优先级 1：Kvant 及俄语题集

从第 1 条末尾四项与连续频率习题出发，查 1980 年以后 M590 的补充解答、勘误、引用，以及相关竞赛题集。可检索作者名 **Гусятников**、题号 **М590**、关键词 **сумма модулей косинусов**；沿 2005 年《Задачник «Кванта». Математика》第一部分等汇编继续定位。汇编是待查线索，本次未逐页核对。

**需要回答：** 是否出现了更强的连续频率界、\(n=6\) 精确式、全部例外指标或一般等号分类？此链比再查普通余弦和更可能发现直接先例。

### 优先级 2：Kelly → 2013 → 2026

取得 Kelly pp.193–212，先读 §10，再回查一般定理与 §9 等号；取得 Alzer–Liu–Shi 2013 全文；最后读 Alzer–Volkmer 2026 的全部定理和推论。核对变量、权重的允许范围、相移形式、交错符号是否必要，以及是否存在非交错的附带结论。相关链接见第 5、6、9 条。

**需要回答：** 能否通过合法的参数特化得到所有角度下的 \(S_n\) 下界，而不只是积分、带权量或另一个函数？若能，还要核对取等条件。

### 优先级 3：2022 问题的来源与站外延伸

核查第 2 条是否来自题集、竞赛、其他论坛或作者已有笔记，追踪引用该问题编号的页面。目前公开修订和评论未给出更早题源；不能将其当成“问题最早于 2022 年出现”的证明。本次没有联系发帖人或论文作者。

### 优先级 4：Tureckii → Mitrinović

以第 7 条俄文题名调取 1954 年原文，并核对卷/期编号；检查 D. S. Mitrinović, *Analytic Inequalities* (Springer, 1970), p.252 及邻近条目。除了已知加权正弦上界，还要查看有无一般绝对三角和结论。原文未核对前，不应把二手引述升级为完整阅读。

### 优先级 5：带符号极值的深层旧文献

按问题相近程度，继续检查：

- Belov 1994 → Belov, *On the extremal problem on the minimum of the free term of a nonnegative trigonometric polynomial*, *Proc. Steklov Inst. Math.* **277**, suppl.1 (2012), S55–S72，[DOI](https://doi.org/10.1134/S0081543812050070)。重点仍是其精确优化对象。
- Pichorides, *A remark on exponential sums*, *Bull. AMS* **83**(2) (1977), 283–285，[DOI](https://doi.org/10.1090/S0002-9904-1977-14308-5) → S. A. Pichugov, *Estimates of the minimum of trigonometric sums*（1982，俄文会议集，页码待核）→ Belov, *Use of complex analysis for deriving lower bounds for trigonometric polynomials*, *Mathematical Notes* **63** (1998), 709–716，[DOI](https://doi.org/10.1007/BF02312763)。
- Odlyzko 全文及其后续的非负整数系数构造。需要检查是否存在未在摘要展示的有限锐不等式；目前没有证据把这条链视为已知重复。

这些后续条目用于精确指出缺口，不算作已完成定理级核查的核心记录。对于尚未取得的全文，优先通过机构图书馆、作者公开稿或馆际互借取得；本次没有购买文献。

## 来源

[^0]: Ruixi Sun. *Exact Minima of Finite Absolute Cosine Sums*. arXiv:2609.05545v1 (2026). [全文](https://arxiv.org/html/2609.05545v1)。
[^1]: P. B. Gusyatnikov. *Problem M590 / Solution to Problem M590*. Kvant, 1979(10), 26; 1980(8), 32–34. [档案](https://www.kvant.digital/problems/m590/)，[关键原刊页](https://www.kvant.digital/data/kvant_1980_8/jpg/0034.jpg)。
[^2]: HDD 292. *Showing that …*, Math StackExchange 4506961 (2022). [原帖](https://math.stackexchange.com/questions/4506961/)，[修订](https://math.stackexchange.com/posts/4506961/revisions)。
[^3]: Christmas Bunny et al. *Showing that …*, Math StackExchange 306728 (2013–2018). [原始问答](https://math.stackexchange.com/questions/306728/)。
[^4]: Nigel1 (cited as Ivan in arXiv v1). *Summation of the absolute value of the variable*. Math StackExchange 1536892 (2015). [原帖](https://math.stackexchange.com/questions/1536892/)。
[^5]: Alzer, Liu and Shi. *Inequalities for Alternating Trigonometric Sums*. Results Math. 63 (2013), 1215–1223. [出版社](https://link.springer.com/article/10.1007/s00025-012-0264-8)。
[^6]: Kelly. *Metric inequalities and symmetric differences*. Inequalities II (1970), 193–212. [目录](https://external.dandelon.com/download/attachments/dandelon/ids/DE0049C95BCE9AD2EAC1FC12579B900569774.pdf)；数学结论通过第 5、8 条核对。
[^7]: Tureckii. *On a function deviating least from zero* (1954), 41–43；卷号待核。数学结论与书目通过第 8 条核对。编号疑点来自[1955 年国家书目搜索索引所指扫描](https://dspace.nplg.gov.ge/bitstream/1234/446229/1/Jurnalnaia_Letopis_1955_N2.pdf)，未取得可核图像。
[^8]: Alzer. *A short note on two inequalities for sine polynomials*. Tamkang J. Math. 23(2) (1992), 161–163. [原文](https://journals.math.tku.edu.tw/index.php/TKJM/article/download/4538/1575/10345)。
[^9]: Alzer and Volkmer. *Inequalities for Sine Sums*. Results Math. 81, 143 (2026). [出版社](https://link.springer.com/article/10.1007/s00025-026-02696-3)。
[^10]: Alzer and Kwong. *On inequalities for alternating trigonometric sums*. Publ. Math. Debrecen 90(1–2) (2017), 205–216. [全文](https://publi.math.unideb.hu/paper/2134/download/)。
[^11]: Glazyrin and Park. *Repeated Minimizers of p-Frame Energies*. SIAM J. Discrete Math. 34(4) (2020), 2411–2423. [核对版本 v3](https://arxiv.org/pdf/1901.06096v3)。
[^12]: Belov. *On an extremal problem on the minimum of a trigonometric polynomial*. Russian Acad. Sci. Izv. Math. 43(3) (1994), 593–606. [原始记录及全文](https://www.mathnet.ru/eng/im834)。
[^13]: Odlyzko. *Minima of Cosine Sums and Maxima of Polynomials on the Unit Circle*. JLMS (2) 26(3) (1982), 412–420. [出版社](https://doi.org/10.1112/jlms/s2-26.3.412)。
[^14]: Chidambaraswamy. *On the Mean Modulus of Trigonometric Polynomials and a Conjecture of S. Chowla*. Proc. AMS 36(1) (1972), 195–200. [原刊](https://www.jstor.org/stable/2039059)。
[^15]: McGehee, Pigno and Smith. *Hardy's inequality and the L1-norm of exponential sums*. Ann. Math. 113(3) (1981), 613–618. [期刊](https://annals.math.princeton.edu/1981/113-3/p09)，[Pigno 大学档案中的原文重印](https://www.math.ksu.edu/about/awards-history/history/historical_materials_additional/L_Pigno_collection-merged-compressed.pdf)。
[^16]: Konyagin. *On a problem of Littlewood*. Math. USSR-Izv. 18(2) (1982), 205–225. [原始记录](https://www.mathnet.ru/eng/im1556)。
[^17]: Pichorides. *On the L1 norm of exponential sums*. Ann. Inst. Fourier 30(2) (1980), 79–89. [期刊](https://aif.centre-mersenne.org/articles/10.5802/aif.785/)。
[^18]: Kolountzakis. *A Construction Related to the Cosine Problem*. Proc. AMS 122(4) (1994), 1115–1119. [原刊](https://www.jstor.org/stable/2161179)，[作者上传原文](https://www.researchgate.net/publication/2759486_A_construction_related_to_the_cosine_problem)。
