# 检索审计与复查清单

检索截止：2026-09-09。对应主报告 literature_review_zh.md。这里记录检索入口、真实访问层级和排除理由，便于后续补查；不把未命中解释为不存在。

## 入口与限制

| 入口 | 本次实际覆盖 | 限制 |
|---|---|---|
| arXiv | 目标 v1、p-frame v3、相关题名/公式检索 | 未做全库 TeX 公式穷举 |
| Google Scholar 可索引页面 | 网页索引、原论文提供的 Scholar 引用入口 | 未登录全库逐条检索，未取得完整 cited-by 导出 |
| MathSciNet / zbMATH | 域名定向搜索、MathNet/期刊所列 MR/Zbl 交叉记录 | 没有机构订阅数据库访问；不声称完整审阅 reviews |
| Springer | 2013/2026 出版社摘要和完整参考文献；其他相关题名 | 两篇最接近文章的全文需订阅，公开 PDF 入口未取得正文 |
| Wiley / LMS | Odlyzko 摘要；相关题名与作者目录 | Odlyzko 全文未取得 |
| AMS / Annals / JSTOR | 书目、摘要、原刊索引片段、作者/大学档案原稿 | 部分直接全文访问失败；逐条阅读深度见主报告 |
| SIAM | Glazyrin–Park 出版社和机构书目，arXiv 全文 | 定理核对固定为 v3 |
| Project Euclid / Cambridge / Elsevier / Taylor & Francis | 相关关键词和题名的定向检索、引用链筛选 | 未做每个平台的登录后全库检索 |
| MathNet / AIF / Numdam | Belov、Konyagin、Pichorides 等原始记录与可用全文 | 阅读层级按报告逐条标明 |
| Math StackExchange | 原问题、回答、修订及评论；官方接口核对三个问题的回答数 | 不覆盖删除内容、私下或站外解答 |
| Kvant | 官方 M590 档案；1980 第8期32–34页原刊扫描 | 未逐卷核对后续所有汇编、勘误与补充解答 |

## 已执行的主检索式

以下保留主检索中的字符串；部分严格公式/域名检索没有产生相关命中。搜索引擎不可靠地索引竖线、上下标和数学公式，因此同时使用文字、题号和作者变体。

1. `"sum" "absolute" "cosines" minimum inequality`
2. `"sum" "|cos(kx)|" minimum`
3. `"sum" "absolute cosine" minimum -site:arxiv.org`
4. `"cos" "minimum" "Chebyshev" "absolute" sums`
5. `"absolute cosine sums"`
6. `"absolute trigonometric sums" minimum`
7. `"cos x" "cos 2x" "cos nx" "minimum" absolute`
8. `"суммы" "модулей" "косинусов" минимум`
9. `"absolute" "cosine sums" inequalities -site:reddit.com`
10. `"sum of absolute" "cosines" inequality minimum`
11. `"余弦" "绝对值" "最小值" "n" 求和`
12. `"Kvant" "590" cosine`
13. `"minimum" "p-frame energy" "circle"`
14. `"sum" "absolute" "cos" "minimum" "weights" inequality trigonometric`
15. `"sums" "absolute values" "Chebyshev polynomials"`
16. `"energy" "cycle" "cot" "4" Gutman`
17. `"p-frame" "minimum" energy`
18. `"cosine" "absolute" "sum" "shifted" inequality`
19. `"|cos" "sum" "minimum" site:zbmath.org`
20. `"absolute" "trigonometric sums" site:mathscinet.ams.org`
21. `"absolute" "trigonometric" "inequalities" [domains: zbmath.org]`
22. `"absolute" "trigonometric" sums [domains: mathscinet.ams.org]`
23. `"absolute cosine" sums [domains: scholar.google.com]`
24. `"Repeated minimizers" Glazyrin Park arxiv`
25. `"absolute" "trigonometric sums" [domains: projecteuclid.org, jstor.org, cambridge.org, tandfonline.com]`
26. `"absolute" "cosine" "inequalities" [domains: link.springer.com, sciencedirect.com, onlinelibrary.wiley.com, ams.org]`
27. `"cos" "2,4,6" inequality`
28. `"sum" "absolute cosine" "minimum" -site:math.stackexchange.com`
29. `"finite absolute" "cosine"`
30. `"cosine sums" "absolute values" minimum`
31. `"cos kx" "absolute" inequality Alzer`
32. `"cos(kx)" "floor" "minimum"`
33. `"Inequalities for Sine Sums" "Volkmer" 2026`
34. `"Metric inequalities and symmetric differences" Kelly pdf`
35. `"cos" "absolute" "Kelly" trigonometric inequalities`
36. `"absolute cosine sums" arxiv Sun`
37. `"Two inequalities for sine polynomials" Alzer 1992 DOI`
38. `"On a function deviating least from zero" Tureckii`
39. `"sum" "|cos" "minimum" "Tureckii"`
40. `"minimum" "absolute" "trigonometric" "shifted sums"`

## 补充检索组

- 直接问题：4506961、1536892、306728、4185602；完整题名；各自修订历史和回答。
- 公式/例外：cos x / cos 2x / cos nx + 2,4,6；cos4x / sqrt3 / cos3x；cos6x + absolute + minimum。
- 俄文：М590、Гусятников、суммы модулей косинусов、минимум、1979、1980；中文：余弦、绝对值、最小值。
- 最近邻：Alzer Liu Shi + 两个 alternating trigonometric sums 题名；DOI 10.1007/s00025-012-0264-8；Alzer Volkmer + Inequalities for Sine Sums + DOI 10.1007/s00025-026-02696-3。
- 原文获取：上述题名分别搭配 PDF / theorem / 作者名；排除聚合站后查作者稿；检查出版社直接 PDF 入口。
- 老文献：Kelly + Metric inequalities and symmetric differences；Tureckii / Turetskii + function deviating least；Турецкий + «Об одной функции, наименее уклоняющейся от нуля» + 1954。
- 替代表述：Chebyshev + absolute values + minimum；sum |T_k|；absolute trigonometric sums；cosine sums moduli；sum of absolute sines；hypermetric；p-frame energies。
- Littlewood：McGehee Pigno Smith + Hardy inequality；Konyagin + On a problem of Littlewood；Pichorides + L1 norm exponential sums / One-sided / A remark on exponential sums。
- 带符号极值：Odlyzko + Minima of cosine sums；Belov + On an extremal problem on the minimum；Kolountzakis + A construction related to the cosine problem + Theorem2 + weights。
- 后续引用：Bourgain + Sur le minimum d'une somme de cosinus；Roth + On cosine polynomials corresponding to sets of integers；Belov1998/2012；Pichugov1982。
- 固定网格与相移：shifted absolute sines、partial sum absolute cosine、cosine regular grid；筛查相移是共同相位还是频率乘以变量。

## 已核对的关键历史证据

1. Kvant M590：官方档案指向1979题目及1980解答。原刊第33页核对二项极小值及加权式，第34页核对四项锐界确为附加练习。以印刷页码为准，不以图片文件的顺序号代替。
2. MSE4506961：两次修订均为2022-08-06，第二次加入短区间表达式。当前官方接口 answer_count=0。
3. MSE1536892、4185602：当前官方接口 answer_count=0。未将提问者的猜式/CAS输出当成已证明文献。
4. Alzer2013：online first 2012-06-19，期刊卷年2013；Alzer–Volkmer2026：2026-07-02。以出版记录而非搜索抓取日期判定先后。
5. Alzer–Kwong2017：完整五个主定理的对象为平方和；不是一次绝对值和。
6. Glazyrin–Park：Theorem4.2的参数及奇偶情形已核对；主报告的三角权重推导另经数学复查。

## 排除或降级的典型命中

| 命中 | 处理及理由 |
|---|---|
| MSE4185602（2021）fixed-grid absolute cosine sums | 同类周期公式线索，但无回答，且问题中的表达式有疑似转录错误；未作为既有极小值定理 |
| 无可核年份的波兰论坛四项不等式 | 不用于优先权时间判断；已有Kvant原刊证据更强 |
| 自动生成的Kvant解题页面 | 仅作为找到题号的线索；数学与历史结论全部回到官方扫描 |
| 将“sum of absolute values”匹配成“absolute value of sum”的页面 | 按数学对象剔除或转入背景层 |
| 一般非负/正三角多项式论文 | 核对系数、区间与量词；无直接特化时不称更一般结果 |
| Chowla新进展、Bourgain/Ruzsa负值估计 | 属于带符号余弦和背景；不为凑数量写成直接前作 |
| arbitrary-frequency lower bounds | 全奇数频率反例说明必须核查算术结构条件 |
| graph energy / regular polygons | 完整周期恒等式线索，不等于连续变量下的全部前缀极小化 |
| ResearchGate“相关论文”、聚合站列表 | 只有原文文献表确认后才视为真实引用关系 |

## 尚需补查的材料

- Alzer–Liu–Shi2013全文。
- Alzer–Volkmer2026全部14页，而非出版社首页预览。
- Kelly1970 pp193–212，尤其一般定理、等号与三角推论。
- Tureckii1954原文和真实刊号；Mitrinović1970 p252及邻近条目。
- Kvant M590后续题集与俄语竞赛解答的强化结果。
- HDD292问题更早的来源、站外引用或历史存档。
- Odlyzko1982全文；Pichugov1982及相关俄文参考链。

这份清单中的缺口已经纳入主报告的风险判断；任何一项都未被默认为“没有相关结果”。

