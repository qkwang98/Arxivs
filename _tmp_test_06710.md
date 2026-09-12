# Filtered deformations of three-variable polynomial algebras

作者：Jason Bell、Boris Li（University of Waterloo）。

## 主要定理（中文概括）

本文完整分类了三元多项式环的全部 filtered deformation，并用该分类回答了 Etingof 问题的一个特例。设 K 为域，A 是带滤链 V0 ⊆ V1 ⊆ V2 ⊆ … 的代数，其相伴分次环恰为三变量多项式环 K[x,y,z]，则 A 必同构于文中所列九族代数之一，主要包括：unipotent 型的迭代 Ore 扩张；满足 [x,y]=z、[x,z]=γy、[y,z]=f(x) 的族；以及若干只存在于特征 2 或特征 3 的族。在此分类基础上，若 K 是正特征（char K = p > 0）的代数闭域，则这样的 A 必定满足一个多项式恒等式，即 PI 性对三变量多项式环的 filtered deformation 普遍成立。这正是 Etingof 所提问题在"相伴分次环为三变量多项式环"这一情形下的肯定回答。作者同时声明：该"分类"并不声称九族之间互不同构，族内部与族之间的同构问题仍未解决；当 K 代数闭且特征为零时，分类只余族 (1)、(3)、(4)。

## 证明方法（三步）

第一步（分类）：按生成元次数的排序 a ≤ b ≤ c，并对 [x,y] 做换元，把问题归为 Case I（[x,y]=h(x)）、Case II（[x,y]=y）、Case III（[x,y]=z），再把最难的 Case III 细分为 III(a)（b > 2a−2）与 III(b)（b ≤ 2a−2）。在每个情形中借助 Jacobi 恒等式逐项比较系数，把相容的代数整理成九族；反向则用 Bergman 的 diamond lemma（PBW 定理式证明）验证各族确实是三变量多项式环的 filtered deformation。

第二步（PI 判据）：证明若 A 含有非平凡中心元，则 A 是 PI。技术核心是一则引理：相伴分次环为有限生成 Noether 整环时，除环中任何包含基域的子域都有限生成（用 de Jong 的论证），再结合 Bell 关于 Krull 维数二的 filtered deformation 为 PI 的结果，把"存在中心元"升级为"满足多项式恒等式"。

第三步（构造中心元）：族 (1) 直接由 Brown–Zhang 关于 unipotent Ore 扩张的定理得到 PI；族 (2)、(5)、(7)、(9) 显式写出形如 x^{p²} − γ^{(p²−p)/2} x^p 的中心元；族 (3)、(4) 先用 Sage Math 在特征零下搜出中心元，再用提升引理把中心元过渡到正特征；族 (6)、(8) 则利用 ad_x 在有限维不变量空间上的线性相关性，构造出以 x 为变量的中心多项式。
