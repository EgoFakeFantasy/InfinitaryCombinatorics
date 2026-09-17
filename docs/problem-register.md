# 无穷组合开问题筛选与七天研究预算评估

检索截止：2026-09-17。十年界线：2016-09-17。

## 结论与证据边界

本记录包括八项主要候选、一项年代仍需补查的观察项，以及一项在本次核查中得到直接证明的文献问题。不是全部无穷组合开问题的穷尽目录。

“主要候选”的含义是：在近十年的原始论文中找到明确的问题表述；未在追索的出处及后续材料中发现其早于十年界线的明确表述，也未检到完整解答。它不是作者确认、数据库穷尽或绝对的首次提出日期认证。

第二条排除条件——“被充分研究且没有证明路线”——不能只凭引用量或论文年份机械认证。本次主要保留有具体参数缺口、邻近正面定理或可检验构造方案的问题；没有把“没搜到后续论文”当作“很容易”。

领域边界按问题本身而非论文全部应用判断。保留序数组合、无限图染色、分割关系、几乎不交族和经典基数不变量；不把拓扑空间性质、描述复杂度、算子代数或强迫模型构造本身作为候选目标。组合问题的否定答案可能最终需要独立性分析，这一点不能预先排除。

## 主登记表

| 编号 | 问题 | 最早核见的明确问题出处 | 原文编号 | 当前分类 |
|---|---|---|---|---|
| A1 | 有界深度的 disjoint type guessing 是否总成立？ | Lambie-Hanson–Uhrik，2023 年预印本，2024 年发表 [1] | Question 6.1 | 主要候选；七天优先 |
| A2 | 每个 Δ-regressive 染色是否必有单色四元组？ | Lambie-Hanson–Soukup，2020 年预印本 [2] | Problem 5.2 的四元组部分 | 主要候选；七天备选 |
| A3 | 存在 HM 图是否蕴含存在 regressive HM 图？ | Lambie-Hanson–Uhrik，2023 [1] | Question 6.3 | 主要候选 |
| A4 | 在 ω₁ 上是否存在极大无单色三角形的可数色染色？ | Lambie-Hanson–Soukup，2020 [2] | Problem 5.3 | 主要候选 |
| A5 | over-partition pump-up 定理能否去掉 χ≤cf(λ)？ | Kojman–Rinot–Steprāns，2022 [3] | Question 5.1 | 主要候选；宽参数版本不优先 |
| A6 | 能否同时指定有向图的规模、二色数为 κ，并排除短有向圈？ | Joó，2019 [4] | Question 3.1 | 主要候选；完整全基数版本不优先 |
| A7 | ZFC 中是否存在规模为 c 的 nowhere MAD、fin-intersecting 族？ | Corral–Rodrigues，2022–2023 预印本，2024 正式版 [5] | 正式版 Question 3.9 | 主要候选 |
| A8 | c>a≥s 是否保证存在规模为 a 的非 fin-intersecting MAD 族？ | Corral–Rodrigues，2022–2023/2024 [5] | 正式版 Question 4.10 | 主要候选 |
| B1 | SS 族存在 ⇒ almost strongly separable 族存在：能否删去 b=c？ | 在 2025 年末在线发表的修订版核见 [7]；最早提问时间待补查 | 正式版 Question 5.20 | 观察项，暂不计入严格合格清单 |
| R0 | 非 fin-intersecting AD 族的最小规模是否为 s？ | [5] 正式版 Question 4.9；[6] Question 11 再次提出 | Q4.9 / Q11 | 本次得到下述直接证明；不再列作待攻开题；新颖性未认证 |

## A1：有界深度类型猜测

有限不交类型记录两个等长有限序数集的交错次序。若 $a,b$ 长度均为 $n>0$，其深度是使

$$
\max(a)<b(k)\quad\text{或}\quad\max(b)<a(k)
$$

成立的最小 $k<n$。宽度为 $n$，深度与宽度不能混同。

给定类型序列 $\vec t=\langle t_k:k<\omega\rangle$，令 $n_k$ 为宽度。问题是：若深度有统一有限上界，能否选择 $C$-序列，使每个 $f:\lim(\omega_1)\to\omega$ 都有 $\alpha<\beta$ 与 $k$ 满足

$$
f(\alpha)=f(\beta)=k,\qquad
\operatorname{type}(C_\alpha[n_k],C_\beta[n_k])\in\{t_k,\bar t_k\}?
$$

这里 $C_\alpha$ 是趋于 $\alpha$ 的递增 ω 序列，$C_\alpha[n]$ 是其前 $n$ 项。[1, Q6.1]

已知相邻结论是有界宽度情形；不能将它直接当作有界深度的证明。[1, Theorem 2.7]

**我的研究路线建议：**尝试把已知证明中依赖宽度的安排压缩成仅依赖深度的有限交错骨架。核心任务是证明一个统一的尾部补全引理：骨架选定后，任意所需宽度的剩余点都能放置，而不破坏同色配对和类型。若补全所需参数仍依赖具体宽度，就没有消除原障碍。只证明任意固定宽度的结论，不算完成此题。

## A2：Δ-regressive 染色中的单色 K₄

设 $\kappa$ 正则不可数，$x,y\in2^\kappa$ 不同，令

$$
\Delta(x,y)=\min\{\xi<\kappa:x(\xi)\ne y(\xi)\}.
$$

若 $c:[2^\kappa]^2\to\kappa$ 满足 $\Delta(x,y)>0\Rightarrow c(x,y)<\Delta(x,y)$，是否必有四个不同点，其六条边同色？原文同时询问无限及不可数单色集，这些加强版本不另行计数。[2, P5.2]

**我的研究路线建议：**先按四条分支的首次分裂形状分类，寻找把六条边同时压至一个颜色的融合条件。有限模式枚举可用于排除错误引理，不能替代任意正则不可数基数上的实现论证。七天目标只选完整的 K₄ 子问，不把更强的无限版本混入。

## A3：HM 图的回归强化

HM 图是 ω₁ 上的不可数色数图，各顶点的下邻居集有限，或是趋于该顶点的 ω 序列。regressive HM 还要求不存在正常顶点染色 $c:\omega_1\to\omega_1$，使其在所有非零极限点满足 $c(\alpha)<\alpha$。

问题为

$$
\exists\,\mathrm{HM}\quad\Longrightarrow\quad\exists\,\mathrm{regressive\ HM}?
$$

这是两个存在性命题之间的蕴含，不是“每个 HM 图自己都回归不可染色”。作者指出其检查的构造方法均可改造为回归版本。[1, Q6.3]

**我的研究路线建议：**从给定 HM 图构造新图，把新图的回归正常染色转换为原图的可数正常染色，同时保持梯状下邻居限制。仅用 Fodor 引理取得驻集上的常值，并不能自动完成这一转换。若新的边复制破坏梯状性，这条路线便没有推进到目标。

## A4：ω₁ 上的极大无三角形染色

寻找 $c:[\omega_1]^2\to\omega$，无单色三角形，并且不能在增加一个新顶点后、仍用相同颜色集扩张为无单色三角形染色。[2, P5.3]

展开极大性的要求是：

$$
\forall d:\omega_1\to\omega\ \exists\alpha<\beta<\omega_1\quad
c(\alpha,\beta)=d(\alpha)=d(\beta).
$$

**我的研究路线建议：**构造阶段同时维护无三角形限制与对顶点颜色函数的覆盖要求。关键难点是上述对所有 $d$ 的量词；让每个单色图都具有不可数色数，并不等于取得这个覆盖性质。不建议仅靠一般逐点递归就投入整周。

## A5：去掉 pump-up 定理中的共尾数限制

对固定分割 $p:[\lambda^+]^2\to\lambda$，现有定理在 $\chi\le\operatorname{cf}(\lambda)$ 下将

$$
\operatorname{Pr}_1(\lambda^+,\lambda^+,\lambda,\chi)_p
$$

提升为

$$
\operatorname{Pr}_1(\lambda^+,\lambda^+,\lambda^+,\chi)_p.
$$

原问是能否去掉该限制；应保留原定理其余参数。论文另有统一提升算子，但不能额外把该更强的统一性要求强加为原问题。[3, Theorem A; Q5.1]

这里 $\operatorname{Pr}_1(\kappa,\kappa,\theta,\chi)_p$ 要求有染色 $c:[\kappa]^2\to\theta$，对每个 $\sigma<\chi$、规模为 $\kappa$ 的两两不交、成员序型为 $\sigma$ 的集族 $\mathcal A$，以及每个 $\tau:\operatorname{codom}(p)\to\theta$，可找到分离排列的 $a,b\in\mathcal A$，使 $c(\alpha,\beta)=\tau(p(\alpha,\beta))$ 在 $a\times b$ 上成立。

**我的研究路线建议：**先逐处定位证明为何使用 $\sigma<\operatorname{cf}(\lambda)$，尝试用分块一致化替代一次性的共尾有界化。首个可试验的区域是可数共尾奇异 $\lambda$、$\chi=\omega_1$；该区域即使成功，也只算局部结果，不能冒充原题的完全解决。

## A6：有向图的规模与二色数精确相等

有向图的二色数 $\chi_d(D)$ 是把顶点分成诱导无有向圈子图所需的最少份数。对每个无限基数 $\kappa$ 和每个有限 $n$，是否存在 $D$ 使

$$
|V(D)|=\chi_d(D)=\kappa,
$$

且 $D$ 无长度小于 $n$ 的有向圈？[4, Q3.1]

该文已有高二色数且无短圈的构造；额外障碍是把顶点规模也精确控制为同一个 $\kappa$。

**我的研究路线建议：**尝试从大构造抽取规模 $\kappa$ 的子图，并设计阻止低色数染色的见证系统。不能假定高二色数自动向大小恰当的子图反映。$(\kappa,n)=(\omega_1,4)$ 是可单独试验的子目标；完成它不等于完成任意基数版本。

## A7、A8 与 R0 的共同定义

$\mathfrak c=2^{\aleph_0}$，$\mathfrak a$ 是无限 MAD 族的最小规模，$\mathfrak s$ 是分裂族的最小规模。AD 表示两个不同成员交集有限；MAD 表示对加入新的无限集而言极大。

一个 fin-sequence 是两两不交、非空有限集的序列 $C=\langle C_n:n<\omega\rangle$。AD 族 $\mathcal A$ 为 fin-intersecting，若每个此类 $C$ 都存在无限 $I\subseteq\omega$，使族

$$
\bigl\{\{n\in I:a\cap C_n\ne\varnothing\}:a\in\mathcal A\bigr\}
\setminus[I]^{<\omega}
$$

是中心族，即每个非空有限子族的交仍无限。[5, Definition 2.3]

记 $\mathcal I(\mathcal A)$ 为由 $\mathcal A$ 和有限集生成的理想。nowhere MAD 表示：对每个 $X\notin\mathcal I(\mathcal A)$，存在无限 $Y\subseteq X$ 与 $\mathcal A$ 的每个成员几乎不交。

### A7

ZFC 能否构造 $|\mathcal A|=\mathfrak c$、同时 nowhere MAD 与 fin-intersecting 的 AD 族？已有 $\mathfrak b=\mathfrak s=\mathfrak c$ 下的构造。[5, Theorem 3.6; Q3.9]

**我的研究路线建议：**先用树分支式族保证 nowhere MAD，再检验能否针对任意有限块序列取得 FI 的中心化。但二者有张力：下述 R0 说明树编码也很容易产生非 FI 族。不能把“树分支天然 AD”错当作 FI 已经成立。删去两个基数不变量假设的全题不列为七天优先。

### A8

$$
\mathfrak c>\mathfrak a\ge\mathfrak s
\quad\Longrightarrow\quad
\exists\mathcal A\ (\mathcal A\text{ 是 MAD},\ |\mathcal A|=\mathfrak a,
\ \mathcal A\text{ 非 FI})?
$$

这是原文的精确问题。[5, Q4.10]

**我的研究路线建议：**下述 R0 提供规模 $\mathfrak s$ 的非 FI 初始族。剩余关键是能否选择适当初始族，使其有规模 $\mathfrak a$ 的 MAD 扩张，或直接对已有小 MAD 族作保规模改造。Zorn 引理只给某个极大扩张，不控制其规模；不能据此宣称 A8 已解。

## B1：观察项——SS 与 almost strongly separable 的存在性

对 $\mathcal A$，称有限非空集族 $X$ 正，如果对每个 $B\in\mathcal I(\mathcal A)$，存在 $s\in X$ 与 $B$ 不交。SS 要求每个正 $X$ 有无穷多个成员被某个 $B\in\mathcal I(\mathcal A)$ 包含；almost strongly separable 要求可以直接由某个 $a\in\mathcal A$ 包含。

最新正式版在 $\mathfrak b=\mathfrak c$ 下证明这两类无限 AD 族的存在性等价，问能否删除该假设。[7, Theorem 5.15; Q5.20]

**不是**要求同一个 SS 族已经具有更强性质。需要的方向是从某个 SS 族的存在推出某个更强族的存在。

**年代限制：**已核到 2025 年末在线发表的修订版明确列出此问，但未完成对其更早首次公开时间的认证。因此不能用正式版发表日期冒充问题出生日期，本题暂列观察项。

**我的研究路线建议：**现有构造里具体使用 $\mathfrak b=\mathfrak c$ 来同时最终控制先前产生的函数。可研究这些函数是否因 SS 结构而局部有界，或重新安排有限分组，避免同时支配整个先前函数族。这是较集中的缺口；倘若实际可编码任意无界函数族，原路线就需要更换。

## R0：对非 FI 最小规模问题的直接证明

原文 [5, Q4.9] 及后续 [6, Q11] 明确问最小规模是否为 $\mathfrak s$。以下论证在本次核查中得到。它按上述字面定义给出完整答案，但未完成作者核实和优先权检索，不宣称是首次证明。

### 命题

在 ZFC 中，

$$
\min\{|\mathcal A|:\mathcal A\text{ 是非 fin-intersecting 的 AD 族}\}=\mathfrak s.
$$

### 上界

取规模 $\mathfrak s$ 的分裂族 $\{S_\alpha:\alpha<\mathfrak s\}$，可假定每个 $S_\alpha$ 无限且余无限。由于 $\mathfrak s\le\mathfrak c$，选择两两不同的 $x_\alpha\in2^\omega$。

在可数集合 $T=2^{<\omega}$ 上令

$$
A_\alpha^0=\{x_\alpha\restriction n:n\in S_\alpha\},\qquad
A_\alpha^1=\{x_\alpha\restriction n:n\notin S_\alpha\},
$$

并设

$$
\mathcal A=\{A_\alpha^i:\alpha<\mathfrak s,\ i<2\}.
$$

每个成员无限。同一分支上的两半不交；不同分支只有有限多个共同初始段，因此不同成员的交均有限。于是 $\mathcal A$ 是规模 $\mathfrak s$ 的 AD 族。

取有限块 $C_n=2^n$。它们非空、有限，且因序列长度不同而两两不交。

任取无限 $I\subseteq\omega$。选 $S_\alpha$ 分裂 $I$。则

$$
\{n\in I:A_\alpha^0\cap C_n\ne\varnothing\}=I\cap S_\alpha,
$$

$$
\{n\in I:A_\alpha^1\cap C_n\ne\varnothing\}=I\setminus S_\alpha.
$$

两者都无限且不交。因此删去有限迹集后，剩下的族仍不中心。任意 $I$ 都失败，所以 $\mathcal A$ 非 FI。通过 $T$ 与 $\omega$ 的双射可把整个构造移到 $\omega$ 上。

### 下界

若 $|\mathcal A|<\mathfrak s$，给定任意 fin-sequence $C$，对每个 $a\in\mathcal A$ 定义

$$
Q_a=\{n:a\cap C_n\ne\varnothing\}.
$$

$\{Q_a:a\in\mathcal A\}$ 的规模小于 $\mathfrak s$，故存在一个无限 $I$ 不被其中任何集合分裂。因此每个 $I\cap Q_a$ 在 $I$ 中有限或余有限；删去有限者后，任意有限交仍在 $I$ 中余有限，故无限。这就是 FI。下界也见 [5, Theorem 3.1]。

上下界合并即得结论。

### 审计要点

1. $C_n=2^n$ 的块大小无统一上界，但 fin-sequence 定义没有要求统一有界。
2. 构造的是 AD，不是 MAD；不要把二者混用。
3. 这是对原问题字面定义的答案，不自动回答保规模的 MAD 扩张问题 A8。
4. 数学论证与历史新颖性是两件事；短论证可能已有未检到的记录。

## 七天研究预算排序

以下等级是相对选题优先级，不是具有统计校准的成功率；“局部推进”不计作“完全解决”。

| 顺位 | 项目 | 一周内完整解决的评估 | 原因与验收标准 |
|---|---|---|---|
| 先行复核 | R0 | 已有完整短论证，不再是猜测是否能解 | 逐项核对定义、证明及文献优先权；不能包装为已认证新定理 |
| 1 | A1 | 有实际尝试价值；仍属中低把握 | 有界宽度到有界深度的差距具体；必须取得不依赖宽度的补全机制 |
| 条件优先 | B1 | 年代核查通过后，可与 A1 同列优先 | 已知证明中一个全局支配步骤可精确定位；但该障碍可能本质 |
| 2 | A2 的 K₄ 部分 | 中低把握；适合作为备选 | 目标有限、分支形状可分析；需要无限实现，不只是有限枚举 |
| 3 | A3 | 偏低 | 可尝试统一图变换；主要风险是破坏下邻居的梯状性 |
| 4 | A8 | 偏低 | R0 解决非 FI 初始族，但规模受控的极大化仍是独立缺口 |
| 5 | A4 | 偏低，不优先押整周 | 无三角形与针对所有顶点颜色函数的极大性须同时实现 |
| 6 | A7 | 低；局部改进更现实 | 要同时组织 nowhere MAD 和任意有限块序列的中心化 |
| 7 | A5 | 全参数版本低 | 共尾数阈值与分块大小相互作用；应先攻首个越界参数区间 |
| 8 | A6 | 任意无限基数版本低 | 保高二色数的缩小构造需要新的见证/反映机制 |

我的最终选择：先完成 R0 的独立复核，然后将主要研究预算投入 A1；A2 为备选。B1 在满足年代条件之后才进入正式优先队列。不建议同时启动八个证明项目。

可执行的阶段验收方式是：开始阶段重建相邻正面定理，明确唯一或少数关键缺口；中段只推进一个主要引理并同时寻找反例；后段逐项查量词、极限步骤和参数边界。七天结束时只接受完整证明、完整反例或明确标注的局部定理，不把更强的中间猜想当作进度。

## 被排除与未录入的材料

- “奇异基数的后继能否为 Jónsson”是新综述讨论的老问题，不因 2026 年发表而重置年龄。[8]
- Club guessing toolbox I 重述的 Shelah 问题可追溯到 2000 年，不按 2022 年预印本日期计龄。[9]
- [2, P5.8] 的 Erdős 老问题有 1988 年工作背景，排除。
- [1, Q6.2] 直接询问加一个 Cohen 实数后的模型结论；[10, Q2.31] 是关于 Souslin 树消失层的相容性问题；本次按用户的领域收窄口径，不纳入。
- [2, P5.5] 直接加入 continuous/Borel 条件及强迫公理，未作为纯组合目标推荐。
- [3] 的引言说明解决了此前强染色 over partitions 的若干问题，不能照旧清单把已解决条目重复收录。
- [8] 关于 $U$ 原理与满射负分割关系的一项细分问题虽很相关，但最早提出时间尚未核定，不因新综述而认证为新题。
- Proxy principles 综述也作为术语和路线背景核查，没有把整套研究纲领当作可在一周内解决的单个问题。[11]

## 参考文献及可核查入口

[1] Chris Lambie-Hanson, Dávid Uhrik. *Hajnal–Máté graphs, Cohen reals, and disjoint type guessing*. arXiv:2312.01828，首版 2023-12-04；Mathematika 70 (2024), e12261. https://arxiv.org/abs/2312.01828 ; 全文 https://arxiv.org/html/2312.01828v1

[2] Chris Lambie-Hanson, Dániel T. Soukup. *Extremal triangle-free and odd-cycle-free colourings of uncountable graphs*. arXiv:2002.02480，首版 2020-02-06；Acta Mathematica Hungarica 163 (2021), 174–193. https://arxiv.org/abs/2002.02480 ; https://arxiv.org/html/2002.02480

[3] Menachem Kojman, Assaf Rinot, Juris Steprāns. *Ramsey theory over partitions II: Negative Ramsey relations and pump-up theorems*. arXiv:2204.14101，首版 2022-04-29；Israel Journal of Mathematics 261 (2024), 223–247. https://arxiv.org/abs/2204.14101 ; https://arxiv.org/html/2204.14101

[4] Attila Joó. *Uncountable dichromatic number without short directed cycles*. arXiv:1905.00782，首版 2019-05-02；Journal of Graph Theory 94 (2020), 113–116. https://arxiv.org/abs/1905.00782 ; https://arxiv.org/html/1905.00782

[5] César Corral, Vinicius de O. Rodrigues. *Fin-intersecting MAD families*. arXiv:2212.01484，首版 2022-12-02、修订 2023-04-25；Filomat 38:7 (2024), 2563–2578. 本记录采用正式版问题编号。https://arxiv.org/abs/2212.01484 ; 正式版 https://www.pmf.ni.ac.rs/filomat-content/2024/38-7/38-7-25-20080.pdf

[6] César Corral, Vinicius de O. Rodrigues. *New examples of MAD families with pseudocompact hyperspaces*. arXiv:2309.03405；Topology and its Applications 342 (2024), 108773. https://arxiv.org/abs/2309.03405 ; https://arxiv.org/html/2309.03405v2

[7] Jörg Brendle, Osvaldo Guzmán-González, Michael Hrušák, Dilip Raghavan. *Combinatorial properties of MAD families*. arXiv:2206.14936（2022 首版）；本记录采用 Canadian Journal of Mathematics 的修订正式版，2025-12-03 在线发表，DOI 10.4153/S0008414X25101879。Q5.20 最早提出时间待进一步核定。https://arxiv.org/abs/2206.14936 ; 作者保存的正式版 https://www.matmor.unam.mx/~oguzman/Combinatorics%20of%20MAD%20families.pdf

[8] Assaf Rinot. *May the successor of a singular cardinal be Jónsson?* Bollettino dell'Unione Matematica Italiana，2026-01-07 在线发表。https://link.springer.com/article/10.1007/s40574-025-00525-z

[9] Tanmay Inamdar, Assaf Rinot. *A club guessing toolbox I*. arXiv:2207.03969；Bulletin of Symbolic Logic 30 (2024), 303–361. https://arxiv.org/abs/2207.03969 ; https://arxiv.org/html/2207.03969

[10] Assaf Rinot, Shira Yadai, Zhixing You. *The vanishing levels of a tree*. arXiv:2309.03821. https://arxiv.org/abs/2309.03821 ; https://arxiv.org/html/2309.03821

[11] Ari Meir Brodsky, Assaf Rinot, Shira Yadai. *Proxy principles in combinatorial set theory*. arXiv:2403.14815. https://arxiv.org/abs/2403.14815 ; https://arxiv.org/html/2403.14815v2
