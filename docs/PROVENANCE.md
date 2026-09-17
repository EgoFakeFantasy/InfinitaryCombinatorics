# 来源与可复现性

- 需求来源：用户提供的 `infinitary_combinatorics_problem_register_2026-09-.md`，原样保存为 `problem-register.md`。
- Lean 新增模块：Codex 编写主体；`CountableSplitting.lean` 由 WorkBuddy 通过 Agent 广场 task 16 协作，Codex 复核并纳入统一构建/公理审计。可数 FI 与基数界推论由 Codex 在 `Characteristics.lean` 接入。
- `R0.lean` 与 `R0/*.lean`：逐字复制自相邻的 `work/r0-formalization`，未改原工程。副本各文件 SHA-256 见 `r0-source-hashes.json`，复现脚本检查一致性。R0 原工程说明其候选论证及形式化由 GPT-6 Astra 生成，不主张历史首次性或独立人类审查。
- R0 数学来源包括 Corral–Rodrigues, *Fin-intersecting MAD families*, Filomat 38(7) (2024), 2563–2578，尤其 Definition 2.3、Theorem 3.1、Proposition 4.8、Question 4.9。完整出处保留在问题登记表；R0 结果的当前内核证据在 `CheckR0.lean` 和 `verification/`。
- Mathlib：`v4.30.0`，commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`，依赖源码保留其自身的版权与许可证。未将依赖源码打入交付压缩包。

本机 `.lake/packages` 联接到现有缓存，仅用于节省下载/编译。源包不含该联接；在其他机器按 `lean-toolchain` 和 `lake-manifest.json` 安装依赖即可。最终检查的来源哈希和时间保存在 `verification/manifest.json`。公开仓库为 [EgoFakeFantasy/InfinitaryCombinatorics](https://github.com/EgoFakeFantasy/InfinitaryCombinatorics)。验收记录来自本地 Lean 内核检查，不代表 GitHub Actions 的运行结果。

