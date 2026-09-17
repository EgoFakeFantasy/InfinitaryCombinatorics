# 来源与可复现性

- 基础库模块由 Codex 编写与整合；`CountableSplitting.lean` 由 WorkBuddy 协作完成，Codex 复核并纳入统一构建与公理审计。相关可数 FI 与基数界推论位于 `Characteristics.lean`。
- 各具体形式化项目的数学来源、作者说明、主定理和证明导航保存在对应的 [Formalizations/](../Formalizations/README.md) 子目录。
- Mathlib 使用 `v4.30.0`，commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`。依赖源码保留其自身的版权与许可证，未纳入本库源码包。

按 `lean-toolchain` 和 `lake-manifest.json` 安装锁定依赖，运行 `./verify.ps1` 可复现构建、陈述检查及公理审计。检查时间和源文件哈希保存在 `verification/manifest.json`。

验收记录来自本地 Lean 内核检查，不代表 GitHub Actions 的运行结果。公开文档和源码包只包含基础库及已收录形式化项目的材料。
