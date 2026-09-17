# 本库的后续维护约定

- 公开文档只介绍基础库和已授权收录的形式化项目。用户提供的本地题目集、题号映射、研究优先级和内部计划不得自动进入公开文档或源码包。
- 根 README 只保留基础库说明及 `Formalizations/` 总入口；具体项目的结论、来源和证明导航放在该项目子目录。文档打包使用明确文件清单，新增公开文档时逐项审查。

- 使用 Lean 4.30.0 与本库锁定的 mathlib；常规任务不自动升级工具链。
- 基础工具使用 `InfinitaryCombinatorics` namespace 并加入 `InfinitaryCombinatorics.lean`；问题形式化放入 `Formalizations/<项目名>/`，使用 `InfinitaryCombinatorics.Formalizations.<项目名>` namespace 并加入 `Formalizations.lean`。基础库不反向导入应用层。
- `R0/` 为有来源哈希的兼容快照。常规扩展写新模块；需要改变旧定义时先给出明确的迁移/等价说明。
- 文献问题的存在性目标只能作为命题或明确假设出现，不得添加为公理。不得以有限/可数近似替换不可数目标，或把约束性结论写成无条件结论。
- 保留不同顶点、不同块、族的规模、块序型、正则性、共尾数和 universe/lift 条件。
- 修改完成后运行 `./verify.ps1`；实际核对 `verification/manifest.json` 的时间与源哈希，不引用旧日志证明当前成功。
- 交付说明区分已证工具、已定义接口和未解决的研究步骤；新增文件须经过总入口覆盖和完整公理审计。
