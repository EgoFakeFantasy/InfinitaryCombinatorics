# 基于本库的无穷组合问题形式化

本目录专门收录基于本仓库的基础工具、定义和已证定理完成的无穷组合相关问题形式化。每个问题使用独立子目录，提供可编译入口、数学陈述、来源说明和验收方法。

## 已收录项目

| 项目 | 数学内容 | Lean 入口 | 状态 |
| --- | --- | --- | --- |
| [R0](R0/README.md) | 非 fin-intersecting 无限 AD 族的最小规模等于分裂数 s，且在自然数上达到 | [Formalizations.R0.Main](R0/Main.lean) | 完整证明；复用本库保留的 R0 实现；纳入统一构建与公理审计 |

R0 的原始本地证明先于基础库完成，其定义和引理随后纳入本库。本条目是该证明在本库中的应用入口，不表示重新证明了一个新的数学结果。

## 使用与验证

```lean
import Formalizations.R0.Main
-- 导入全部已收录项目时可使用 import Formalizations
open InfinitaryCombinatorics.Formalizations.R0
```

在仓库根目录运行：

```text
lake build
lake env lean CheckFormalizations.lean
lake env lean Audit.lean
```

Windows 可运行 `./verify.ps1` 完成统一验收。当前证据见 [验收清单](../verification/manifest.json)、[应用陈述检查](../verification/formalizations-statements.log) 和 [公理审计](../verification/axiom-audit.log)。这些是本地 Lean 内核检查记录。

## 后续贡献

每个问题放入 `Formalizations/<项目名>/`，至少包含 `README.md` 和一个 Lean 入口；README 写明主定理、所有附加假设、使用的基础库模块、来源与尚未形式化的部分。

通用工具放在 `InfinitaryCombinatorics/`，问题专属证明放在本目录。声明使用 `InfinitaryCombinatorics.Formalizations.<项目名>` namespace，并在根目录 `Formalizations.lean` 加入入口 import。基础库不反向导入应用项目，以免形成依赖循环。

贡献需接入 `CheckFormalizations.lean` 的语义陈述检查与 `Audit.lean` 的必需声明清单，运行完整构建、源码缺口扫描和传递公理审计。允许的公理依赖为 `propext`、`Classical.choice`、`Quot.sound`；不能将研究目标作为额外公理加入。文献优先权、数学意义与 Lean 内核通过是不同的证据，应分别说明。
