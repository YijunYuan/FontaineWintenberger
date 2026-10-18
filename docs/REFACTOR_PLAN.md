# FontaineWintenberger 重构方案（v2，全部定稿）

> 状态：A–F 全部与作者讨论定稿（2026-10-17/18）。执行按 §F 分阶段进行，每阶段一个分支。
> 讨论顺序建议：A（全局设计）→ B（目录）→ C（命名）→ D（文档）→ E（工程）→ F（执行顺序）。
>
> 范围 = instruction.pdf §1 的五个目标：
> (1) APF / strict APF 的定义（Wintenberger 1.2.1）
> (2) field of norms X_K(L) 的定义（2.1.1）
> (3) Thm 2.1.3：X_K(L) 是特征 p 的完备离散赋值域，剩余域 = k_L
> (4) 函子性：Thm 3.1.2；Cor 3.2.3（Gal(K^sep/L) ≅ Gal(X^sep/X_K(L))）
> (5) Rem 3.2.4：L/K Galois 时 Gal(L/K) 作用于 X_K(L)，诱导 G_K 的作用

---

## 0. 现状数据

| 指标 | 数值 |
|---|---|
| Lean 文件数 | 228（+ 根文件） |
| 总行数 | 44 460 |
| theorem / def 数 | 1 922 / 317 |
| `letI` / `let :` 局部实例安装 | 1 445 / 1 761（合计 3 206 处） |
| 定理**陈述**里含 `letI` 的声明 | > 150 |
| `omit [...] in` | 159 |
| `(R := …)` 显式传环参数（Ramification） | 610 |
| 全量编译总 CPU 时间 | 116 min |
| 编译 > 60 s 的文件 | 8 个（最慢 1 545 s） |
| 编译 > 20 s 的文件 | 24 个 |
| 文档填充词 "actual" / "original" | 1 641 / 1 458 次 |
| 引用 Serre / Wintenberger 章节号的文件 | 2 / 0 |
| 项目内从未被引用的声明（Ramification 抽样） | 96 / 646 |
| `sorry` | 0 |
| 根文件未直接导入的模块 | 25 |
| blueprint 的 `\lean{}` 宏 | 是空宏（没有 leanblueprint），从未被机器校验 |

最慢文件全部是 `FieldOfNorms/NormUnion*`：

| 文件 | 行数 | 秒 |
|---|---|---|
| NormUnionGaloisEquiv | 180 | 1545 |
| NormUnionAbsoluteAction | 354 | 1358 |
| NormUnionGaloisRestrictionFun | 52 | 746 |
| NormUnionGaloisAction | 155 | 726 |
| NormUnionGaloisIsomorphism | 314 | 457 |
| NormUnionAbsoluteStages | 262 | 386 |
| SeparableClosedUnion | 438 | 75 |
| Ramification/EmbeddingComparison | 1238 | 64 |

52 行的文件编译 746 s，说明慢的不是证明，而是**签名**：每个声明的类型里要重新 elaborate 十几个 `letI`（`Field (DirectLimit …)` 由 `inferInstanceAs` 现场重算、`Field (NormLimit K N.val)` 对每个 stage 重建、`CommRing.ofMinimalAxioms` 展开等）。详见 A6。

---

## A. 全局设计决策（影响全局，先讨论）

### A1. 基域假设束 → 一个 class　【已定稿 2026-10-17】

**现状**：下面这串在 ~166 个文件里重复 284 次，拼法有 10 种变体，`PerfectField` 又另起一行，`p` 和 `[CharP 𝓀 p]` 再显式穿过 124 个声明：
```lean
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField …) p]
```
另外还有第二套 `Valued K Γ + IsRankOneDiscrete` 表述，4 个 section 只为在两套之间搬运。

**决定**：
1. 保留 normed 表述（谱范数 / `IsKrasner` 等 Mathlib API 都是 normed 的）；`Valued` 表述只留一个入口 `IsCompleteDiscreteValuedField.ofValued`，删除搬运层（`CompatibleNorm`、`NewtonValuation`、`KrasnerValuation` 后半、`SeparableRootExtraction` 后半）。
2. 两层 Prop class，名字写全：
```lean
open scoped NormedField Valued NNReal   -- 每个用到基域的文件都要 open

/-- 非阿基米德完备离散赋值域（normed 表述）。 -/
class IsCompleteDiscreteValuedField (K : Type*) [NontriviallyNormedField K] : Prop
    extends IsUltrametricDist K, CompleteSpace K, IsDiscreteValuationRing 𝒪[K]

/-- Wintenberger 开篇约定的 "corps local"：完备 DVF，剩余域完美且特征 p > 0。
与 Mathlib 的 `IsNonarchimedeanLocalField` 不同，不要求剩余域有限。 -/
class IsPerfectResidueLocalField (K : Type*) [NontriviallyNormedField K] : Prop
    extends IsCompleteDiscreteValuedField K, PerfectField 𝓀[K] where
  residueChar_prime : (ringChar 𝓀[K]).Prime

noncomputable abbrev residueChar (K) [NontriviallyNormedField K] [IsPerfectResidueLocalField K] : ℕ :=
  ringChar 𝓀[K]
instance : Fact (residueChar K).Prime     -- CharP 𝓀[K] (residueChar K) 随之自动成立
```
3. `p` 不再是参数：全部写成 `residueChar K`。这是 A4 把 `Field (FieldOfNorms K L)` 做成 instance 的前提（`p` 无法由目标类型推出）。
4. 整数环与剩余域直接复用 Mathlib 记号 `𝒪[K]`、`𝓀[K]`（来自 `Valued.integer` / `Valued.ResidueField`，通过 scoped instance `NormedField.toValued : Valued K ℝ≥0`）。**实测**（pinned Mathlib）：`𝒪[K]` 与现有 `(NormedField.valuation K).valuationSubring` 作为类型和作为 Subring 都 `rfl`；`𝓀[K]` 同样 `rfl`；`Valued.toUniformSpace = PseudoMetricSpace.toUniformSpace` 是 `rfl`，拓扑也是，无 diamond；`Valued.v x = ‖x‖₊` 是 `rfl`。有限扩张上装谱范数后 `Valued.v x = spectralValuation K L x` 也 `rfl`，因此 A4 阶段可用 `𝒪[L]` 取代 `spectralIntegerRing K L`（841 处）。
   - 注意点：`NormedField.toValued` 在 Mathlib 是 scoped（防止与 `Valued.toNormedField` 循环）。在 `LocalField/Basic.lean` 里于项目命名空间下重新声明为 scoped instance，并在文档说明。
   - 值群：基域 `Valued K ℝ≥0`，field of norms 用 `Valued X ℤᵐ⁰`，互不冲突。

**执行（F1）**：新建 `LocalField/Basic.lean`；脚本把 10 种 variable 头统一为 `[NontriviallyNormedField K] [IsPerfectResidueLocalField K]` 或 `[IsCompleteDiscreteValuedField K]`（按文件是否用到完美性）；`p` → `residueChar K`，删 `(p : ℕ) [Fact p.Prime] [CharP …]`；`IsLocalRing.ResidueField (…).valuationSubring` → `𝓀[K]`，`(…).valuationSubring` → `𝒪[K]`；删 Valued 搬运层（注意 Mathlib 的 `Valuation.RankOne` 是数据而非 Prop，`ofValued` 入口需显式带底数 `e > 1`；原型 `/tmp/fwscratch/Basic.lean` 已验证类定义编译）。谱范数在有限扩张上的 scoped instance 文件 `LocalField/Spectral/Instances.lean`（`[IsCompleteDiscreteValuedField K] [FiniteDimensional K L] → NontriviallyNormedField L, NormedAlgebra K L, IsCompleteDiscreteValuedField L`）同期加入。

### A2. `IsAPF` / `IsStrictlyAPF` 改为 class　【已定稿 2026-10-17】

**现状**：三个 Prop `def`（`IsAPFSubextension`、`IsAPF`、`IsStrictlyAPF`），`hL : IsAPF K L` 作为显式参数出现在 269 个定理和 35 个 def 里；`isAPF_of_finite K M` 手写 53 次；`IsAPF.foo K L hL` 调用 93 处（点记号用不了）。`IsAPF` 进入数据定义（`apfPhi K L hL u`、`normLimitField K L p hL hInfinite`），是全局 `letI` 的根源之一。绝对 Galois 群手写为 `SeparableClosure K ≃ₐ[K] SeparableClosure K`（77 处）。

**决定**：
1. **Galois 群的写法（方案 A）**：
   - 内部统一用 Mathlib 记号 `Gal(SeparableClosure K/K)`（`Mathlib/FieldTheory/Galois/Notation.lean` 的宏）。
   - 对外（绝对上分歧群 `G_K^u`、Cor 3.2.3、Rem 3.2.4、`Main.lean`）用 Mathlib 的 `Field.absoluteGaloisGroup K`。
   - 在 `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`（上游暂存）补桥：`Field.absoluteGaloisGroup.toSep : absoluteGaloisGroup K ≃ₜ* Gal(SeparableClosure K/K)`（限制映射；`≃*` 与正向连续已验证 40 行；反向连续用 Frobenius 幂论证）及推论 `instance : CompactSpace (absoluteGaloisGroup K)`。
   - 为什么内部不能直接用 `G_K`：Mathlib 无限 Galois 理论的 19 条引理（`fixingSubgroup_isClosed`、`isOpen_iff_finite`、`CompactSpace Gal(K/k)`…）全部要求 `[IsGalois k K]`，而 `K^alg/K` 仅当 K 完美时是 Galois；Wintenberger 允许 K 不完美（如 `F_p((t))`）。数学上 `Aut_K(K^sep) ≅ Aut_K(K^alg)` 是典范同胚（`K^alg/K^sep` 纯不可分），差别只在 Galois 对应而非群。
2. **`IsAPF` 字段**（写法 (a)，对所有嵌入量化；`IsAPFSubextension` 删除，它是 `IsAPF K E` 对 `E : IntermediateField K (SeparableClosure K)` 的特例）：
```lean
/-- Wintenberger 1.2.1：对所有 `u ≥ -1`，`G_K^u · G_L` 在 `G_K` 中开。 -/
class IsAPF (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L] : Prop where
  isOpen_sup (i : L →ₐ[K] SeparableClosure K) (u : ℝ) (hu : -1 ≤ u) :
    IsOpen (apfSubgroup K i.fieldRange u : Set Gal(SeparableClosure K/K))

theorem isAPF_iff_absoluteGaloisGroup : IsAPF K L ↔ ∀ u ≥ -1, IsOpen ((… ).comap toSep : Set (absoluteGaloisGroup K))
```
3. **`IsStrictlyAPF`**（保留此名）：
```lean
class IsStrictlyAPF (K L) … : Prop extends IsAPF K L where
  liminf_pos : 0 < Filter.liminf (apfStrictnessRatio K L) Filter.atTop
```
4. **做成 instance 的**（对 `IsAPF` 与 `IsStrictlyAPF` 各一份）：
```lean
instance [FiniteDimensional K L] : IsAPF K L                                          -- 1.2.2
instance [IsAPF K L] (E : IntermediateField K L) : IsAPF K E                          -- 1.2.3(iii)
instance [IsAPF K L] (M : IntermediateField K L) [FiniteDimensional K M] : IsAPF M L  -- 1.2.3(i) 正向；依赖 A1 的谱范数 scoped instance
```
   保持为 iff 定理 + `haveI`（目标中缺域，instance search 无从下手）：`IsAPF K N ↔ IsAPF M N`（M/K 有限，反向）；`IsAPF K L ↔ IsAPF K N`（N/L 有限、N 抽象域）；`IsAPF K i.fieldRange` 对变动嵌入；`isAPF_algEquiv`。
5. **依赖 `hL` 的 6 个数据定义**：`apfPhi`、`apfHerbrandOrderIso`、`apfHerbrandERealOrderIso` → `[IsAPF K L]`。`apfMaximalUnramified`、`apfMaximalTame`（现 `.choose`）→ 显式构造 `K_0 := (apfFiniteStage … 0).comap …`、`K_1` 同理，作为 `IntermediateField K L`，不依赖 APF；`[IsAPF K L] → FiniteDimensional K K_0` 作为 instance。`apfMaximalUnramifiedResidueEquiv` 随之改。
6. **命名空间**：以 `apfPsi`/`apfPhi`/`apfIndex` 为主语的引理放根空间（`strictMono_apfPsi`），`IsAPF.` 前缀只留给关于 APF 性质本身的引理（`IsAPF.of_algHom`、`IsAPF.fieldRange`）。

### A3. "L/K 无限"假设　【已定稿 2026-10-17】

**现状**：`hInfinite : ¬ Module.Finite K L` 显式出现 109 次，进入 40 个 def；"无限 + 有限扩张仍无限"重复证明 9 次。数学上只在一处用到：无限时分歧发散使 `p = 0`，从而得到负元与特征 p（Thm 2.1.3(ii)）。

**决定**：不新建 class，用 Mathlib 的 `Fact` 包裹：
```lean
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]
instance : Field (FieldOfNorms K L)           -- 需要上述两个 instance

-- 推导实例，放 FieldOfNorms/FiniteIntermediateField.lean
instance [Fact (¬ Module.Finite K L)] (N : IntermediateField L M) [FiniteDimensional L N] :
    Fact (¬ Module.Finite K N)
-- 沿 ≃ₐ 搬运只给定理，需要时 haveI
```
理由：`Fact` 正是 Mathlib 对"需作 instance 传递但不值得起名"的命题的惯用法（`Fact p.Prime`）；命题本身已众所周知；推导实例写法与 `Fact (1 < p) ← Fact p.Prime` 相同；不会与将来 Mathlib 可能加入的谓词撞名。放弃的备选：(b) 让 `Field` 只需 `[IsAPF]`（要多证有限情形 ≈200 行且无用）；(c) `IsInfiniteAPF` 合并类（把正交性质绑死，并与 `IsStrictlyAPF` 形成菱形）。

### A4. `FieldOfNorms K L` 作为带实例的类型　【已定稿 2026-10-17】

**现状**：`NormLimit K L := WithZero (normLimitGroup K L)` 是 `abbrev`；`Field`、`Valued`、`CommSemiring`、`AddCommMonoid`、`MulSemiringAction` 都是带 `p hL hInfinite` 的 `@[instance_reducible] def`，下游 `letI := normLimitField …` 655 处；`SeparableNormUnion` 的 `Field` 是 `abbrev … := by letI (N) …; exact inferInstanceAs (Field (DirectLimit …))`，每次使用重新综合（NormUnion* 文件慢的直接原因）。

**决定**：
1. **载体用 `def`，不用 `abbrev`**：
```lean
/-- Wintenberger 2.1.1：范数相容的单位族，附加 0。 -/
def FieldOfNorms (K L : Type*) [...] : Type _ := WithZero (normCompatibleUnits K L)
instance : CommGroupWithZero (FieldOfNorms K L) := inferInstanceAs (CommGroupWithZero (WithZero _))  -- 无条件
```
   `Field` 实例在 term mode 下写成 `{ (inferInstance : CommGroupWithZero _) with add := …, … }`，使 `Field.toCommGroupWithZero` 与原实例按结构 η `rfl`；A6 的 diamond（66 处 `letI : Mul U := ….toMul`、`normLimitField_toCommGroupWithZero` 见证引理）随之消失。
2. **实例清单**（现为 def/定理者全部改 instance；`[IsAPF K L] [Fact (¬ Module.Finite K L)]` 为标准前提）：`Field`、`CharP _ (residueChar K)`、`Valued _ ℤᵐ⁰`、`Valuation.IsRankOneDiscrete Valued.v`、`IsDiscreteValuationRing 𝒪[X]`、`CompleteSpace`、`PerfectField 𝓀[X]`、`CharP 𝓀[X] (residueChar K)`、`MulSemiringAction Gal(L/K) (FieldOfNorms K L)` + `ContinuousConstSMul`。
3. **`RelFieldOfNorms K L M := DirectLimit (fun N : FiniteIntermediateField L M => FieldOfNorms K N) …`**（X_{L/K}(M)，3.2.1）同为 `def`；实例 `Field`、`Algebra (FieldOfNorms K L) _`、`[IsSepClosure L Ω] → IsSepClosure (FieldOfNorms K L) (RelFieldOfNorms K L Ω)`。各 stage 有全局 `Field` 后，`DirectLimit` 的 `Field` 直接 `inferInstance`。
4. **X 作为局部域**：X 上的主结构是全局 `Valued X ℤᵐ⁰`。`NontriviallyNormedField X`（经 `Valued.toNontriviallyNormedField`，实测其 `toUniformSpace := Valued.toUniformSpace`，拓扑 defeq）与 `IsPerfectResidueLocalField X` 做成 **scoped instance**，放 `FieldOfNorms/Structure/LocalField.lean`，需要时 `open scoped FieldOfNorms.LocalField`。原因：若全局提供，则在 `open scoped NormedField` 的文件里 `𝒪[X]` 可能解析到 `Valued X ℝ≥0`，与 `ℤᵐ⁰` 版只命题相等不 defeq。与 Mathlib 自己对 `Valued.toNormedField` 的 scoped 处理一致。本项目内部不需开启；供 FalseTate 后续项目使用。
5. 删 `@[simp] normLimitField_add`（把 `+` 改写成内部运算）；39 条带 `letI` 的 simp 引理随 A2–A4 消失。范畴层去留见 B。

### A5. 复用 Mathlib（不限于绝对 Galois 群）　【已定稿 2026-10-17】

| 项目里的东西 | Mathlib 已有 | 处理 |
|---|---|---|
| `SeparableClosure K ≃ₐ[K] SeparableClosure K`（手写 77 处，无名字） | `Field.absoluteGaloisGroup K`（= `Aut(K^alg/K)`，带 Krull 拓扑） | 新增 `absoluteGaloisGroupEquivSep : G_K ≃* Gal(K^sep/K)`（连续；**原型 40 行已编译通过**，用 `restrictNormalHom_surjective` + `separableClosure.isPurelyInseparable`）。最终定理（Cor 3.2.3、Rem 3.2.4、绝对上分歧群）用 `Field.absoluteGaloisGroup` 陈述；内部仍以 `SeparableClosure K` 为环境域（因为 Mathlib 的无限 Galois 对应要求 `IsGalois`，而 K 不完美时 `K^alg/K` 不是 Galois）。给 `Gal(K^sep/K)` 一个 scoped notation。 |
| `LocalField/Krasner.lean` 的 `krasner_mem_adjoin` | `IsKrasner`, `IsKrasner.of_completeSpace` | 删包装，直接用 |
| `local_ramificationIdx_tower`, `local_inertiaDeg_eq_finrank_residueField`, `localResidue_normal` | `Ideal.ramificationIdx_tower`, `Ideal.inertiaDeg_eq_of_isMaximal`, `Ideal.Quotient.normal` | 删包装 |
| `card_lowerRamificationGroup_zero`, `InertiaFixedField.lean` | `Ideal.card_inertia_eq_ramificationIdxIn`, `IsInertiaField` | 改为直接应用 |
| `differentIdeal_eq_span_derivative_of_adjoin_eq_top`, `trace_integral_iff_le_codifferent` | `conductor_mul_differentIdeal`, `aeval_derivative_mem_differentIdeal`, `traceDual` API | 对接 |
| `herbrandOrderIso` | `StrictMonoOn.orderIsoOfSurjective` | 用之 |
| `upperRamificationEquivToLimit` | `InfiniteGalois.mulEquivToLimit` | 对齐 |
| `IntermediateField.fixedField_isGaloisGroup` | `IsGaloisGroup.subgroup` / `of_fixedPoints_eq` | 删 |
| `nonempty_separablyClosed_embeddings`, `exists_aut_extends_*` | `IsSepClosed.lift`, `AlgHom.liftNormal` | 删 |
| `IntermediateField.completeSpace_of_finiteDimensional` | `FiniteDimensional.complete` | 删 |
| `[IsDiscreteValuationRing val.v.valuationSubring]` 与 `[IsRankOneDiscrete val.v]` 并列 | `Valuation.valuationSubring_isDiscreteValuationRing` 实例 | 删冗余 binder |
| `residueTeichmuller` | `Perfection.teichmuller₀` 的特化 | 保留但改为薄包装 |
| `continuous_powerSeries_subst` | `MvPowerSeries.continuous_subst` | 派生 |
| `normLimitUniformizer_isUniformizer` 等 | `Valuation.IsUniformizer`, `Valuation.Uniformizer` | 用 Mathlib 谓词 |
| `finiteGaloisNormalClosure` | `FiniteGaloisIntermediateField.adjoin` | 对齐 |

**反方向：项目里属于 Mathlib 层的通用引理**（新建 `FontaineWintenberger/Mathlib/`，按 Mathlib 命名，不得 import 项目其他目录；日后可整体 PR 上游）：Newton–Hensel 非单位导数版（`NewtonLifting`，还带着 Mathlib 的版权头）、Henselian DVR 有限扩张的单生成性（`IntegralGenerator`）、`Polynomial.discr_map` / `sq_sub_dvd_discr`、`Algebra.norm` 的基变换、线性无交的 minpoly 判据、`isAdicComplete_of_isNilpotent_ideal`、等特征 Cohen 同构 `k⟦X⟧ ≃+* R`、子群指数引理（`GroupTheory/*`）、`fixingSubgroup_relIndex_eq_finrank`、`finiteGaloisMap/Lift`、`G_K ≃ Gal(K^sep/K)`。


**决定**：
1. 新建 `FontaineWintenberger/Mathlib/`，目录镜像 Mathlib，Mathlib 命名空间与命名规范，零项目依赖，文件头注明 "upstream candidate"。候选见上段；另加 `absoluteGaloisGroup.toSep`、`Valued.completeSpace_of_completeSpace_valuationSubring`、`SequentialInverseLimit`、`residueTeichmuller`（`Perfection.teichmuller₀` 薄包装）。
2. 上表 15 项包装删除、改用 Mathlib。
3. `spectralIntegerRing K L`（841 处）→ `𝒪[L]`：依赖 A1 的 scoped 谱范数实例文件（`[IsCompleteDiscreteValuedField K] [Algebra.IsAlgebraic K L]` ⇒ `NontriviallyNormedField L`、`NormedAlgebra K L`，有限时 `IsCompleteDiscreteValuedField L`）。`spectralIntegerInclusion`/`spectralResidueInclusion` 改为 `Valuation.HasExtension` 下的通用映射。顺带消除 A6 第 6 条"整数环两种模型"。`WildTower`、`Subgroup` 两个让 L 自带范数的文件改为只用谱范数版，避免 diamond。

### A6. 性能：根因与修法　【已定稿 2026-10-17：红线 < 60 s/文件（目标 < 20 s），全量 < 25 min；F5 逐文件 `timeout 120` 构建，超时即改设计；动刀前先在 `separableNormUnionAbsoluteMap_of`、`normUnionGaloisRestrictionFun_base`、`normUnionGaloisRelativeHom` 上用 `trace.profiler`/`diagnostics` 确认诊断】

根因（按影响排序；来自读码 + 构建日志，尚未用 profiler 实测，重构前先在三个代表声明上开 `trace.profiler` / `diagnostics` 确认）：
1. **实例是 def 不是 instance**（A2/A4）：每个声明签名里 10–15 行 `letI`，Lean 对每条都重新 elaborate 并检查 defeq。`separableNormUnionField` 是 `abbrev` + `inferInstanceAs (Field (DirectLimit …))`，每次使用重新综合。
2. **实例 diamond**：`NormLimit` 是 `abbrev … := WithZero …`，于是全局有一个 `CommGroupWithZero` 的 `Mul`；`SeparableNormUnion` 是 `abbrev … := DirectLimit …`，Mathlib 的 `DirectLimit` 实例用的是这个 `WithZero` 乘法；而 `normLimitField` 派生的 `Mul` 要通过展开 `CommRing.ofMinimalAxioms` + 匿名结构合并才能和它对上。代码里的证据：`letI : Mul U := (separableNormUnionField …).toMul`（66 处）、`@CommSemiring.toSemiring U (@Semifield.toCommSemiring U (@Field.toSemifield U …))`（手写投影链）、`normLimitField_toCommGroupWithZero … := rfl`（专门用来见证 diamond 的引理）。
3. **具体化的 `Ω = SeparableClosure K`**：六个最慢文件都把 `L : IntermediateField K (SeparableClosure K)` 和 `FiniteLayer L (SeparableClosure K)` 写死；`NormLimit K ↥N.val` 到 `AlgebraicClosure K`（`MvPolynomial` 的商）有五层子类型强制。对照：做同样代数但用泛型 `Ω`/`M` 的文件（`NormUnionKrull` 17 s、`NormUnionAutomorphisms` 2.6 s、`NormUnionAbsoluteGalois` 5 s）都快。
4. **同一签名的"pin"不一致**：`NormUnionGaloisRestrictionFun`（52 行，746 s）的陈述没加 `Mul U`/`Add U` pin，证明项却来自加了 pin 的 `mem_normUnionGaloisSubgroup`，unifier 要在两条路径间来回。还有无类型标注的 `def … :=`、`simpa only [separableNormUnionTransition, …]` 展开 8 行 `letI` 定义体、穿过 `DirectLimit.Ring.lift` 的 `rfl`。
5. 环参数 `R` 在 `ramificationOrder`/`herbrandFunction`/`upperRamificationGroup` 里 implicit 却推不出 → 610 处 `(R := …)`。
6. 同一个整数环有两种模型（`spectralIntegerRing K F` vs `Valuation.valuationSubring (comap …)`），Transport/FieldEquiv/Subgroup 三个文件只做搬运。
7. `Fintype.ofFinite` 被 `letI` 63 次（`[Finite G]` 与 `[Fintype G]` 混用）。

修法：A1–A4（`def` 载体 + term-mode 构造的真实 instance，diamond 按 `rfl` 成立）+ Galois 作用文件改用泛型 `[IsSepClosure K Ω]`、只在最后一行特化到 `SeparableClosure K` + `R` 显式 + 统一整数环模型 + 谱范数 scoped instance 文件 + 删除搬运层。

**验收标准**：每个文件 `lake build <Mod>` < 60 s（硬），目标 < 20 s；全量 < 25 min。重构过程中每改一个文件就单独构建，`timeout 120`，超时即视为设计问题而非等待。

---

## B. 目录结构　【已定稿 2026-10-17】

原则：(1) 按五个目标 + 两层基础（Serre IV 分歧理论、局部域工具）组织；(2) 严格分层，低层不得 import 高层（现有 10 处倒置逐个修正）；(3) 每个子目录 ≤ ~12 个文件，文件名说明数学内容；(4) 合并逐行重复实现，228 → 约 110 个文件；(5) 每层一个聚合文件 `FontaineWintenberger/<Layer>.lean`，根文件只导入聚合文件 + `Main.lean`，CI 检查每个 `.lean` 都被某聚合文件导入。

**决定**：
- 顶层七层：`Mathlib/ → LocalField/ → Ramification/ → APF/ → FieldOfNorms/ → Main.lean`（+ `Attic/`，见下）。现有 `Algebra/`、`GroupTheory/`、`FieldTheory/` 解散。
- 暂不拆仓；`Mathlib/ + LocalField/ + Ramification/` 严格不依赖 APF 以上，将来供 FalseTate 项目共用时可整体搬出。
- 范数估计 11 个文件归 `FieldOfNorms/Estimates/`（陈述含 `apfRamificationBound`，不能下沉）。
- 范畴层保留为可选叶子 `FieldOfNorms/Relative/Equivalence.lean`（论文 3.2.2 原话）。
- `RamificationTransfer`（Prop 3.3.2）保留在 `FieldOfNorms/Estimates/Transfer.lean`，拆出通用部分，文档标注为目标外。
- **死代码不删**：无下游且不对应论文编号陈述的文件和声明，整体移入独立目录 `FontaineWintenberger/Attic/`（不被任何聚合文件导入，但仍由 CI 构建以免腐烂），后续再决定去留。首批：`EmbeddingRestrictionBounds`、`FiniteUniformizer`、`LowerFixedQuotient`、`KrasnerValuation`、`LaurentSubstitution`、`UniversalDiscriminant`、`NormUnionRelativeStages`，以及各目录中确认无引用的声明（Ramification 抽样 96/646）。对应论文编号的叶子（strict APF 层、`Growth`、`StrictPositive`）留在正文。

```
FontaineWintenberger/
  Mathlib/                      -- 上游候选（Mathlib 命名；零项目依赖）
    GroupTheory/Index.lean, GroupTheory/PrimeChain.lean
    FieldTheory/{RelIndex, NormalClosure, LinearDisjointMinpoly, AbsoluteGaloisGroup, FiniteGaloisMap}.lean
    RingTheory/{PolynomialDiscriminant, NormBaseChange, HenselMonogenic, TeichmullerResidue,
                AdicNilpotent, PowerSeriesCohen, ValuationExtension, SequentialInverseLimit}.lean
    Analysis/{NewtonHensel, KrasnerUniqueness, UnitBallAdic, SpectralIntegers}.lean
    Topology/ValuedCompleteness.lean
  LocalField/                   -- 局部域工具层（不 import Ramification/APF/FieldOfNorms）
    Basic.lean                  -- IsCompleteDiscreteValuedField / IsPerfectResidueLocalField / residueChar / ofValued
    Spectral/{Instances, FiniteExtension, Uniqueness, Tower, BaseChange, Maps}.lean   -- Instances = scoped 谱范数实例
    Hensel/{Krasner, RootExtraction}.lean
    Residue/{Basic, Teichmuller, TruncatedCoefficients}.lean
    Laurent/Coordinates.lean
    DVRExtension/{Index, Degree, Tower, ResidueDigits}.lean   -- 从 Ramification 下沉
  Ramification/                 -- Serre IV（可 import LocalField）
    Lower/{Basic, Generator, Wild, Tame, Inertia, Transport, PrimeOrder}.lean
    Herbrand/{Basic, Inverse, Affine, Subgroup}.lean
    Upper/{Basic, Tate, FixedField, Quotient, Functoriality, BaseChange}.lean
    Infinite/{Basic, Restriction, Limit, SplittingField}.lean
    Different/{Monogenic, Hilbert, TraceIdeal, Subextension}.lean
    Norm/{Valuation, Congruence, Tower, Approximation}.lean
    Fields/{Inertia, Wild, Nonnormal, PrimeTower}.lean
    Embedding/{Basic, Closure, Valued, Tate, Fiber, Rebase}.lean
  APF/                          -- 目标 (1)
    Defs.lean (IsAPF, IsStrictlyAPF)  Galois.lean  Index.lean  Herbrand.lean (ψ, φ)
    RamificationBound.lean (i(L/K))   Strict.lean (c(L/K))   Subextension.lean (1.2.3 ii–iv)
    Finite/{Galois, Nonnormal, Slope}.lean
    BaseChange/{UpperGroups, Basic, Strict, Bounds}.lean      -- 1.2.3(i)/(iv)，只留抽象 normed 基一版
    Elementary/{FirstBreak, PrimeDegree, TameCompositum}.lean  -- 1.3
    Tower/{Stages, Residue, Tame, Wild}.lean                   -- 1.4, 2.1.2（K_0, K_1 显式构造）
  FieldOfNorms/
    FiniteIntermediateField.lean  -- 𝓔_{L/K}（现 FiniteLayer）+ Fact(¬finite) 推导实例
    Layers/{Descent, DescentTower, NormPairs, GoodTowers, GaloisGood}.lean   -- 现 Algebra/Finite*
    Basic/{Defs, Valuation, Addition, Ring}.lean                 -- 目标 (2)：X_K(L)、v、加法、Field/Valued/CharP 实例
    Structure/{PrecisionTower, Reconstruction, Truncation, Uniformizer, Completeness, Residue,
               ResidueEmbedding, Laurent, LocalField}.lean      -- 目标 (3)：Thm 2.1.3；LocalField = scoped 局部域实例
    Estimates/{Integral, Topology, Prime, Wild, Tame, NormEstimates, NormContinuity, WildNormContinuity,
               Nonnormal, FiniteLayer, Truncated, Herbrand, RamificationUnbounded, Transfer}.lean
    Functor/{Map, RingHom, Galois, Separable, FullyFaithful}.lean  -- 目标 (4a)：Thm 3.1.2
    Relative/{Defs, Hom, Krull, UpperStage, ApproximateRoots, SeparablyClosed, EssImage, Equivalence}.lean
                                                                 -- X_{L/K}(M)，Thm 3.2.2
    Galois/{AbsoluteGroup, Action, RelAction, Ambient}.lean      -- 目标 (4b)(5)：Cor 3.2.3, Rem 3.2.4（用 G_K 陈述）
  Attic/                        -- 无下游、无论文编号的代码，暂存待议；CI 构建但不导入
  Main.lean                     -- 五个目标的最终陈述，干净签名，供 blueprint 与读者
```
逐文件 old → new 映射见附录 B-1。

---

## C. 命名与术语　【已定稿 2026-10-17】

### C1. 核心对象
| 现名 | 新名 | 备注 |
|---|---|---|
| `NormLimit K L` | `FieldOfNorms K L` | 不加记号 |
| `normLimitGroup K L` | `FieldOfNorms.normCompatibleUnits K L` | |
| `normLimitEval E` | `FieldOfNorms.coord E` | α ↦ α_E，论文 "coordonnée" |
| `SeparableNormUnion K L M` | `RelFieldOfNorms K L M` | X_{L/K}(M)，3.2.1 |
| `FiniteLayer K L` | `FiniteIntermediateField K L` | 对齐 `FiniteGaloisIntermediateField` |
| `spectralIntegerRing K L` | `𝒪[L]` | A5 |
| `SeparableClosure K ≃ₐ[K] SeparableClosure K` | `Gal(SeparableClosure K/K)`；对外 `Field.absoluteGaloisGroup K` | A2 |

### C2. 分歧理论侧
| 现名 | 新名 |
|---|---|
| `herbrandFunction G` / `inverseHerbrandFunction G` | `herbrandPhi R G` / `herbrandPsi R G`（Serre φ/ψ，`R` 显式） |
| `ramificationOrder g`（i_G） | 保留名，移至 `Lower/Basic`，`R` 显式 |
| `lowerRamificationGroup(Real)`、`upperRamificationGroup`、`upperRamificationGroupInfinite` | 保留 |
| `absoluteUpperRamificationGroup K u` | 保留名，改在 `Field.absoluteGaloisGroup K` 上定义 |
| `integralEmbeddingOrder` / `embeddingIntegralOrder` / `closureEmbeddingOrder` / `closureEmbeddingNumber` / `integerRamificationNumber` / `valuedRamificationNumber` | 并入 `embeddingRamificationOrder σ τ : ℝ≥0∞` 与 `embeddingRamificationNumber σ τ : EReal` 两个 |
| `Transport`/`RingTransport`/`FieldEquiv`/`Subgroup` 等搬运文件 | 随整数环模型统一而消失 |

### C3. APF 侧
| 现名 | 新名 |
|---|---|
| `apfRamificationBound K L`（i(L/K)） | `apfFirstBreak K L` |
| `apfStrictnessRatio` / `apfStrictnessConstant`（c(L/K)） | 保留 |
| `apfInertiaIndex` + `apfIndex` | 只留 `apfIndex` |
| `apfFiniteStage K L u`（K_n） | `apfStage K L u` |
| `apfMaximalUnramified` / `apfMaximalTame`（K_0、K_1） | 保留名，显式构造 |
| `apfPhi K L hL` / `apfPsi K L` | `apfPhi K L` / `apfPsi K L`，`[IsAPF K L]` |
| `IsAPF.strictMono_apfPsi` 与根空间 `strictMono_apfPhi` 混用 | 以 `apfPsi`/`apfPhi`/`apfIndex` 为主语的引理全放根空间；`IsAPF.` 只留关于性质本身的引理 |
| `_of_finiteGalois`、`_of_normedAlgebra` 后缀 | 随三版合一消失 |

### C4. Field of norms 内部
| 现名 | 新名 |
|---|---|
| `normLimitMap` 及 16 个映射变体 | `FieldOfNorms.map τ : FieldOfNorms K L →+* FieldOfNorms K L'`、`FieldOfNorms.mapEquiv` |
| `normLimitAut`、`normLimitAbsoluteAut` | `MulSemiringAction` 实例 + `FieldOfNorms.galAction`（对 G_K） |
| `normLimitUniformizer` | `FieldOfNorms.uniformizer` |
| `normLimitLaurentEquiv` / `normLimitPowerSeriesEquiv` | `FieldOfNorms.laurentSeriesEquiv` / `powerSeriesEquiv` |
| `sourceResidueConstants*`（f_{L/K}） | `FieldOfNorms.residueEmbedding` |
| `normLimitResidueEquiv` 与 `sourceResidueConstantsResidueEquiv`（两个方向） | 合一为 `FieldOfNorms.residueEquiv : 𝓀[L] ≃+* 𝓀[X]` |
| `Deep*` / `deepFiniteTower` | `precision*` / `precisionTower`（2.3.2 的"精度 s(E)"） |
| `HighBreak*` / `FiniteLayer.HasFullUpper` | `UpperStage` / `IsFullUpperStage` |
| `separableNormUnion*` / `normUnion*`（196 个标识符） | `RelFieldOfNorms.*`：`of`、`algebraMap`、`map`、`homEquiv`、`krullEquiv`、`absoluteGaloisEquiv`、`ambientGaloisEquiv` |
| `Displacement`、`Constants`、`PrimeValuation`、`Isomorphism`、`Algebra.lean` 等误名文件 | 按附录 B-1 更名/合并 |

### C5. 机械规则
删标识符中的 Original/Actual/Source/Genuine；def 用 lowerCamelCase（`inertia_fixedField_residueEquiv` → `inertiaFixedFieldResidueEquiv`，`finiteTower_autEquivImage` 等）；定理 snake_case 且主语在前；Mathlib 命名空间的引理归位（`monic_discr_map` → `Polynomial.Monic.discr_map`、`sq_sub_dvd_discr` → `Polynomial.sq_sub_dvd_discr`、`exists_aut_extends_intermediate_embedding` → Mathlib 已有）；`local_`/`discreteValued_`/`unitBall_`/`intermediate_spectral_`/`finiteBase_`/`extensionValuationSubring_` 前缀由 namespace 或 typeclass 取代；`[Fintype G]` 统一为 `[Finite G]`，证明内需要时 `Fintype.ofFinite`；`local notation` 全库统一（`𝒪[K]`、`𝓀[K]`、`Gal(·/·)`），删除 166 处各自为政的 `OK`/`R`/`A`/`R₀`/`O`/`D`/`U` 局部记号。

---

## D. 文档　【已定稿 2026-10-18】

1. **模块文档模板**（Mathlib 风格）：`# 标题` / 一段数学说明 / `## Main definitions` / `## Main results` / `## References`（Serre *Local Fields* IV §n 或 Wintenberger §n.m.k）/ `## Implementation notes`（仅当确有设计选择）。声明 docstring 说"是什么"，不说"没假设什么"。
2. **版权头与 LICENSE**：全部文件统一为
   ```
   Copyright (c) 2026 Yijun Yuan. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Yijun Yuan
   ```
   仓库根加 Apache 2.0 `LICENSE`。`NewtonLifting.lean`（改自 Mathlib `NumberTheory/Padics/Hensel.lean`）保留原作者 Robert Y. Lewis 的署名并加上 Yijun Yuan。
3. **填充词**：删除 "actual / original / genuine(ly) / source / intrinsic / literal(ly) / same original / no new … is introduced / without … certificate"（约 4 000 处），逐条重写为陈述数学内容。
4. `ActionContinuity.lean` 的悬空引用 "Yuan, Lemma 5.3" 改为 Wintenberger 3.1.2（X_K(σ) 连续）。
5. **新增**：`CLAUDE.md`（分层规则、标准假设束、命名规范、性能红线、单文件构建方法）；README 重写（删泄漏文字，加模块布局与五个目标对应的声明名）；`blueprint/mathlib-audit.md` 的内容改写为 `docs/MATHLIB_REUSE.md`（A5 表）。

## E. 工程　【已定稿 2026-10-18】

1. **根文件**：只 import 各层聚合文件 + `Main.lean`，模块文档放最前；CI 检查每个 `.lean`（含 `Attic/`）都被某聚合文件或 `Attic.lean` 导入。
2. **lakefile**：四个选项已加入（2026-10-17）；`maxSynthPendingDepth = 3` 与 Mathlib 一致，F5 顺带验证。
3. **blueprint**：整个 `blueprint/` 目录删除（其 `\lean{}` 是空宏，无 DAG）。`Main.lean` + README 承担"五个目标对应哪些声明"的说明。
4. **CI**：保留 `lean-action` + `docgen`；加"聚合文件覆盖检查"；`update.yml` 与 commit-hash pin 的冲突留到 F7 处理（重构期间不动 Mathlib 版本）；确认 `actions/checkout@v7` 存在。
5. **PDF**：`Wintenberger.pdf`、`instruction.pdf` 加入 `.gitignore`（作者将手工移除），README 写明来源。
6. **分支策略**：每阶段一个分支，阶段末全量构建通过、零 warning 后合并到 master；每阶段结束报告编译时间表。

## F. 执行顺序（每阶段一个分支，阶段末全量构建通过、无 warning 再合并）

| 阶段 | 内容 | 风险 | 预计删减 |
|---|---|---|---|
| F0 | 加版权头、LICENSE、CLAUDE.md；删 blueprint/；.gitignore PDF；lakefile 新选项下修 longLine/header 警告 | 无 | — |
| F1 | A1：`LocalField/Basic.lean` 的 class 束 + notation；全库替换 variable 头；删 Valued 搬运层 | 低，机械 | −300 行 |
| F2 | A5 的"删包装、直接用 Mathlib"+ 建 `Mathlib/` 暂存目录 + 修正倒置 import | 低 | −500 行 |
| F3 | Ramification 重组（B）：`R` 显式、合并重复、统一整数环模型、子目录 | 中 | −2 000 行 |
| F4 | A2：`IsAPF`/`IsStrictlyAPF` class；APF 重组（三套基变换合一） | 中 | −2 000 行 |
| F5 | A3/A4：`FieldOfNorms` 类型 + 实例；`RelFieldOfNorms`；全库去 `letI`；FieldOfNorms 重组 | **高**（最慢文件都在这里；必须边改边测时） | −4 000 行，编译时间 −80% |
| F6 | 绝对 Galois 群接口、`Main.lean`、命名表 C 的剩余重命名 | 低 | — |
| F7 | 文档全面重写（D）、README、CI、Mathlib pin 策略 | 低 | — |

每个阶段内：改一个文件 → `timeout 120 lake build <Mod>` → 超时即回头改设计，不等待。

---

## 附录 B-1. 逐文件映射（old → new；"∪" 表示合并进同一文件，"⤴" 表示上移到 Mathlib/，"✗" 表示移入 Attic/（不删除））

### Algebra / GroupTheory / FieldTheory（41 → 约 20）
| 现文件 | 去向 |
|---|---|
| GroupTheory/FiniteIndex, NormalIndex | ⤴ Mathlib/GroupTheory/Index |
| GroupTheory/PrimeChain | ⤴ Mathlib/GroupTheory/PrimeChain（前两条）；`wild_subgroup_prime_chain` → Ramification/Lower/Wild |
| FieldTheory/RelativeIndex | ⤴ Mathlib/FieldTheory/RelIndex |
| Algebra/StableFiniteLayers | ⤴ Mathlib/FieldTheory/NormalClosure |
| Algebra/SeparableEmbeddings | ✗（Mathlib `AlgHom.liftNormal`、`IsSepClosed.lift`） |
| Algebra/SeparableExtensionCategory | FieldOfNorms/Relative/Category（可选叶子） |
| Algebra/PolynomialDiscriminant, PolynomialRootDiscriminant, UniversalDiscriminant | ⤴ Mathlib/RingTheory/PolynomialDiscriminant（Mathlib 命名 `Polynomial.Monic.discr_map` 等） |
| Algebra/NormBaseChange | ⤴ Mathlib/RingTheory/NormBaseChange（前两条）；其余 ∪ FieldOfNorms/Layers/Descent |
| Algebra/FiniteDescent, FiniteDescentTower | 通用部分 ⤴ Mathlib/FieldTheory/LinearDisjointMinpoly；其余 → FieldOfNorms/Layers/{Descent, DescentTower}，合并重复的 `injective_*_tensor_lift`、`adjoinTensorEquiv` |
| Algebra/FiniteNormPairs, GoodFiniteTowers, GaloisGoodFields | FieldOfNorms/Layers/{NormPairs, GoodTowers, GaloisGood}；`IsGoodFiniteLayer` 改 structure/class；`finiteDescentIntersection` ∪ `finiteLayerPullback` 二选一 |

### LocalField（25 → 约 16）
| 现文件 | 去向 |
|---|---|
| （新） | LocalField/Basic：`IsCompleteDVF`、`IsLocalField`、`𝒪ₙ`/`𝓀ₙ`、`residueChar`、`IsCompleteDVF.ofValued` |
| Krasner | 包装 ✗；唯一性引理 ⤴ Mathlib/Analysis/KrasnerUniqueness；项目部分 → Hensel/Krasner |
| KrasnerValuation, NewtonValuation, CompatibleNorm | ✗（Valued 搬运层，被 Basic 的单一入口取代） |
| NewtonLifting | ⤴ Mathlib/Analysis/NewtonHensel |
| SeparableRootExtraction | `unitBall_*` ⤴ 同上；其余 → Hensel/RootExtraction（删 `_additive` 重复） |
| Henselian | `unitBall` 部分 ⤴ Mathlib/Analysis/UnitBallAdic；谱部分 → Spectral/Integers |
| IntegralGenerator | ⤴ Mathlib/RingTheory/HenselMonogenic |
| SpectralIntegers | ⤴ Mathlib/Analysis/SpectralIntegers（`isIntegral_iff_spectralNorm_le_one`、`spectralValuation`）+ Spectral/Integers |
| FiniteExtension, Uniqueness, NormedTower, BaseChange, SpectralMaps | Spectral/{FiniteExtension, Uniqueness, Tower, BaseChange, Maps}；`completeSpace_of_finiteDimensional` ✗ |
| FullGalois, FixedField | Ramification/Lower/Inertia 附近（它们 import Ramification），`fixedField_isGaloisGroup` ✗ |
| ResidueField, ResidueEquiv, TotalRamification | Residue/Basic；TotalRamification ⤴ 候选 |
| AlgebraicResidue | APF/Tower/Residue（它 import APF.Residue；两套整闭包 API 留一套） |
| Teichmuller, TruncatedCoefficients | Residue/{Teichmuller, TruncatedCoefficients}；通用部分 ⤴ Mathlib/RingTheory/{TeichmullerResidue, AdicNilpotent} |
| LaurentCoordinates | Cohen 同构 ⤴ Mathlib/RingTheory/PowerSeriesCohen；`Valued F ℤᵐ⁰` 实例 ⤴；项目部分 → Laurent/Coordinates |
| LaurentSubstitution, UniformContinuity | ⤴（从 `MvPowerSeries.continuous_subst` 派生） |

### Ramification（64 → 约 40，含从 LocalField 下沉与向 APF 上移）
| 现文件 | 去向 |
|---|---|
| Lower, Real, Valuation, NormalizedValuation | Lower/Basic（`R` 显式；加 DVR 特化 API；删 `ValuationSubring.*` 包装） |
| Generator, Uniformizer | Lower/Generator |
| Wild / Tame / Inertia | Lower/{Wild, Tame, Inertia} |
| Transport, RingTransport | Lower/Transport（只留 RingEquiv 版） |
| PrimeDegree | 群论部分 → Lower/PrimeOrder；trace 界 → Different/TraceIdeal；APF 部分 → APF/Elementary |
| Index, Degree, Tower, ResidueDigits | → LocalField/DVRExtension/* |
| Herbrand / HerbrandOrder + HerbrandInverse / HerbrandAffine / HerbrandSubgroup + FirstBreak | Herbrand/{Basic, Inverse, Affine, Subgroup} |
| Upper §GroupAction | Upper/Basic（只依赖 Herbrand/Inverse） |
| Tate, Conjugates, Coset | Upper/Tate（与 EmbeddingComparison §EmbeddingTate 的 pair 版合一） |
| FixedField, CosetMax | Upper/FixedField（6 个变体压成 1–2 个） |
| HerbrandQuotient, HerbrandTransitivity, LowerFixedQuotient, Upper §fixedField | Upper/Quotient |
| FieldEquiv, FiniteRestriction, Transport §IntermediateField | Upper/Functoriality |
| Subgroup | Upper/BaseChange（改名） |
| Absolute + Cofinal / InfiniteRestriction + InfiniteEquiv / UpperLimit + AbsoluteGalois / PolynomialSplitting | Infinite/{Basic, Restriction, Limit, SplittingField}；`absoluteUpperRamificationGroup` 改在 `Field.absoluteGaloisGroup` 上陈述 |
| Different + DifferentOrder / HilbertDifferent / TraceIdeal / OrbitDifferent | Different/{Monogenic, Hilbert, TraceIdeal, Subextension}（OrbitDifferent 747 行拆 4 处） |
| NormValuation / NormCongruence / NormTower / NormApproximation | Norm/{Valuation, Congruence, Tower, Approximation} |
| NormPrecision, NormContinuity | → APF（依赖 `apfRamificationBound`） |
| InertiaFixedField + FiniteUniformizer / TameField + WildTower / Nonnormal / PrimeTower | Fields/{Inertia, Wild, Nonnormal, PrimeTower} |
| Embedding | Embedding/{Basic, Closure}（8 个 order/number 概念压成 2 个） |
| ValuedAutomorphism | Embedding/Valued |
| EmbeddingComparison（1 238 行，14 个 section） | Embedding/{Tate, Rebase}；§RelativeParameter 等 5 个 APF section → APF/BaseChange；纯群论 → Mathlib/GroupTheory |
| EmbeddingFiberTate | Embedding/Fiber |
| EmbeddingFiniteBase, EmbeddingRestrictionBounds | → APF/BaseChange（叶子，无下游，确认后可大幅删减） |

### APF（43 → 约 22）
| 现文件 | 去向 |
|---|---|
| Basic + Abstract | Defs（`class IsAPF`） |
| Galois | Galois |
| Index + IndexTransport + IndexTower | Index |
| Herbrand + HerbrandTower§Calculus + FiniteBaseBounds§Extended + StrictBaseChange§Cofinal | Herbrand |
| Bound + StrictDescent 的 bound 部分 | RamificationBound |
| Strict + StrictPositive + Growth + StrictDescent 的 strict 部分 | Strict（`class IsStrictlyAPF`） |
| FiniteExtension + StrictDescent 其余 | Subextension |
| Finite + FiniteBound / FiniteNonnormal + FiniteGaloisOverfield / FiniteSlope + FiniteTail | Finite/{Galois, Nonnormal, Slope} |
| FiniteOverfieldBaseChange + FiniteBaseChange + FiniteTower + AbsoluteBaseChange | BaseChange/UpperGroups |
| AbstractFiniteBase + FiniteBase + FiniteBaseIndex + HerbrandTower§FiniteBase | BaseChange/Basic（只留抽象 normed 基一版，中间域版作为推论） |
| StrictBaseChange + AbstractFiniteBase 的 strict 部分 | BaseChange/Strict |
| FiniteBaseBounds + FiniteOverfieldBounds | BaseChange/Bounds |
| FirstBound / PrimeDegree(APF 部分) + OrbitDifferent / WildFirstBound + WildCompositumHerbrand | Elementary/{FirstBreak, PrimeDegree, TameCompositum} |
| FiniteStages + CountableStages + DeepTail / Residue / MaximalTame / WildTail | Tower/{Stages, Residue, Tame, Wild} |
| BaseClosure, CofinalBase, AbstractFiniteBase §CommonClosure | ⤴ Mathlib/FieldTheory |

### FieldOfNorms（80 → 约 35）
| 现文件 | 去向 |
|---|---|
| Multiplicative §FiniteLayer + Isomorphism §map + Addition §instances + FiniteLayerGlue | FiniteIntermediateField |
| Multiplicative 其余 + Cofinal + Constants §normLimitOfTail | Basic/Defs（`def FieldOfNorms`；2.1.1） |
| Valuation + Normalization | Basic/Valuation（2.1.2） |
| Addition + Convergence + Operations + Approximation + Separation | Basic/Addition（2.1.3(i)） |
| Algebra + FiniteSums + Semiring + Field + Valued + Displacement | Basic/Ring（`instance Field/Valued/CharP`） |
| PrimeValuation, HerbrandControl, SeparableBaseChange | → APF（纯 APF 内容） |
| Integral, Topology, PrimeNorms, WildNorms, TameNorms, NormEstimates, NormContinuity, WildNormContinuity, NonnormalNormContinuity, FiniteLayerNormEstimates, TruncatedNorms | Estimates/*（或下沉到 Ramification/Norm，它们是有限层范数估计） |
| DeepTruncatedTower + Reconstruction + Truncation + TruncatedInverseLimit(⤴) | Structure/{PrecisionTower, Reconstruction, Truncation} |
| Uniformizer / Completeness + ValuationCompleteness(⤴) / Residue / Constants / LaurentCoordinates | Structure/{Uniformizer, Completeness, Residue, ResidueEmbedding, Laurent}（Thm 2.1.3；两个方向的剩余域同构合一） |
| Isomorphism + FiniteFunctor + FiniteFunctorLaws + FunctorEquivariance + FiniteNaturality | Functor/Map（16 个映射变体压成 `map`/`mapEquiv`） |
| FiniteEmbedding + EmbeddingFunctor | Functor/RingHom |
| FaithfulAction + FiniteGalois + FiniteEmbeddingGalois | Functor/Galois |
| FiniteSeparable / SeparableFullFaithful + FiniteFullFaithful | Functor/{Separable, FullyFaithful}（Thm 3.1.2） |
| SeparableNormUnion + NormUnionCongr | Relative/Defs（`def RelFieldOfNorms`；3.2.1） |
| NormUnionHom + NormUnionAutomorphisms / NormUnionKrull | Relative/{Hom, Krull} |
| HighBreakCoordinates + DiscriminantStability / ApproximateRoots / SeparableClosedUnion | Relative/{UpperStage, ApproximateRoots, SeparablyClosed}（3.2.5） |
| FiniteSubfieldReconstruction + SeparableEssentialImage + SeparableAlgebraicEssentialImage | Relative/EssImage（3.2.2(i)） |
| SeparableFunctor + SeparableEquivalence | Relative/Equivalence（可选叶子） |
| NormUnionAbsoluteGalois | Galois/AbsoluteGroup（Cor 3.2.3，用 `Field.absoluteGaloisGroup` 陈述） |
| ActionContinuity + AbsoluteBaseAction | Galois/Action |
| NormUnionAbsoluteStages + NormUnionStageValuation + NormUnionAbsoluteAction；NormUnionRelativeStages ✗ | Galois/RelAction（泛型 Ω） |
| NormUnionGaloisAction + …RestrictionFun + …Restriction + …GaloisEquiv + …GaloisIsomorphism | Galois/Ambient（Rem 3.2.4；泛型 Ω，最后一行特化） |
| RamificationTransfer | Estimates/Transfer（Prop 3.3.2；通用 `algebraicResidueAut` 部分拆出） |

---

## 执行日志

### F0（分支 `refactor/f0-headers`，2026-10-17/18）
- 229 个 Lean 文件加版权头（`NewtonLifting.lean` 保留 Robert Y. Lewis 署名）；新增 `LICENSE`（Apache 2.0）、`CLAUDE.md`、`docs/MATHLIB_REUSE.md`；删除 `blueprint/`；PDF 加入 `.gitignore`。
- 新 lakefile 选项下的 linter 修正：91 处超长行（其中 7 个匿名 `local instance` 在 `HighBreakCoordinates.lean` 命名为 `FiniteLayer.inst*`）；3 个文件的全局 `open scoped Classical` 改为声明级 `open scoped Classical in`；`OrbitDifferent.lean` 两个 section 的 `[Fintype G] [DecidableEq G]` 改为 `[Finite G]`；`NormCongruence.lean` 两个定理去掉未用的 `[DecidableEq G]`；7 处单行 docstring 折为两行。
- **`maxSynthPendingDepth = 3` 暴露了 A6 的 diamond**：`SeparableAlgebraicEssentialImage.lean`（`AddMonoid (SeparableNormUnion …)`）与 `NormUnionAbsoluteStages.lean`（`Add (NormLimit …)`）各有一个声明 TC 搜索超时（20000 heartbeats）。原因：两者都是 `abbrev`（`DirectLimit` / `WithZero`），实例搜索先去尝试 Mathlib 的通用实例。过渡处理：声明级 `set_option synthInstance.maxHeartbeats 80000 in` + `TODO(F5)` 注释；F5 把载体改为 `def` 后删除。
- 注意：`lake env lean <file>` **不**应用 lakefile 的 `leanOptions`，单文件验证时必须显式传 `-DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true` 等。
- **F0 全量构建通过（零错误、零 warning）。** 但新选项下最慢文件的耗时约翻倍（增量构建，仅重编了改动文件及其下游）：

| 文件 | 原（s） | F0（s） |
|---|---|---|
| NormUnionGaloisEquiv | 1545 | 3432 |
| NormUnionAbsoluteAction | 1358 | 3188 |
| NormUnionGaloisRestrictionFun | 746 | 1749 |
| NormUnionAbsoluteStages | 386 | 1034 |
| NormUnionGaloisIsomorphism | 457 | 803 |
| SeparableAlgebraicEssentialImage | 12 | 66 |

  原因是 `maxSynthPendingDepth = 3` 使 `abbrev` 载体上的失败实例搜索更贵。这不改变 F5 的方案，只是把它的优先级提到 F3/F4 之前再评估（见下一条）。日志存于 `.lake/f0-build.log`。

### F1a（分支 `refactor`，2026-10-19）
- 新文件 `LocalField/Basic.lean`：`IsCompleteDiscreteValuedField`、`IsPerfectResidueLocalField`、`residueChar`、`residueChar_eq`、`IsPerfectResidueLocalField.of_charP`。
- 164 个文件的 `variable`/`omit` 头：`[IsUltrametricDist K] [CompleteSpace K] [IsDiscreteValuationRing 𝒪…]` → `[IsCompleteDiscreteValuedField K]`（按 section 判断，只有完整三元组所在的 section 才打包；跨 section 时在外层三元组处打包）。
- 新的打包搬运定理：`normedAlgebra_isCompleteDiscreteValuedField K L`（`NormedTower.lean`）、`normedAlgebra_isPerfectResidueLocalField`/`normedAlgebra_residueChar_eq`（`ResidueField.lean`）、`discreteValued_isCompleteDiscreteValuedField`（`CompatibleNorm.lean`）；约 110 处 `letI := normedAlgebra_unitBall_isDiscreteValuationRing …` 安装点改用前者。
- **范围调整**：`PerfectField 𝓀[K]` 在 F1a 保持为独立 binder。`IsPerfectResidueLocalField` 额外断言剩余特征为素数，仅有 `PerfectField` 假设的调用方构造不出它；并入将与 `p → residueChar K` 一起在 F1b 完成（届时 `[Fact p.Prime] [CharP 𝓀 p]` 正好提供素特征）。
- 可重放脚本 `scripts/f1a_headers.py`（从干净树一次跑完）；零散问题手工修（`RamificationTransfer` 三处重复 `CompleteSpace` 实例导致 `whnf` 超时；`NormContinuity`/`EmbeddingRestrictionBounds` 的多余 `[CompleteSpace M]`；`AbstractFiniteBase` 的 `PerfectField` 安装点拆回两条）。
- 全量构建零错误零警告。最慢文件耗时与 F0（关闭 `maxSynthPendingDepth` 后）基本持平：NormUnionAbsoluteAction 2751 s、NormUnionGaloisRestrictionFun 1771 s、NormUnionGaloisAction 772–933 s。

### A2（分支 `refactor`，2026-10-19）
- `IsAPFSubextension`、`IsAPF`、`IsStrictlyAPF` 已是 class（`scripts/a2_core.py`）；实例：`isAPF_of_finite`、`IsAPF.intermediateField`、`IsAPFSubextension ↔ IsAPF` 双向、`separableNormUnionStage_isAPF`、`separableNormUnionStage_fact_infinite`。
- `hInfinite : ¬ Module.Finite K L` → `[Fact (¬ Module.Finite K L)]`（A3）。
- 机械替换 `scripts/a2_isapf_class.py`（按文件只删在 HEAD 中确实绑定为 APF/无限假设的名字，区分"作为参数"与"作为函数头"），其余手修：`.1/.2` 投影 → `toIsAPF`/`liminf_pos`；`⟨hL, _⟩` → `⟨_⟩`；`have hX := …` → `haveI/have`；`normLimitAut` 的 `L` 改为显式参数（原先只经 `hL` 隐式确定）。
- 全量构建零错误零警告（提交 561d049）。

### F1b（分支 `refactor`，2026-10-19/20）
- 剩余特征统一为 `residueChar K`。凡在 HEAD 中线程传递 `(p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p]` 的文件（56 个）以及因调用它们而需要的 PerfectField-only 文件（`Addition`、`NormEstimates`、`Normalization`、`NonnormalNormContinuity`、`EmbeddingComparison`、`EmbeddingFiberTate`、`EmbeddingFiniteBase`、`EmbeddingRestrictionBounds`、`FiniteUniformizer`，共 9 个）：K 头改为 `[IsPerfectResidueLocalField K]`，删除 `p` 变量块，在 K 头后声明 `local notation "p" => residueChar K`（term 级用法 `p ^ n`、`(p : E)` 保持原文），调用处删去显式 `p` 实参。64 个文件带该记号；其余仅假设 `PerfectField 𝓀[K]` 的 64 个文件保持不变。
- 真正以通用素数为参数的声明（`lowerRamificationGroup_one_isPGroup`、`wild_fixedField_ramificationIdx_coprime`、`fixedField_wild_norm_baseChange`、`coprime_relIndex_iff_le_of_normal_pGroup`（改名 `q`）等 34 处）保留 `(p : ℕ) [Fact p.Prime]`，调用方继续显式传 `p`。
- 基域搬运：`letI := normedAlgebra_isCompleteDiscreteValuedField K E` + `normedAlgebra_residueField_perfectField K E` 的安装点在需要 `IsPerfectResidueLocalField E` 的地方改为单条 `normedAlgebra_isPerfectResidueLocalField K E`；`FiniteLayerNormEstimates` 用 `normedAlgebra_residueChar_eq` 把 `residueChar E.val` 改写回 `p`（`simp only` 而非 `rw`，后者在该处 `whnf` 超时）。`TameNorms` 加局部实例 `tameNorm_residueField_charP : CharP 𝓀(spectralIntegerRing K Ω) p`。
- 坑：（1）`local notation "p"` 在 `variable (hd : … = p ^ d)` 这类 `variable` 命令里会被展开成 `sorry`（无报错，下游声明静默带 `sorryAx`）——`variable` 中必须写 `residueChar K`；（2）记号不能点号调用，`p.Prime` → `Nat.Prime p`；（3）declaration 头部留下的空行触发 "do not place empty lines within commands"。
- 脚本 `scripts/f1b_residue_char.py`（从干净树一次跑完 62 个文件）+ 约 40 处手工修正。全量构建见 `.lake/f1b-build.log`。

### F5（分支 `refactor`，2026-10-19，进行中）
- **(1/3，提交 69bb39a)** `NormLimit K L := WithZero (normLimitGroup K L)` 与 `SeparableNormUnion K L M := DirectLimit …` 改为 `def`。全局实例：`NormLimit` 上 `CommGroupWithZero`（无条件）、`AddCommMonoid`/`CommSemiring`（`[IsAPF K L]`，低优先级）、`Neg`/`Field`/`CharP (residueChar K)`/`Valued ℤᵐ⁰`（再加 `[Fact (¬ Module.Finite K L)]`）；`SeparableNormUnion` 上 `Field`、`Algebra (NormLimit K L) _`、`Valued ℚᵐ⁰`。`Field` 实例用 `{ normLimitCommSemiring, instCommGroupWithZero, normLimitNeg with … }` 构造（不再经 `CommRing.ofMinimalAxioms`），`Semifield.toCommSemiring`/`toCommGroupWithZero` 对原实例 `rfl`。`NormLimit.recZeroCoe`、`coe_*` 小 API 替代直接的 `WithZero` 引理。旧名 `normLimitField`、`separableNormUnionField`、`…StageField` 保留为 `abbrev … := inferInstance` 别名。
- **(2/3，提交 7b0c1a1)** `scripts/f5_remove_letI.py` 删除 1233 处 `letI := normLimitField …` 等安装与 169 行 `.toMul/.toAdd/.toNonAssocSemiring` 投影 pin；再删 100 处 stage 级 `Algebra.IsSeparable K N.val`、`IsAPF K N.val`、`Fact (¬ Module.Finite K N.val)` 的局部安装。坑：这三个 stage 实例原先以 `N.val`（`N : FiniteLayer L M`）为键，对字面量 stage `(⟨E, _⟩ : FiniteLayer L M).val` 不触发（判别树把 `Subtype.val ⟨E,_⟩` 约化成 `E`）；改为以任意 `E : IntermediateField L M` 为键后两种写法都命中。`FiniteSubfieldReconstruction` 里对 `let P := ⟨normalClosure …, _⟩` 加 `clear_value P`。
- 效果（全量构建，零错误零警告，`.lake/f5-s3-full.log`）：

| 文件 | F1b | F5(2/3) |
|---|---|---|
| NormUnionAbsoluteAction | 6564 s | 557 s |
| NormUnionGaloisEquiv | 1814 s | 12 s |
| NormUnionGaloisRestrictionFun | 785 s | 2 s |
| NormUnionGaloisAction | 747 s | 13 s |
| NormUnionGaloisIsomorphism | 429 s | 24 s |
| NormUnionAbsoluteStages | 409 s | 49 s |

- **(3/3，提交 bd247e8、47cfde2)** 删除两处 `synthInstance.maxHeartbeats 80000` 过渡设置，重新打开 `maxSynthPendingDepth = 3`（不再变慢）。profiler 定位到 `NormUnionAbsoluteAction` 剩余的 346 s 全在一条 `:= rfl`：`separableNormUnionAbsoluteMap_of` 把 `DirectLimit.Ring.lift` 沿商展开（358 s 消去 + 205 s `@[simp]` 属性再查一遍）。改为把 `DirectLimit.Ring.lift_of` 的全部参数显式写出后整文件 13 s。删除别名 `separableNormUnionStageField`/`separableNormUnionField`。
- **(提交 9ae5883)** `CompleteSpace`、`PerfectField 𝓀`、`IsRankOneDiscrete`、`IsDiscreteValuationRing 𝒪` 改为实例（后两者同时以 `Valued.v` 为键，因为下游以 `Valued.v` 而非 `normLimitFieldValuation K L` 提问），删除 37 处安装；`NormUnionAbsoluteStages` 的慢 `rfl` 同样改为引用 `normUnionStageEquiv_apply`（70 s → 10 s）。
- 现状：230 个模块全部 < 60 s，最慢 `EmbeddingFiberTate` 59 s、`EmbeddingComparison` 57 s、`FiniteTower` 48 s、`TruncatedNorms` 47 s、`RamificationTransfer` 36 s；全库约 1800 s CPU（原始约 8000 s，其中六个文件占 5000 s）。
- 未做：六个文件的 `Ω = SeparableClosure K` 泛化为 `[IsSepClosure K Ω]`。慢的根因（abbrev 载体）已消除，这一项不再影响编译时间，归入 C（命名/签名清理）阶段处理。

### F5 设计细化（原计划，供对照）
1. **`FieldOfNorms K L`**：`def FieldOfNorms := WithZero (normCompatibleUnits K L)`；`instance : CommGroupWithZero := inferInstanceAs …`（无条件）；`instance : Nontrivial`、`Inhabited`。`coord E : FieldOfNorms K L →*₀ E` 替代 `normLimitEval`。
2. **加法与域**：`normLimitAdd` 的定义只依赖 `[IsAPF K L]`（`p` 仅被线程传递，`Convergence.lean` 中唯一实质使用是 `p ∈ 𝔪^n` 的发散性，来自 `PrimeValuation`）。目标：
   - `instance [IsAPF K L] : AddCommMonoid (FieldOfNorms K L)`、`CommSemiring`（term-mode，`add := FieldOfNorms.add`）。
   - `instance [IsAPF K L] [Fact (¬ Module.Finite K L)] : Field (FieldOfNorms K L)`：`neg α := (residueChar K - 1) • α`，`{ (inferInstance : CommSemiring _), (inferInstance : CommGroupWithZero _) with … }`，使 `Field.toCommGroupWithZero` 对原实例 `rfl`。需要 `IsPerfectResidueLocalField K`（提供 `residueChar`、素性与 `CharP 𝓀 p`），因此 FieldOfNorms 层的 K 头在 F5 一并改成 `[IsPerfectResidueLocalField K]`，`p` → `residueChar K`（即原 F1b 的剩余部分，并入 F5）。
   - `instance : CharP (FieldOfNorms K L) (residueChar K)`、`Valued _ ℤᵐ⁰`、`IsRankOneDiscrete`、`IsDiscreteValuationRing 𝒪[X]`、`CompleteSpace`、`PerfectField 𝓀[X]`（现为定理 → instance）。
3. **`RelFieldOfNorms K L M`**（现 `SeparableNormUnion`，91 处类型出现）：`def … := DirectLimit (fun N : FiniteLayer L M => FieldOfNorms K N) (transition …)`；stage 的 `Field` 由 1–2 的全局实例给出，所以 Mathlib 的 `DirectLimit` 域实例直接成立（`[∀ i, Field (G i)] [∀ i j h, RingHomClass (T h) …]`）；`instance : Algebra (FieldOfNorms K L) (RelFieldOfNorms K L M)`。删除 683 处 `letI := normLimitField`、182 处 `separableNormUnionField`、118 处 `separableNormUnionAlgebra`、68 处 `normLimitValued` 以及全部 `letI : Mul U/Add U/NonAssocSemiring U/Group (RingAut U)` 投影 pin。
4. 六个最慢文件改用泛型 `[IsSepClosure K Ω]`，只在末尾特化到 `SeparableClosure K`。
5. 顺序：先在 `Multiplicative/Addition/…/Field/Valued` 建新实例并保留旧名为 `abbrev`/`theorem` 别名 → 构建通过 → 全库删 `letI` → 再重命名 `NormLimit → FieldOfNorms`。
