import Submission.DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Immersion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Topology _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u v

section ChartedSpace

variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable (M : ι → Type u) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

private def sigmaAtlas : Set (OpenPartialHomeomorph (Σ i, M i) H) :=
  ⋃ i, (fun e : OpenPartialHomeomorph (M i) H =>
    e.lift_openEmbedding (IsOpenEmbedding.sigmaMk (i := i))) '' atlas H (M i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sigmaAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sigmaAtlas target :: scope.openDecls } }

private theorem mem_sigmaAtlas_iff {e : OpenPartialHomeomorph (Σ i, M i) H} :
    e ∈ sigmaAtlas M ↔ ∃ (i : ι) (f : OpenPartialHomeomorph (M i) H),
      f ∈ atlas H (M i) ∧ f.lift_openEmbedding (IsOpenEmbedding.sigmaMk (i := i)) = e := by
  simp only [sigmaAtlas, Set.mem_iUnion, Set.mem_image]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.mem_sigmaAtlas_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.mem_sigmaAtlas_iff target :: scope.openDecls } }

@[instance_reducible]
instance sigmaChartedSpace : ChartedSpace H (Σ i, M i) where
  atlas := sigmaAtlas M
  chartAt := fun x => (chartAt H x.2).lift_openEmbedding
    (IsOpenEmbedding.sigmaMk (i := x.1))
  mem_chart_source := by
    rintro ⟨i, x⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    exact _root_.Set.mem_image_of_mem _ (mem_chart_source H x)
  chart_mem_atlas := by
    rintro ⟨i, x⟩
    exact (mem_sigmaAtlas_iff M).mpr ⟨i, chartAt H x, chart_mem_atlas H x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaChartedSpace ``Submission.DifferentialGeometry.Topology.sigmaChartedSpace

theorem sigmaChartedSpace_chartAt (x : Σ i, M i) :
    chartAt H x = (chartAt H x.2).lift_openEmbedding
      (IsOpenEmbedding.sigmaMk (i := x.1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaChartedSpace_chartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaChartedSpace_chartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaChartedSpace_chartAt ``Submission.DifferentialGeometry.Topology.sigmaChartedSpace_chartAt

private theorem sigmaChartedSpace_atlas : atlas H (Σ i, M i) = sigmaAtlas M := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sigmaChartedSpace_atlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sigmaChartedSpace_atlas target :: scope.openDecls } }

end ChartedSpace

section Manifold

variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
variable [∀ i, IsManifold I n (M i)]

instance sigmaIsManifold : IsManifold I n (Σ i, M i) where
  compatible := by
    intro e e' he he'
    rw [sigmaChartedSpace_atlas] at he he'
    obtain ⟨i, f, hf, rfl⟩ := (mem_sigmaAtlas_iff M).mp he
    obtain ⟨i', f', hf', rfl⟩ := (mem_sigmaAtlas_iff M).mp he'
    by_cases hii : i = i'
    · subst hii
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact StructureGroupoid.compatible (contDiffGroupoid n I) hf hf'
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext z
      simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
        OpenPartialHomeomorph.lift_openEmbedding_symm_source,
        OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
        OpenPartialHomeomorph.lift_openEmbedding_source, Set.mem_image, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro - ⟨y, -, hy⟩
      exact hii (Sigma.mk.inj_iff.mp hy).1.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaIsManifold ``Submission.DifferentialGeometry.Topology.sigmaIsManifold

end Manifold

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u v

section Orientation

variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E H} [∀ i, IsManifold I ∞ (M i)]
variable {k : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem mem_sigmaTrivializationAt_baseSet_self {i : ι} (p y : M i) :
    (⟨i, y⟩ : Σ j, M j) ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet ↔
      y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
    sigmaChartedSpace_chartAt, OpenPartialHomeomorph.lift_openEmbedding_source]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact sigma_mk_injective hzy ▸ hz
  · exact fun hy => ⟨y, hy, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.mem_sigmaTrivializationAt_baseSet_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.mem_sigmaTrivializationAt_baseSet_self target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem not_mem_sigmaTrivializationAt_baseSet_of_ne {i i' : ι} (h : i ≠ i')
    (p : M i) (y : M i') :
    (⟨i', y⟩ : Σ j, M j) ∉
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, sigmaChartedSpace_chartAt,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  rintro ⟨z, -, hzy⟩
  exact h (congrArg Sigma.fst hzy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.not_mem_sigmaTrivializationAt_baseSet_of_ne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.not_mem_sigmaTrivializationAt_baseSet_of_ne target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [∀ i, IsManifold I ∞ (M i)] in
private theorem extend_sigma_aux {i : ι} (p x : M i) :
    ((chartAt H (⟨i, p⟩ : Σ j, M j)).extend I) ∘
        ((chartAt H (⟨i, x⟩ : Σ j, M j)).extend I).symm =
      ((chartAt H p).extend I) ∘ ((chartAt H x).extend I).symm := by
  funext u
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, sigmaChartedSpace_chartAt,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.extend_sigma_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.extend_sigma_aux target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [∀ i, IsManifold I ∞ (M i)] in
private theorem extend_sigma_aux_apply {i : ι} (x : M i) :
    ((chartAt H (⟨i, x⟩ : Σ j, M j)).extend I) (⟨i, x⟩ : Σ j, M j) =
      ((chartAt H x).extend I) x := by
  simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    sigmaChartedSpace_chartAt, OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.extend_sigma_aux_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.extend_sigma_aux_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem tangentChartEquiv_sigma_apply {i : ι} (p x : M i)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet)
    (hx' : (⟨i, x⟩ : Σ j, M j) ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet)
    (v : TangentSpace I x) :
    tangentChartEquiv I (Σ j, M j) (⟨i, p⟩ : Σ j, M j) ⟨i, x⟩ hx'
        (show TangentSpace I (⟨i, x⟩ : Σ j, M j) from v) =
      tangentChartEquiv I (M i) p x hx v := by
  rw [tangentChartEquiv, tangentChartEquiv, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_apply, TangentBundle.trivializationAt_apply,
    TangentBundle.trivializationAt_apply, extend_sigma_aux, extend_sigma_aux_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.tangentChartEquiv_sigma_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.tangentChartEquiv_sigma_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem tangentChartEquiv_sigma {i : ι} (p x : M i)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet)
    (hx' : (⟨i, x⟩ : Σ j, M j) ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet) :
    tangentChartEquiv I (Σ j, M j) (⟨i, p⟩ : Σ j, M j) ⟨i, x⟩ hx' =
      tangentChartEquiv I (M i) p x hx := by
  apply LinearEquiv.ext
  intro v
  exact tangentChartEquiv_sigma_apply p x hx hx' v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.tangentChartEquiv_sigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.tangentChartEquiv_sigma target :: scope.openDecls } }

def manifoldOrientationUnion (hdim : Module.finrank ℝ E = k)
    (o : ∀ i, ManifoldOrientation I (M i) k) : ManifoldOrientation I (Σ i, M i) k where
  dimension_eq := hdim
  orientation x := (o x.1).orientation x.2
  locally_constant := by
    intro p x hx
    obtain ⟨i, p₀⟩ := p
    obtain ⟨i', x₀⟩ := x
    by_cases hii : i' = i
    · subst i'
      have hx₀ := (mem_sigmaTrivializationAt_baseSet_self p₀ x₀).mp hx
      obtain ⟨U, hUopen, hxU, hUsub, hconst⟩ := (o i).locally_constant p₀ x₀ hx₀
      have hU'sub : Sigma.mk i '' U ⊆
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) (⟨i, p₀⟩ : Σ j, M j)).baseSet := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_sigmaTrivializationAt_baseSet_self p₀ y).mpr (hUsub hy)
      refine ⟨Sigma.mk i '' U, (IsOpenEmbedding.sigmaMk (i := i)).isOpenMap U hUopen,
        ⟨x₀, hxU, rfl⟩, hU'sub, ?_⟩
      intro y hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      rw [tangentChartEquiv_sigma p₀ y₀ (hUsub hy₀) (hU'sub ⟨y₀, hy₀, rfl⟩),
        tangentChartEquiv_sigma p₀ x₀ hx₀ hx]
      exact hconst y₀ hy₀
    · exact absurd hx (not_mem_sigmaTrivializationAt_baseSet_of_ne (Ne.symm hii) p₀ x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.manifoldOrientationUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.manifoldOrientationUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.manifoldOrientationUnion ``Submission.DifferentialGeometry.Topology.manifoldOrientationUnion

theorem manifoldOrientationUnion_orientation (hdim : Module.finrank ℝ E = k)
    (o : ∀ i, ManifoldOrientation I (M i) k) (i : ι) (y : M i) :
    (manifoldOrientationUnion hdim o).orientation (⟨i, y⟩ : Σ j, M j) = (o i).orientation y :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.manifoldOrientationUnion_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.manifoldOrientationUnion_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.manifoldOrientationUnion_orientation ``Submission.DifferentialGeometry.Topology.manifoldOrientationUnion_orientation

end Orientation

end DifferentialGeometry.Topology


namespace DifferentialGeometry.Topology

universe u v

section SigmaEmbedding

variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
variable [∀ i, IsManifold I n (M i)]

private theorem lift_openEmbedding_extend_apply {X X' Z : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Z] [Nonempty Z] {f : X → X'}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (e : OpenPartialHomeomorph X Z) (hf : _root_.Topology.IsOpenEmbedding f)
    (J : ModelWithCorners 𝕜 E' Z) (x : X) :
    (e.lift_openEmbedding hf).extend J (f x) = e.extend J x := by
  rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
    Function.comp_apply, Function.comp_apply]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.lift_openEmbedding_extend_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.lift_openEmbedding_extend_apply target :: scope.openDecls } }

theorem sigmaMk_isImmersionOfComplement (i : ι) :
    IsImmersionOfComplement Unit I I n (Sigma.mk i : M i → Σ j, M j) := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sigma.mk i x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sigma.mk i x))
  intro y hy
  simp only [Function.comp_apply]
  rw [sigmaChartedSpace_chartAt, lift_openEmbedding_extend_apply,
    PartialEquiv.right_inv _ hy]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaMk_isImmersionOfComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaMk_isImmersionOfComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaMk_isImmersionOfComplement ``Submission.DifferentialGeometry.Topology.sigmaMk_isImmersionOfComplement

theorem isSmoothEmbedding_sigmaMk (i : ι) :
    IsSmoothEmbedding I I n (Sigma.mk i : M i → Σ j, M j) :=
  ⟨(sigmaMk_isImmersionOfComplement (I := I) (n := n) i).isImmersion,
    (IsOpenEmbedding.sigmaMk (i := i)).toIsEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSmoothEmbedding_sigmaMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSmoothEmbedding_sigmaMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSmoothEmbedding_sigmaMk ``Submission.DifferentialGeometry.Topology.isSmoothEmbedding_sigmaMk

end SigmaEmbedding

end DifferentialGeometry.Topology


namespace DifferentialGeometry.Topology

universe u v
variable {ι : Type v} {H : Type*} [TopologicalSpace H] [Nonempty H]
  {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [∀ i, IsManifold I n (M i)]

theorem isLocalDiffeomorph_sigmaMk (i : ι) :
    IsLocalDiffeomorph I I n (Sigma.mk i : M i → Σ j, M j) := by
  intro x
  let c := chartAt H x
  let d := c.lift_openEmbedding (IsOpenEmbedding.sigmaMk (i := i))
  let e := c.trans d.symm
  have hc : ContMDiffOn I I n c c.source := contMDiffOn_chart
  have hc' : ContMDiffOn I I n c.symm c.target := contMDiffOn_chart_symm
  have hd : ContMDiffOn I I n d d.source :=
    contMDiffOn_chart (I := I) (n := n) (x := (⟨i, x⟩ : Σ j, M j))
  have hd' : ContMDiffOn I I n d.symm d.target :=
    contMDiffOn_chart_symm (I := I) (n := n) (x := (⟨i, x⟩ : Σ j, M j))
  let D : PartialDiffeomorph I I (M i) (Σ j, M j) n :=
    { e with
      contMDiffOn_toFun := hd'.comp' hc
      contMDiffOn_invFun := hc'.comp' hd }
  refine ⟨D, ⟨mem_chart_source H x, c.map_source (mem_chart_source H x)⟩, ?_⟩
  intro y hy
  change Sigma.mk i y = Sigma.mk i (c.symm (c y))
  rw [c.left_inv hy.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_sigmaMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_sigmaMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_sigmaMk ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_sigmaMk

end DifferentialGeometry.Topology
