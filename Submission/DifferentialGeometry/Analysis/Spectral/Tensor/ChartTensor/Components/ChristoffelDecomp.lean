import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import Mathlib.Analysis.Calculus.FDeriv.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorTrivProj_contMDiffOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (tensorTrivProj (I := I) (M := M) g r s S α)
      ((chartAt H α).source) := by
  classical
  have hbase :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).baseSet =
        (chartAt H α).source := by
    change ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (chartAt H α).source
    change (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∩
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := _root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  refine ContMDiffOn.congr hrewrite ?_
  intro x hx
  have hx_base : x ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [hbase]; exact hx
  unfold tensorTrivProj
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x (S.toSection x) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_contMDiffOn_chart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_contMDiffOn_chart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_contMDiffOn_chart_source ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_contMDiffOn_chart_source

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma mdifferentiableAt_tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source) :
    MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E))
      (tensorTrivProj (I := I) (M := M) g r s S α) b := by
  have hcontMDiff := tensorTrivProj_contMDiffOn_chart_source
    (I := I) (M := M) g r s S α
  have hAt : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (tensorTrivProj (I := I) (M := M) g r s S α) b :=
    hcontMDiff.contMDiffAt ((chartAt H α).open_source.mem_nhds hb_chart)
  exact hAt.mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mdifferentiableAt_tensorTrivProj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mdifferentiableAt_tensorTrivProj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mdifferentiableAt_tensorTrivProj ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mdifferentiableAt_tensorTrivProj

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma differentiableAt_tensorTrivProj_pullback
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
  classical
  set fE : M → TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α
  set φ : PartialEquiv M E := extChartAt I α
  have hf_at : MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b :=
    mdifferentiableAt_tensorTrivProj (I := I) (M := M) g r s S α hb_chart
  have hb_source : b ∈ φ.source := by
    have hb_source' : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact hb_source'
  have hbridge :
      MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b ↔
        MDifferentiableWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E))
          (fE ∘ φ.symm) (_root_.Set.range I) (φ b) :=
    mdifferentiableAt_iff_source_of_mem_source (x := α) (x' := b) hb_chart
  have hwithin :
      MDifferentiableWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E))
        (fE ∘ φ.symm) (_root_.Set.range I) (φ b) :=
    hbridge.mp hf_at
  have htgt : (extChartAt I α).target ⊆ _root_.Set.range I :=
    extChartAt_target_subset_range α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hrange_nhds : _root_.Set.range I ∈ 𝓝 (φ b) :=
    Filter.mem_of_superset (hint_open.mem_nhds hb_int)
      (interior_subset.trans htgt)
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hwithin
  exact hwithin.differentiableAt hrange_nhds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorTrivProj_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorTrivProj_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorTrivProj_pullback ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorTrivProj_pullback

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem mfderiv_tensorTrivProj_eq_chart_fderiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
        (tensorTrivProj (I := I) (M := M) g r s S α) b) v =
      fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v) := by
  classical
  set fE : M → TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α
  set φ : PartialEquiv M E := extChartAt I α
  set y₀ : E := φ b
  set gE : E → TensorRSModel r s ℝ E := fE ∘ φ.symm
  have hb_source : b ∈ φ.source := by
    rw [extChartAt_source]; exact hb_chart
  have hfE_eqOn : ∀ y, y ∈ φ.source → fE y = gE (φ y) := by
    intro y hy
    change fE y = fE (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hsrc_nhds : φ.source ∈ 𝓝 b :=
    extChartAt_source_mem_nhds' (I := I) hb_source
  have hev : fE =ᶠ[𝓝 b] gE ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hfE_eqOn y hy
  have hmfderiv_eq :
      mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b =
        mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E)) (gE ∘ φ) b :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hφ_mdiff : MDiffAt φ b :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hb_chart
  have hgE_diff : DifferentiableAt ℝ gE y₀ :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S α hb_chart hb_int
  have hgE_mdiff : MDifferentiableAt (𝓘(ℝ, E))
      (𝓘(ℝ, TensorRSModel r s ℝ E)) gE y₀ :=
    hgE_diff.mdifferentiableAt
  have hchain :
      mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E)) (gE ∘ φ) b =
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E)) gE (φ b)).comp
          (mfderiv I (𝓘(ℝ, E)) φ b) :=
    mfderiv_comp b hgE_mdiff hφ_mdiff
  have hmf_to_fderiv :
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E)) gE (φ b) =
        fderiv ℝ gE (φ b) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := TensorRSModel r s ℝ E)
      (f := gE) (x := φ b)
  have htriv_eq :
      mfderiv I (𝓘(ℝ, E)) (extChartAt I α) b =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := b) hb_chart).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ gE (φ b))
        ((mfderiv I (𝓘(ℝ, E)) (extChartAt I α) b) v) =
      fderiv ℝ gE y₀
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)
  rw [htriv_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_eq_chart_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_eq_chart_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_eq_chart_fderiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_eq_chart_fderiv

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorTrivProj_chart_pullback_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    HasFDerivAt
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b))
      (extChartAt I α b) :=
  (differentiableAt_tensorTrivProj_pullback (I := I) (M := M) g r s S α
    hb_chart hb_int).hasFDerivAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_chart_pullback_hasFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_chart_pullback_hasFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_chart_pullback_hasFDerivAt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_chart_pullback_hasFDerivAt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_pullback_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
        (extChartAt I α).symm =
      (tensorChartComponentProjection (E := E) r s Idx Jdx) ∘
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm) := by
  funext y
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_pullback_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_pullback_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_chart_pullback_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    HasFDerivAt
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
        (extChartAt I α).symm)
      ((tensorChartComponentProjection (E := E) r s Idx Jdx).comp
        (fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b)))
      (extChartAt I α b) := by
  classical
  have hfact := tensorChartComponentRaw_pullback_eq
    (I := I) (M := M) g r s S α Idx Jdx
  rw [hfact]
  have htriv := tensorTrivProj_chart_pullback_hasFDerivAt
    (I := I) (M := M) g r s S α hb_chart hb_int
  have hCLM_hasFDeriv :
      HasFDerivAt (tensorChartComponentProjection (E := E) r s Idx Jdx)
        ((tensorChartComponentProjection (E := E) r s Idx Jdx) :
          TensorRSModel r s ℝ E →L[ℝ] ℝ)
        ((tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b)) :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).hasFDerivAt
  exact HasFDerivAt.comp (extChartAt I α b) hCLM_hasFDeriv htriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_hasFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_hasFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_hasFDerivAt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_hasFDerivAt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_chart_pullback_fderiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) =
      (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
        (fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b)) :=
  (tensorChartComponentRaw_chart_pullback_hasFDerivAt
    (I := I) (M := M) g r s S α Idx Jdx hb_chart hb_int).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_fderiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chart_pullback_fderiv

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_partial_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (w : E) :
    fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        (fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b) w) := by
  classical
  rw [tensorChartComponentRaw_chart_pullback_fderiv
    (I := I) (M := M) g r s S α Idx Jdx hb_chart hb_int]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_partial_decomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_partial_decomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_partial_decomp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_partial_decomp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_mfderiv_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, ℝ))
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) b) v =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
          (tensorTrivProj (I := I) (M := M) g r s S α) b) v) := by
  classical
  set fE : M → TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α
  set P : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have hf_mdiff : MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b :=
    mdifferentiableAt_tensorTrivProj (I := I) (M := M) g r s S α hb_chart
  have hP_mdiff : MDifferentiableAt (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ))
      (P : TensorRSModel r s ℝ E → ℝ) (fE b) := by
    have hP_diff : ContMDiff (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ)) ∞
        (P : TensorRSModel r s ℝ E → ℝ) := P.contMDiff
    exact (hP_diff.contMDiffAt).mdifferentiableAt (by simp)
  have hcomp_eq :
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx =
        (P : TensorRSModel r s ℝ E → ℝ) ∘ fE := by
    funext x
    rfl
  rw [hcomp_eq]
  rw [mfderiv_comp b hP_mdiff hf_mdiff]
  have hP_fderiv : fderiv ℝ (P : TensorRSModel r s ℝ E → ℝ) (fE b) =
      (P : TensorRSModel r s ℝ E →L[ℝ] ℝ) :=
    P.fderiv (x := fE b)
  have hP_eq :
      mfderiv (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ))
          (P : TensorRSModel r s ℝ E → ℝ) (fE b) =
        fderiv ℝ (P : TensorRSModel r s ℝ E → ℝ) (fE b) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := TensorRSModel r s ℝ E) (E' := ℝ)
      (f := (P : TensorRSModel r s ℝ E → ℝ)) (x := fE b)
  rw [hP_eq, hP_fderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_mfderiv_decomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_mfderiv_decomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_mfderiv_decomp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_mfderiv_decomp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_chartBasis_partial
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    (mfderiv I (𝓘(ℝ, ℝ))
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) b)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
          (tensorTrivProj (I := I) (M := M) g r s S α) b)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)) :=
  tensorChartComponentRaw_mfderiv_decomp
    (I := I) (M := M) g r s α S hb_chart Idx Jdx _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chartBasis_partial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chartBasis_partial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chartBasis_partial ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_chartBasis_partial

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
