import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Rhs.Pairings
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace RicciDualNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem


private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def ricciCovectorChartCoord
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (j : Fin (Module.finrank ℝ E)) (b : M) : ℝ :=
  ricciTensor (I := I) g b (gradFun (I := I) g φ b)
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricciCovectorChartCoord_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (j : Fin (Module.finrank ℝ E)) (b : M) :
    ricciCovectorChartCoord (I := I) g α φ j b =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_def ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciCovectorChartCoord_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (ricciCovectorChartCoord (I := I) g α φ j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
        (ricciTensor (I := I) g b)) :=
    ricciTensor_contMDiff (I := I) g
  have hGrad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g φ b)) :=
    gradFun_contMDiff_total_section (I := I) g φ.contMDiff
  have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := I) α j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
  have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b,
          ricciTensor (I := I) g b
            (gradFun (I := I) g φ b)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)⟩ :
          _root_.Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic.contMDiffOn hGrad.contMDiffOn hBasis
  change ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
  intro b hb
  have hpb := happ b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciCovectorChartCoord_contMDiffOn

noncomputable def chartRicciDualNormSq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    ricciCovectorChartCoord (I := I) g α φ i b *
      ricciCovectorChartCoord (I := I) g α φ j b *
      chartInvGramMatrix (I := I) g α b i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma chartRicciDualNormSq_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (b : M) :
    chartRicciDualNormSq (I := I) g α φ b =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ricciCovectorChartCoord (I := I) g α φ i b *
          ricciCovectorChartCoord (I := I) g α φ j b *
          chartInvGramMatrix (I := I) g α b i j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_def ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem chartRicciDualNormSq_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartRicciDualNormSq (I := I) g α φ)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  unfold chartRicciDualNormSq
  refine contMDiffOn_finsetSum (fun i _ => ?_)
  refine contMDiffOn_finsetSum (fun j _ => ?_)
  have h1 := ricciCovectorChartCoord_contMDiffOn (I := I) g α φ i
  have h2 := ricciCovectorChartCoord_contMDiffOn (I := I) g α φ j
  have h3 := chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  exact (h1.mul h2).mul h3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_contMDiffOn

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem chartRicciDualNormSq_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) :
    ContinuousOn (chartRicciDualNormSq (I := I) g α φ)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
  (chartRicciDualNormSq_contMDiffOn (I := I) g α φ).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_continuousOn

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem chartRicciDualNormSq_bdd_on_compact
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {K : Set M} (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, chartRicciDualNormSq (I := I) g α φ b ≤ C := by
  classical
  have h_cont : ContinuousOn (chartRicciDualNormSq (I := I) g α φ) K :=
    (chartRicciDualNormSq_continuousOn (I := I) g α φ).mono hK_subset
  by_cases hK_ne : K.Nonempty
  · obtain ⟨b_max, hb_max_mem, hb_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne h_cont
    refine ⟨max (chartRicciDualNormSq (I := I) g α φ b_max) 0, le_max_right _ _, ?_⟩
    intro b hb
    have h := hb_max hb
    exact h.trans (le_max_left _ _)
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    exfalso; exact hK_ne ⟨b, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_bdd_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_bdd_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_bdd_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_bdd_on_compact

noncomputable def ricciSharp (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) : TangentSpace I b :=
  DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g b
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b)).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricciSharp_def (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) :
    ricciSharp (I := I) g φ b =
      DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g b
        (ricciTensor (I := I) g b (gradFun (I := I) g φ b)).toLinearMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp_def ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharp_def

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma inner_ricciSharp (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) (w : TangentSpace I b) :
    g.inner b (ricciSharp (I := I) g φ b) w =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b) w := by
  rw [ricciSharp_def]
  exact DifferentialGeometry.Geometry.Operator.inner_metricSharp (I := I) g b
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b)).toLinearMap w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma inner_ricciSharp_right (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) (w : TangentSpace I b) :
    g.inner b w (ricciSharp (I := I) g φ b) =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b) w := by
  rw [g.symm b w (ricciSharp (I := I) g φ b)]
  exact inner_ricciSharp (I := I) g φ b w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp_right ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharp_right

noncomputable def ricciSharpChartCoeff
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (k : Fin (Module.finrank ℝ E)) (b : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α b k j *
      ricciCovectorChartCoord (I := I) g α φ j b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricciSharpChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (k : Fin (Module.finrank ℝ E)) (b : M) :
    ricciSharpChartCoeff (I := I) g α φ k b =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b k j *
          ricciCovectorChartCoord (I := I) g α φ j b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff_def ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartCoeff_def

noncomputable def ricciSharpChartLocal
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) : TangentSpace I b :=
  ∑ k : Fin (Module.finrank ℝ E),
    ricciSharpChartCoeff (I := I) g α φ k b •
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma inner_ricciSharpChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner b (ricciSharpChartLocal (I := I) g α φ b)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
      ricciCovectorChartCoord (I := I) g α φ k b := by
  classical
  unfold ricciSharpChartLocal
  rw [show g.inner b (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
          ∑ i, ricciSharpChartCoeff (I := I) g α φ i b *
            g.inner b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) from ?_]
  swap
  · rw [show (g.inner b (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)) =
            (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
                g.inner b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)) from ?_]
    · rw [sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  have ha : ∀ i, ricciSharpChartCoeff (I := I) g α φ i b =
      ∑ j, chartInvGramMatrix (I := I) g α b i j *
        ricciCovectorChartCoord (I := I) g α φ j b := fun i => rfl
  rw [show ∑ i, ricciSharpChartCoeff (I := I) g α φ i b *
            g.inner b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α b i j *
              ricciCovectorChartCoord (I := I) g α φ j b) *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    rfl
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α b i j *
              ricciCovectorChartCoord (I := I) g α φ j b) *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α b i j *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k) *
            ricciCovectorChartCoord (I := I) g α φ j b from ?_]
  swap
  · rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α b i j *
                ricciCovectorChartCoord (I := I) g α φ j b) *
                  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α b i j *
                  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k) *
                  ricciCovectorChartCoord (I := I) g α φ j b from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  have hsym : ∀ i, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k i := fun i => g.symm b _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α b i j *
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α b i j *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k) =
            (∑ i, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k i *
              chartInvGramMatrix (I := I) g α b i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    have hidentity : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b *
          chartInvGramMatrix (I := I) g α b) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hb]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α b i j *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k) *
              ricciCovectorChartCoord (I := I) g α φ j b =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            ricciCovectorChartCoord (I := I) g α φ j b from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), _root_.MulZeroClass.zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharpChartLocal_chartBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharpChartLocal_chartBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharpChartLocal_chartBasis ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharpChartLocal_chartBasis

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciSharpChartLocal_eq_ricciSharp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ricciSharpChartLocal (I := I) g α φ b =
      ricciSharp (I := I) g φ b := by
  classical
  apply DifferentialGeometry.Geometry.Operator.metricFlatLinear_injective (I := I) g b
  ext v
  change g.inner b (ricciSharpChartLocal (I := I) g α φ b) v =
    g.inner b (ricciSharp (I := I) g φ b) v
  rw [inner_ricciSharp (I := I) g φ b v]
  set bs : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
    DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hb
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => bs.repr v k
  have hv_decomp : v = ∑ k, c k • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b := by
    have h1 : v = ∑ k, bs.repr v k • bs k := (bs.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply (I := I) α hb k]
  rw [hv_decomp]
  rw [show g.inner b (ricciSharpChartLocal (I := I) g α φ b)
        (∑ k, c k • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
        ∑ k, c k * g.inner b (ricciSharpChartLocal (I := I) g α φ b)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show (ricciTensor (I := I) g b (gradFun (I := I) g φ b))
        (∑ k, c k • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
        ∑ k, c k *
          (ricciTensor (I := I) g b (gradFun (I := I) g φ b))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_ricciSharpChartLocal_chartBasis (I := I) g α φ hb k]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal_eq_ricciSharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal_eq_ricciSharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal_eq_ricciSharp ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciSharpChartLocal_eq_ricciSharp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma inner_ricciSharpChartLocal_self_eq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (b : M) :
    g.inner b (ricciSharpChartLocal (I := I) g α φ b)
        (ricciSharpChartLocal (I := I) g α φ b) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ricciSharpChartCoeff (I := I) g α φ k b *
          ricciSharpChartCoeff (I := I) g α φ l b *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l := by
  classical
  unfold ricciSharpChartLocal
  have hexpand :
      g.inner b
          (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
          (∑ j, ricciSharpChartCoeff (I := I) g α φ j b •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)
        = ∑ i, ∑ j, (ricciSharpChartCoeff (I := I) g α φ i b *
            ricciSharpChartCoeff (I := I) g α φ j b) *
            g.inner b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) := by
    have hL :
        g.inner b
            (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
          = ∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
              g.inner b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL]
    rw [sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [smul_apply]
    have hR :
        g.inner b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
            (∑ j, ricciSharpChartCoeff (I := I) g α φ j b •
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)
          = ∑ j, ricciSharpChartCoeff (I := I) g α φ j b *
              g.inner b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharpChartLocal_self_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.inner_ricciSharpChartLocal_self_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma sum_sharp_coeff_gram_eq_invGram
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ricciSharpChartCoeff (I := I) g α φ k b *
          ricciSharpChartCoeff (I := I) g α φ l b *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l =
      chartRicciDualNormSq (I := I) g α φ b := by
  classical
  set N := Module.finrank ℝ E with hN_def
  set α' : Fin N → ℝ :=
    fun i => ricciCovectorChartCoord (I := I) g α φ i b with hα'_def
  set Ginv : Fin N → Fin N → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g α b i j with hGinv_def
  set G : Fin N → Fin N → ℝ :=
    fun i j => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i j with hG_def
  have hsym : ∀ k l, G k l = G l k := fun k l => by
    rw [hG_def]; exact g.symm b _ _
  have hinner : ∀ i l, (∑ k, Ginv k i * G k l) =
      if l = i then (1 : ℝ) else 0 := by
    intro i l
    rw [show (∑ k, Ginv k i * G k l) =
        (∑ k, G l k * Ginv k i) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro k _
      rw [hsym k l]; ring
    have hid : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b *
            chartInvGramMatrix (I := I) g α b) l i =
        if l = i then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hb]
      rw [Matrix.one_apply]
    change (∑ k, G l k * Ginv k i) =
        if l = i then (1 : ℝ) else 0
    rw [hG_def, hGinv_def]
    rw [← hid, Matrix.mul_apply]
  have hkrInv : ∀ i j, (∑ k, ∑ l, Ginv k i * Ginv l j * G k l) = Ginv i j := by
    intro i j
    rw [show (∑ k, ∑ l, Ginv k i * Ginv l j * G k l) =
        (∑ l, Ginv l j * (∑ k, Ginv k i * G k l)) from ?_]
    swap
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [show (∑ l, Ginv l j * (∑ k, Ginv k i * G k l)) =
        (∑ l, Ginv l j * (if l = i then (1 : ℝ) else 0)) from
      Finset.sum_congr rfl (fun l _ => by rw [hinner i l])]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]; ring
    · intro l _ hli
      rw [if_neg hli, _root_.MulZeroClass.mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hLHS_full :
      (∑ k, ∑ l,
        ricciSharpChartCoeff (I := I) g α φ k b *
          ricciSharpChartCoeff (I := I) g α φ l b *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l) =
      ∑ i, ∑ j, α' i * α' j * Ginv i j := by
    have hstep1 :
        ∀ k l, ricciSharpChartCoeff (I := I) g α φ k b *
            ricciSharpChartCoeff (I := I) g α φ l b *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l =
          ∑ i, ∑ j, α' i * α' j * (Ginv k i * Ginv l j * G k l) := by
      intro k l
      rw [ricciSharpChartCoeff_def, ricciSharpChartCoeff_def]
      rw [show (∑ i, chartInvGramMatrix (I := I) g α b k i *
                ricciCovectorChartCoord (I := I) g α φ i b) =
              ∑ i, Ginv k i * α' i from
            Finset.sum_congr rfl (fun i _ => by rw [hα'_def, hGinv_def])]
      rw [show (∑ j, chartInvGramMatrix (I := I) g α b l j *
                ricciCovectorChartCoord (I := I) g α φ j b) =
              ∑ j, Ginv l j * α' j from
            Finset.sum_congr rfl (fun j _ => by rw [hα'_def, hGinv_def])]
      rw [show DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l = G k l from rfl]
      rw [Finset.sum_mul_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    have hLHS_subst :
        (∑ k, ∑ l,
          ricciSharpChartCoeff (I := I) g α φ k b *
            ricciSharpChartCoeff (I := I) g α φ l b *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l) =
        ∑ k, ∑ l, ∑ i, ∑ j,
          α' i * α' j * (Ginv k i * Ginv l j * G k l) :=
      Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => hstep1 k l))
    rw [hLHS_subst]
    have hsumprod1 :
        (∑ k, ∑ l, ∑ i, ∑ j,
            α' i * α' j * (Ginv k i * Ginv l j * G k l)) =
        ∑ kl ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
          ∑ ij ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
            α' ij.1 * α' ij.2 * (Ginv kl.1 ij.1 * Ginv kl.2 ij.2 * G kl.1 kl.2) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_product]
    rw [hsumprod1]
    rw [Finset.sum_comm]
    have hsumprod2 :
        (∑ ij ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
          ∑ kl ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
            α' ij.1 * α' ij.2 * (Ginv kl.1 ij.1 * Ginv kl.2 ij.2 * G kl.1 kl.2)) =
        ∑ i, ∑ j, ∑ k, ∑ l,
            α' i * α' j * (Ginv k i * Ginv l j * G k l) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.sum_product]
    rw [hsumprod2]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [show (∑ k, ∑ l, α' i * α' j * (Ginv k i * Ginv l j * G k l)) =
        α' i * α' j * (∑ k, ∑ l, Ginv k i * Ginv l j * G k l) from ?_]
    · rw [hkrInv]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.mul_sum]
  rw [hLHS_full]
  unfold chartRicciDualNormSq
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hα'_def, hGinv_def]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.sum_sharp_coeff_gram_eq_invGram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.sum_sharp_coeff_gram_eq_invGram target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartRicciDualNormSq_eq_inner_ricciSharp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    chartRicciDualNormSq (I := I) g α φ b =
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) := by
  classical
  rw [← ricciSharpChartLocal_eq_ricciSharp (I := I) g α φ hb]
  rw [inner_ricciSharpChartLocal_self_eq (I := I) g α φ b]
  exact (sum_sharp_coeff_gram_eq_invGram (I := I) g α φ hb).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_eq_inner_ricciSharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_eq_inner_ricciSharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_eq_inner_ricciSharp ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_eq_inner_ricciSharp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartRicciDualNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    0 ≤ chartRicciDualNormSq (I := I) g α φ b := by
  rw [chartRicciDualNormSq_eq_inner_ricciSharp (I := I) g α φ hb]
  exact metric_inner_self_nonneg (I := I) (M := M) g b _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_nonneg

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairing_cs_sq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (b : M) (w : TangentSpace I b) :
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b) w) ^ 2 ≤
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) *
        g.inner b w w := by
  rw [show ricciTensor (I := I) g b (gradFun (I := I) g φ b) w =
        g.inner b (ricciSharp (I := I) g φ b) w from
      (inner_ricciSharp (I := I) g φ b w).symm]
  exact metric_inner_cauchy_schwarz_sq (I := I) (M := M) g b _ w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairing_cs_sq_chartLocal
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (w : TangentSpace I b) :
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b) w) ^ 2 ≤
      chartRicciDualNormSq (I := I) g α φ b * g.inner b w w := by
  rw [chartRicciDualNormSq_eq_inner_ricciSharp (I := I) g α φ hb]
  exact ricciPairing_cs_sq (I := I) g φ b w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq_chartLocal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq_chartLocal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq_chartLocal ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.ricciPairing_cs_sq_chartLocal

section GlobalBound

variable [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tsupport_chartAtlasPOU_compact (α : M) :
    IsCompact (tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)) :=
  isClosed_tsupport _ |>.isCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.tsupport_chartAtlasPOU_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.tsupport_chartAtlasPOU_compact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma tsupport_chartAtlasPOU_subset_baseSet (α : M) :
    tsupport (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) ⊆
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  have hsrc : x ∈ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α hx
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsrc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.tsupport_chartAtlasPOU_subset_baseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.tsupport_chartAtlasPOU_subset_baseSet target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRicciDualNormSq_bdd_on_chart_tsupport
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ tsupport (fun x : M =>
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x),
      chartRicciDualNormSq (I := I) g α φ b ≤ C :=
  chartRicciDualNormSq_bdd_on_compact (I := I) g α φ
    (tsupport_chartAtlasPOU_compact (I := I) (M := M) α)
    (tsupport_chartAtlasPOU_subset_baseSet (I := I) (M := M) α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_bdd_on_chart_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.chartRicciDualNormSq_bdd_on_chart_tsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_global_ricci_dual_normSq_bound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C := by
  classical
  have hbound_each : ∀ α, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ tsupport (fun x : M =>
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x),
      chartRicciDualNormSq (I := I) g α φ b ≤ C := fun α =>
    chartRicciDualNormSq_bdd_on_chart_tsupport (I := I) (M := M) g φ α
  choose Cfn hCfn_nn hCfn_bdd using hbound_each
  by_cases hM_ne : Nonempty M
  · let b₀ : M := Classical.arbitrary M
    obtain ⟨α_seed, _hα_seed_pos⟩ : ∃ α, 0 < (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b₀ :=
      (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ b₀)
    have hα_seed_support : (Function.support ((chartAtlasPOU I M) α_seed)).Nonempty :=
      ⟨b₀, ne_of_gt _hα_seed_pos⟩
    have hα_seed_mem : α_seed ∈ chartAtlasPOUFinset (I := I) (M := M) := by
      rw [chartAtlasPOU_finset_mem]
      exact hα_seed_support
    have hS_ne : (chartAtlasPOUFinset (I := I) (M := M)).Nonempty :=
      ⟨α_seed, hα_seed_mem⟩
    refine ⟨(chartAtlasPOUFinset (I := I) (M := M)).sup' hS_ne Cfn, ?_, ?_⟩
    · exact le_trans (hCfn_nn α_seed)
        (Finset.le_sup' (f := Cfn) hα_seed_mem)
    · intro b
      obtain ⟨α₀, hα₀_pos⟩ : ∃ α, 0 < (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b :=
        (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ b)
      have hα₀_support : (Function.support ((chartAtlasPOU I M) α₀)).Nonempty :=
        ⟨b, ne_of_gt hα₀_pos⟩
      have hα₀_mem : α₀ ∈ chartAtlasPOUFinset (I := I) (M := M) := by
        rw [chartAtlasPOU_finset_mem]
        exact hα₀_support
      have hb_tsupp : b ∈ tsupport (fun x : M =>
          (chartAtlasPOU I M α₀ : C^∞⟮I, M; ℝ⟯) x) :=
        subset_tsupport _ (ne_of_gt hα₀_pos)
      have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α₀).baseSet :=
        tsupport_chartAtlasPOU_subset_baseSet (I := I) (M := M) α₀ hb_tsupp
      have hg_eq : g.inner b (ricciSharp (I := I) g φ b)
            (ricciSharp (I := I) g φ b) =
          chartRicciDualNormSq (I := I) g α₀ φ b :=
        (chartRicciDualNormSq_eq_inner_ricciSharp (I := I) g α₀ φ hb_base).symm
      rw [hg_eq]
      have hb_le_Cα₀ : chartRicciDualNormSq (I := I) g α₀ φ b ≤ Cfn α₀ :=
        hCfn_bdd α₀ b hb_tsupp
      exact le_trans hb_le_Cα₀ (Finset.le_sup' (f := Cfn) hα₀_mem)
  · refine ⟨0, le_refl 0, ?_⟩
    intro b
    exact absurd ⟨b⟩ hM_ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.exists_global_ricci_dual_normSq_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.exists_global_ricci_dual_normSq_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.exists_global_ricci_dual_normSq_bound ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm.exists_global_ricci_dual_normSq_bound

end GlobalBound

end RicciDualNorm
end Laplacian
end Analysis
end DifferentialGeometry

end
