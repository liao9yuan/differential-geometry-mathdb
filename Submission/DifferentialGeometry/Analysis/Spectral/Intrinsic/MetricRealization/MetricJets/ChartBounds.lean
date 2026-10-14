import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Perturbation.GramDifference
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Christoffel.Perturbation
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.OrderDropping

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M ↦ Tensor0SBundle.TensorRSSpace r s I b)]
    (b : M) : NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorRSRiemannianNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorRSRiemannianNormedAddCommGroup_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramOnE_diffAt_interior
    (g : SmoothRiemannianMetric I M) (α : M) (l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α l b) y := by
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior ((extChartAt I α).target : Set E)) :=
    (chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset
  exact (hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramOnE_diffAt_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramOnE_diffAt_interior target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_contDiffOn_interior
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior ((extChartAt I α).target : Set E)))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a f)
      (interior ((extChartAt I α).target : Set E)) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hrw : (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a f) =
      fun y => fderiv ℝ f y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a) := rfl
  rw [hrw]
  exact hfderiv.clm_apply contDiffOn_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_contDiffOn_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_contDiffOn_interior target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_chartGramOnE_diffAt_interior
    (g : SmoothRiemannianMetric I M) (α : M) (a l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g α l b)) y := by
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior ((extChartAt I α).target : Set E)) :=
    (chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset
  have hcd_partial : ContDiffOn ℝ ∞
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g α l b))
      (interior ((extChartAt I α).target : Set E)) :=
    partialDeriv_contDiffOn_interior (I := I) α hcd_int a
  exact (hcd_partial.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_chartGramOnE_diffAt_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_chartGramOnE_diffAt_interior target :: scope.openDecls } }

def reprDiffChartCompOnE (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    ccTensorBilinSymm (I := I) g_bg
      (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
      ((extChartAt I α).symm y)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l ((extChartAt I α).symm y))
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b ((extChartAt I α).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.reprDiffChartCompOnE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.reprDiffChartCompOnE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.reprDiffChartCompOnE ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.reprDiffChartCompOnE

omit [BoundarylessManifold I M] in
theorem chartGramOnE_realizeMetricAt_sub_funext
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) :
    (fun y : E => chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b y -
        chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b y) =
      reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b := by
  funext y
  rw [reprDiffChartCompOnE]
  exact chartGramOnE_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂ α l b y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramOnE_realizeMetricAt_sub_funext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramOnE_realizeMetricAt_sub_funext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramOnE_realizeMetricAt_sub_funext ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramOnE_realizeMetricAt_sub_funext

omit [BoundarylessManifold I M] in
theorem chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α
          ((extChartAt I α).symm y) l b -
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α
          ((extChartAt I α).symm y) l b =
      reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y := by
  rw [reprDiffChartCompOnE]
  exact chartGramMatrix_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂
    α ((extChartAt I α).symm y) l b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp

omit [BoundarylessManifold I M] in
theorem partialDeriv_chartGramOnE_realizeMetricAt_sub_eq
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
        (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
        (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
        (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y := by
  rw [← chartGramOnE_realizeMetricAt_sub_funext (I := I) g_bg hu₁ hu₂ α l b]
  rw [DifferentialGeometry.Tensor.Coordinates.partialDeriv, DifferentialGeometry.Tensor.Coordinates.partialDeriv, DifferentialGeometry.Tensor.Coordinates.partialDeriv, ← sub_apply]
  congr 1
  exact (fderiv_sub
    (chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b hy)
    (chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b hy)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_chartGramOnE_realizeMetricAt_sub_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_chartGramOnE_realizeMetricAt_sub_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_chartGramOnE_realizeMetricAt_sub_eq ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv_chartGramOnE_realizeMetricAt_sub_eq

omit [BoundarylessManifold I M] in
theorem partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (c a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b)) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b)) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y := by
  have hop : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have h_eqOn : Set.EqOn
      (fun z => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z)
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b))
      (interior ((extChartAt I α).target : Set E)) := by
    intro z hz
    exact partialDeriv_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂ α a l b hz
  rw [DifferentialGeometry.Tensor.Coordinates.partialDeriv, DifferentialGeometry.Tensor.Coordinates.partialDeriv, DifferentialGeometry.Tensor.Coordinates.partialDeriv, ← sub_apply]
  have hfd_sub :
      fderiv ℝ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b)) y -
        fderiv ℝ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b)) y =
      fderiv ℝ (fun z => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
            (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
            (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z) y :=
    (fderiv_sub
      (partialDeriv_chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₁)
        α a l b hy)
      (partialDeriv_chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₂)
        α a l b hy)).symm
  rw [hfd_sub]
  have hev : (fun z => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z)
      =ᶠ[nhds y]
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior ((extChartAt I α).target : Set E), hop.mem_nhds hy, h_eqOn⟩
  rw [hev.fderiv_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace in
def iteratedCovGradJetSum (g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g_bg 0 2) (x : M) : ℝ :=
  ∑ j ∈ Finset.range 3,
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g_bg 0 (2 + j)
    ‖(iteratedCovGrad (I := I) (M := M) g_bg 0 2 j S).toSection x‖)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace in
omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGradJetSum_nonneg (g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g_bg 0 2) (x : M) :
    0 ≤ iteratedCovGradJetSum (I := I) g_bg S x := by
  rw [iteratedCovGradJetSum]
  refine Finset.sum_nonneg (fun j _ => ?_)
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g_bg 0 (2 + j)
  exact norm_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_nonneg

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace in
omit [BoundarylessManifold I M] in
theorem iteratedCovGradJetSum_le_toHs (g_bg : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SmoothCcTensor g_bg 0 2) (x : M),
      iteratedCovGradJetSum (I := I) g_bg S x ≤
        C * ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) S‖ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_singleNorm (I := I) (M := M) g_bg k h_super
  refine ⟨C, hC_pos, fun S x => ?_⟩
  rw [iteratedCovGradJetSum]
  exact hC S x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_le_toHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_le_toHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_le_toHs ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.iteratedCovGradJetSum_le_toHs

omit [BoundarylessManifold I M] in
theorem chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hKsub : K ⊆ interior ((extChartAt I α).target : Set E))
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hcovgrad_jet_bound : ∀ y ∈ K, ∀ l b : Fin (Module.finrank ℝ E),
      |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y| ≤
          C₀ * iteratedCovGradJetSum (I := I) g_bg
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
            ((extChartAt I α).symm y) ∧
        (∀ a : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y)) ∧
        (∀ c a : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
        C * iteratedCovGradJetSum (I := I) g_bg
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
          ((extChartAt I α).symm y) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  set Ncard : ℝ := (Fintype.card ((Fin n) × (Fin n)) : ℝ)
    + (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ)
    + (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) with hNcard_def
  have hNcard_nn : 0 ≤ Ncard := by
    rw [hNcard_def]; positivity
  refine ⟨C₀ * Ncard, mul_nonneg hC₀ hNcard_nn, ?_⟩
  intro y hy
  set R : ℝ := iteratedCovGradJetSum (I := I) g_bg S ((extChartAt I α).symm y) with hR_def
  have hR_nn : 0 ≤ R := iteratedCovGradJetSum_nonneg (I := I) g_bg S _
  have h0 : chartGramDiffSup (I := I) (M := M)
        (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α
        ((extChartAt I α).symm y) ≤
      (Fintype.card ((Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
    rw [chartGramDiffSup, matrixEntryL1]
    calc ∑ pq : (Fin n) × (Fin n),
            |(DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α
                  ((extChartAt I α).symm y) -
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α
                  ((extChartAt I α).symm y)) pq.1 pq.2|
        = ∑ pq : (Fin n) × (Fin n),
            |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α pq.1 pq.2 y| := by
          refine Finset.sum_congr rfl (fun pq _ => ?_)
          rw [Matrix.sub_apply]
          rw [chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp (I := I) g_bg hu₁ hu₂
            α pq.1 pq.2 y]
      _ ≤ ∑ _pq : (Fin n) × (Fin n), C₀ * R :=
          Finset.sum_le_sum (fun pq _ => (hcovgrad_jet_bound y hy pq.1 pq.2).1)
      _ = (Fintype.card ((Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h1 : chartGramPartialDiffSup (I := I) (M := M)
        (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
      (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
    rw [chartGramPartialDiffSup]
    calc ∑ p : (Fin n) × (Fin n) × (Fin n),
            gramPartialDiffEntry (I := I) (M := M)
              (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y p
        = ∑ p : (Fin n) × (Fin n) × (Fin n),
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α p.1 p.2.2) y| := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [gramPartialDiffEntry,
            partialDeriv_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂
              α p.2.1 p.1 p.2.2 (hKsub hy)]
      _ ≤ ∑ _p : (Fin n) × (Fin n) × (Fin n), C₀ * R :=
          Finset.sum_le_sum (fun p _ => (hcovgrad_jet_bound y hy p.1 p.2.2).2.1 p.2.1)
      _ = (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h2 : chartGramPartial2DiffSup (I := I) (M := M)
        (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
      (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
    rw [chartGramPartial2DiffSup]
    calc ∑ p : (Fin n) × (Fin n) × (Fin n) × (Fin n),
            gramPartial2DiffEntry (I := I) (M := M)
              (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y p
        = ∑ p : (Fin n) × (Fin n) × (Fin n) × (Fin n),
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α p.2.2.1 p.2.2.2)) y| := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [gramPartial2DiffEntry,
            partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂
              α p.1 p.2.1 p.2.2.1 p.2.2.2 (hKsub hy)]
      _ ≤ ∑ _p : (Fin n) × (Fin n) × (Fin n) × (Fin n), C₀ * R :=
          Finset.sum_le_sum (fun p _ =>
            (hcovgrad_jet_bound y hy p.2.2.1 p.2.2.2).2.2 p.1 p.2.1)
      _ = (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [chartMetricJet2DiffSup, chartMetricJet1DiffSup]
  calc chartGramDiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α
          ((extChartAt I α).symm y)
        + chartGramPartialDiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y
        + chartGramPartial2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y
      ≤ (Fintype.card ((Fin n) × (Fin n)) : ℝ) * (C₀ * R)
          + (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R)
          + (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
        gcongr
    _ = C₀ * Ncard * R := by rw [hNcard_def]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum

omit [BoundarylessManifold I M] in
theorem chartMetricJet2DiffSup_realizeMetricAt_le_toHs_of_covariant_jet_bound
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : TensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁)
      (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hKsub : K ⊆ interior ((extChartAt I α).target : Set E))
    (k : ℕ) (h_super : 2 * k > Module.finrank ℝ E + 4)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hcovgrad_jet_bound : ∀ y ∈ K, ∀ l b : Fin (Module.finrank ℝ E),
      |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y| ≤
          C₀ * iteratedCovGradJetSum (I := I) g_bg
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
            ((extChartAt I α).symm y) ∧
        (∀ a : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y)) ∧
        (∀ c a : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
        C * ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k)
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)‖ := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum (I := I) g_bg hu₁ hu₂
      α hKsub hC₀ hcovgrad_jet_bound
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    iteratedCovGradJetSum_le_toHs (I := I) g_bg k h_super
  refine ⟨C₁ * C₂, mul_nonneg hC₁_nn hC₂_pos.le, ?_⟩
  intro y hy
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  calc chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y
      ≤ C₁ * iteratedCovGradJetSum (I := I) g_bg S ((extChartAt I α).symm y) := hC₁ y hy
    _ ≤ C₁ * (C₂ * N) :=
        mul_le_mul_of_nonneg_left (hC₂ S ((extChartAt I α).symm y)) hC₁_nn
    _ = C₁ * C₂ * N := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_toHs_of_covariant_jet_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_toHs_of_covariant_jet_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_toHs_of_covariant_jet_bound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.chartMetricJet2DiffSup_realizeMetricAt_le_toHs_of_covariant_jet_bound

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
