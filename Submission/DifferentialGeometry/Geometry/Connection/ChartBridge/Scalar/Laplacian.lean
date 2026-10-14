import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

noncomputable def hessTensorAt
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    Tensor0SSpace (E := E) (H := H) (I := I) (M := M) 2 x := by
  let _ : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  exact
    (((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap).comp
      (hessFun (I := I) g f x).toContinuousBilinearMap).uncurryLeft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.hessTensorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.hessTensorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.hessTensorAt ``Submission.DifferentialGeometry.Geometry.Connection.hessTensorAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem hessTensorAt_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    hessTensorAt (I := I) g f x (vec2 (I := I) v w) =
      hessFun (I := I) g f x v w := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.hessTensorAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.hessTensorAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.hessTensorAt_apply ``Submission.DifferentialGeometry.Geometry.Connection.hessTensorAt_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lap_eq_hess_on [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} {x : M}
    (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hx : x ∈ U) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g f x) := by
  classical
  let basis :
      Module.Basis (CoordinateIdx (𝕜 := ℝ) E) ℝ (TangentSpace I x) :=
    coordinateFrameAtToBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := ℝ) E → CoordinateIdx (𝕜 := ℝ) E → ℝ :=
    fun i j =>
      inverseMetricFlatModelInChartComponent (I := I) g x i j
        (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) g x basis gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  unfold laplacian divergence
  rw [linearMap_trace_eq_sum_inv_inner_apply
    (I := I) g x basis gInv hinv
    ((LeviCivita (I := I) g).toFun
      (fun y => gradientFun (I := I) g f y) x).toLinearMap]
  rw [metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv (hessTensorAt (I := I) g f x)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hessTensorAt_apply]
  rw [hessFun_eq_cov_local (I := I) g hU hf hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.lap_eq_hess_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.lap_eq_hess_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.lap_eq_hess_on ``Submission.DifferentialGeometry.Geometry.Connection.lap_eq_hess_on

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem laplacian_eq_chart_hessian_trace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          chartHessianTensor (I := I) g α f i j x := by
  classical
  have hbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hbase
  let gInv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g α x i j
  have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
    intro i j
    constructor
    · have hmatrix := congrArg (fun A => A i j)
        (chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, basis, gInv,
        chartBasisFamily_apply] using hmatrix
    · have hmatrix := congrArg (fun A => A i j)
        (chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, basis, gInv,
        chartBasisFamily_apply] using hmatrix
  rw [lap_eq_hess_on (I := I) g isOpen_univ hf.contMDiffOn (Set.mem_univ x)]
  rw [metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv (hessTensorAt (I := I) g f x)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hessTensorAt_apply]
  rw [hessFun_eq_cov_local (I := I) g isOpen_univ hf.contMDiffOn
    (Set.mem_univ x)]
  rw [abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf]
  dsimp only [gInv, basis]
  rw [chartBasisFamily_apply, chartBasisFamily_apply]
  rw [chartAlphaMatrixIdentity_holds (I := I) g α hf hx i j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.laplacian_eq_chart_hessian_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.laplacian_eq_chart_hessian_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.laplacian_eq_chart_hessian_trace ``Submission.DifferentialGeometry.Geometry.Connection.laplacian_eq_chart_hessian_trace

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem connLaplacian_function_eq_chartLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacianFunction (I := I) g hf x = ΔG (I := I) g ⟨_, hf⟩ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartLaplacian ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartLaplacian

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem traceFun_abstractHessian_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      ΔG (I := I) g ⟨_, hf⟩ x := by
  classical
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h1 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  have h2 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x :=
    traceFun_hessFun_eq_chartHessTrace_of_orthonormal (I := I) g f x h_orth
  have h3 : chartHessTrace (I := I) g f x = ΔG (I := I) g ⟨_, hf⟩ x :=
    chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x
  rw [← h1, h2, h3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_laplacian ``Submission.DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_laplacian

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem traceFun_abstractHessian_eq_connLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      connLaplacianFunction (I := I) g hf x := by
  rw [connLaplacian_function_eq_chartLaplacian (I := I) g hf x]
  exact traceFun_abstractHessian_eq_laplacian (I := I) g hf x h_orth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_connLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_connLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_connLaplacian ``Submission.DifferentialGeometry.Geometry.Connection.traceFun_abstractHessian_eq_connLaplacian

end Connection
end Geometry
end DifferentialGeometry
