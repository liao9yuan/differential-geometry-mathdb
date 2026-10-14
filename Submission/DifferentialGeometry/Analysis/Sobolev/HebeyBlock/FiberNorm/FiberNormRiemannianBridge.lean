import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.FiberToModel
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.FiberFromModel
import Submission.DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace HebeyBlock

open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance fiberNormBridgeTensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.fiberNormBridgeTensorRSRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.fiberNormBridgeTensorRSRiemannianNormedAddCommGroup target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem triv_eq_toModel_at_chartCenter
    (r s : ℕ) (b₀ : M) (T : TensorRSSpace r s I b₀) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b₀ T =
      TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T := by
  ext D_α
  have h_local :=
    tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
      (I := I) (M := M) r s b₀
      (h_chart := rfl) (h_source := mem_chart_source H b₀) T D_α
  simp only [TensorRSSpace.toModel, tensorRSSpaceContinuousLinearEquiv]
  rw [h_local]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.triv_eq_toModel_at_chartCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.triv_eq_toModel_at_chartCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.triv_eq_toModel_at_chartCenter ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.triv_eq_toModel_at_chartCenter


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem symmL_toModel_eq_self_at_chartCenter
    (r s : ℕ) (b₀ : M) (T : TensorRSSpace r s I b₀) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).symmL ℝ b₀
          (TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T) = T := by
  have h_mem : b₀ ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet :=
    ⟨mem_baseSet_trivializationAt _ _ b₀, _root_.FiberBundle.mem_baseSet_trivializationAt _ _ b₀⟩
  rw [← triv_eq_toModel_at_chartCenter (I := I) r s b₀ T]
  exact Trivialization.symmL_continuousLinearMapAt
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀) h_mem T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.symmL_toModel_eq_self_at_chartCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.symmL_toModel_eq_self_at_chartCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.symmL_toModel_eq_self_at_chartCenter ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.symmL_toModel_eq_self_at_chartCenter

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem modelNorm_le_gNorm_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧ ∀ T : TensorRSSpace r s I x₀,
      ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ ≤ C * ‖T‖ := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s x₀ isCompact_singleton
      (Set.singleton_subset_iff.mpr (mem_chart_source H x₀))
  refine ⟨C₀, hC₀_pos, fun T => ?_⟩
  have h_triv := hC₀_bound x₀ (Set.mem_singleton x₀) T
  rw [triv_eq_toModel_at_chartCenter (I := I) r s x₀ T] at h_triv
  exact h_triv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.modelNorm_le_gNorm_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.modelNorm_le_gNorm_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.modelNorm_le_gNorm_pointwise ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.modelNorm_le_gNorm_pointwise

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gNorm_le_modelNorm_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace r s I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨D₀, hD₀_pos, hD₀_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s x₀ isCompact_singleton
      (Set.singleton_subset_iff.mpr (mem_chart_source H x₀))
  refine ⟨D₀, hD₀_pos, fun T => ?_⟩
  have h_inv := hD₀_bound x₀ (Set.mem_singleton x₀)
    (TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T)
  rw [symmL_toModel_eq_self_at_chartCenter (I := I) r s x₀ T] at h_inv
  exact h_inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.gNorm_le_modelNorm_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.gNorm_le_modelNorm_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.gNorm_le_modelNorm_pointwise ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.gNorm_le_modelNorm_pointwise

end HebeyBlock
end Sobolev
end Analysis
end DifferentialGeometry

end
