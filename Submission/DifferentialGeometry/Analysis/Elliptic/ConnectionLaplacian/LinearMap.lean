import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def rawConnLapLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] SmoothCcTensor g r s where
  toFun T := rawTensorConnLapSmooth (I := I) g r s T
  map_add' T₁ T₂ := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    have hsum :=
      tensorConnLaplacian_of_contMDiff_add (I := I) g r s T₁ T₂
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => T₁.toSection z) T₁.toSection.contMDiff_toFun)
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => T₂.toSection z) T₂.toSection.contMDiff_toFun)
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => (T₁ + T₂).toSection z)
          (T₁ + T₂).toSection.contMDiff_toFun) x
    have hLHS :
        (rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂)).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s (T₁ + T₂)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (T₁ + T₂).toSection z)
              (T₁ + T₂).toSection.contMDiff_toFun)).toSection x := rfl
    have hRHS₁ :
        (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s T₁
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₁.toSection z)
              T₁.toSection.contMDiff_toFun)).toSection x := rfl
    have hRHS₂ :
        (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s T₂
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₂.toSection z)
              T₂.toSection.contMDiff_toFun)).toSection x := rfl
    have hsum_section :
        (rawTensorConnLapSmooth (I := I) g r s T₁ +
            rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x +
            (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x := by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
      rfl
    rw [hLHS, hsum_section, hRHS₁, hRHS₂]
    exact hsum
  map_smul' c T := by
    change rawTensorConnLapSmooth (I := I) g r s (c • T) =
      c • rawTensorConnLapSmooth (I := I) g r s T
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    have hsmul :=
      tensorConnLaplacian_of_contMDiff_smul (I := I) g r s c T
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => T.toSection z) T.toSection.contMDiff_toFun)
        (rawTensorConnLap_contMDiff (I := I) g r s
          (fun z : M => (c • T).toSection z)
          (c • T).toSection.contMDiff_toFun) x
    have hLHS :
        (rawTensorConnLapSmooth (I := I) g r s (c • T)).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s (c • T)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (c • T).toSection z)
              (c • T).toSection.contMDiff_toFun)).toSection x := rfl
    have hRHS :
        (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s T
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T.toSection z)
              T.toSection.contMDiff_toFun)).toSection x := rfl
    have hsmul_section :
        (c • rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          c • (rawTensorConnLapSmooth (I := I) g r s T).toSection x := by
      rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
      rfl
    rw [hLHS, hsmul_section, hRHS]
    exact hsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawConnLapLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawConnLapLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawConnLapLin ``Submission.DifferentialGeometry.Analysis.Elliptic.rawConnLapLin

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem rawConnLapLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawConnLapLin (I := I) g r s T =
      rawTensorConnLapSmooth (I := I) g r s T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawConnLapLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawConnLapLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawConnLapLin_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.rawConnLapLin_apply

end Elliptic
end Analysis
end DifferentialGeometry

end
