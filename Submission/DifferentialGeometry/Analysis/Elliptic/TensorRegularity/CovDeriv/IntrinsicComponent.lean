import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCurryFactor
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorRSChartE_section_repr_eq_tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tensorRSChartESectionRepr (I := I) r s α S.toSection =
      tensorTrivProj (I := I) (M := M) g r s S α :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSChartE_section_repr_eq_tensorTrivProj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSChartE_section_repr_eq_tensorTrivProj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSChartE_section_repr_eq_tensorTrivProj ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSChartE_section_repr_eq_tensorTrivProj

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorRSIntrinsicChartCLM_proj_eq_fderiv_component
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source)
    (hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (v : TangentSpace I b) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection b v)) =
      fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b v) := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hb_baseRS : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α S.toSection b v]
  unfold tensorRSChartFiberFromModel
  rw [(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
      (R := ℝ) hb_baseRS]
  rw [tensorRSChartE_section_repr_eq_tensorTrivProj (I := I) (M := M) g r s S α]
  rw [tensorChartComponentRaw_partial_decomp (I := I) (M := M) g r s α S
    hb_chart hb_int Idx Jdx (trivToE (I := I) α b v)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_proj_eq_fderiv_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_proj_eq_fderiv_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_proj_eq_fderiv_component ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_proj_eq_fderiv_component

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorRSIntrinsicChartCLM_component_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))) =
      euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  rw [tensorRSIntrinsicChartCLM_proj_eq_fderiv_component (I := I) (M := M)
    g r s S α Idx Jdx hb_chart hb_int (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)]
  have htriv_basis :
      trivToE (I := I) α b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)) = _
    exact trivToE_trivFromE (I := I) α hb_base (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
  rw [htriv_basis, DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply, hphi_b]
  rw [euclidPartial_def]
  have hpushed_eq :
      chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) =ᶠ[𝓝 y]
        ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hz
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
      (extChartAt I α).symm) (x := y)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_component_eq_euclidPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_component_eq_euclidPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_component_eq_euclidPartial ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorRSIntrinsicChartCLM_component_eq_euclidPartial

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
