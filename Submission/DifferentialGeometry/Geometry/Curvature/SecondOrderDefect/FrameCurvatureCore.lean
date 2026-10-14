import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.FrozenFrameTrace
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] in
theorem frame_offDiag_curvature_sum_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (∑ i : Fin (Module.finrank ℝ E),
            riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
        ((Module.finrank ℝ E : ℝ)) ^ 2 * Cx *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  classical
  obtain ⟨Cx, hCx_nonneg, hpair⟩ :=
    riemannOp_gradTensor_offDiag_frame_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨Cx, hCx_nonneg, ?_⟩
  set rS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) with hrS_def
  set F : Fin (Module.finrank ℝ E) → TensorRSSpace 0 3 I x := fun i =>
    riemannOp (tensorCov (I := I) g 0 3) x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) with hF_def
  have hsum_le :
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (∑ i : Fin (Module.finrank ℝ E), F i) ≤
        ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) :=
    riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 3 x Finset.univ F
  have hper_le :
      ∑ i : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) ≤
        ∑ _i : Fin (Module.finrank ℝ E), Cx * rS :=
    Finset.sum_le_sum (fun i _ => hpair i a)
  have hcard : ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) =
      (Module.finrank ℝ E : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hconst_sum : (∑ _i : Fin (Module.finrank ℝ E), Cx * rS) =
      (Module.finrank ℝ E : ℝ) * (Cx * rS) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x (∑ i : Fin (Module.finrank ℝ E), F i)
        ≤ ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
            ∑ i : Fin (Module.finrank ℝ E),
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) := hsum_le
    _ ≤ ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
          (∑ _i : Fin (Module.finrank ℝ E), Cx * rS) := by
        refine mul_le_mul_of_nonneg_left hper_le ?_
        rw [hcard]; positivity
    _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (Cx * rS)) := by
        rw [hcard, hconst_sum]
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * Cx * rS := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_offDiag_curvature_sum_fiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_offDiag_curvature_sum_fiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_offDiag_curvature_sum_fiberNormSq_le ``Submission.DifferentialGeometry.Geometry.Curvature.frame_offDiag_curvature_sum_fiberNormSq_le

omit [CompactSpace M] in
theorem exists_frame_offDiag_curvature_sum_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (∑ i : Fin (Module.finrank ℝ E),
            riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    frame_offDiag_curvature_sum_fiberNormSq_le (I := I) (M := M) g T₀ x a
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * Cx, ?_, hbound⟩
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_frame_offDiag_curvature_sum_fiberNormSq_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_frame_offDiag_curvature_sum_fiberNormSq_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_frame_offDiag_curvature_sum_fiberNormSq_bound ``Submission.DifferentialGeometry.Geometry.Curvature.exists_frame_offDiag_curvature_sum_fiberNormSq_bound

section FrozenFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem frozenFrameTrace_eq_rawTensorConnLap_fixedFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    frozenFrameTrace (I := I) g r s T x y =
      rawTensorConnLapFixedFrame (I := I) g r s (smoothOrthoFrame (I := I) g x) T y := by
  rw [frozenFrameTrace_def, rawTensorConnLap_fixedFrame_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_fixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_fixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_fixedFrame ``Submission.DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_fixedFrame

omit [CompactSpace M] [I.Boundaryless] in
theorem frozenFrameTrace_eq_rawTensorConnLap_of_mem_neighborhood
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) {y : M} (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x) :
    frozenFrameTrace (I := I) g r s T x y = rawTensorConnLap (I := I) g r s T y := by
  rw [frozenFrameTrace_eq_rawTensorConnLap_fixedFrame]
  exact (rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s T hT_total
    (B := smoothOrthoFrame (I := I) g x)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) y
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hy i j)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_of_mem_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_of_mem_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_of_mem_neighborhood ``Submission.DifferentialGeometry.Geometry.Curvature.frozenFrameTrace_eq_rawTensorConnLap_of_mem_neighborhood

omit [CompactSpace M] [I.Boundaryless] in
theorem rawTensorConnLap_eventuallyEq_frozenFrameTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    ∀ᶠ y in 𝓝 x, rawTensorConnLap (I := I) g r s T y =
      frozenFrameTrace (I := I) g r s T x y := by
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x] with y hy
  exact (frozenFrameTrace_eq_rawTensorConnLap_of_mem_neighborhood (I := I) g r s T hT_total x hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eventuallyEq_frozenFrameTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eventuallyEq_frozenFrameTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eventuallyEq_frozenFrameTrace ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eventuallyEq_frozenFrameTrace

end FrozenFrame

end Curvature
end Geometry
end DifferentialGeometry

end
