import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartKernelCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
  (chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartKernelCutoff_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartKernelCutoff_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartKernelCutoff_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartKernelCutoff_contMDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_contDiff_of_contDiff
    {u : EuclN → ℝ} (hu : ContDiff ℝ ∞ u) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k u) := by
  have hfd : ContDiff ℝ ∞ (fun z => fderiv ℝ u z) :=
    hu.fderiv_right (m := (∞ : WithTop ℕ∞))
      (by rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl])
  have hcomp : euclidPartial (E := E) k u =
      (fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) ∘
        (fun z => fderiv ℝ u z) := by
    funext z; rw [euclidPartial_def]; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single k 1)).contDiff.comp hfd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_contDiff_of_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_contDiff_of_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_contDiff_of_contDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_contDiff_of_contDiff

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentEuclid_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (cutoffComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_contDiff target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact
    chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_hasCompactSupport target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact
    tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_tsupport_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_tsupport_subset target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartialOrZero_cutoffComponentEuclid_ae_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    cutoffComponentEuclid_contDiff (I := I) (M := M) g r s S α Idx Jdx
  have hu_compact : HasCompactSupport u :=
    cutoffComponentEuclid_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffComponentEuclid_tsupport_subset (I := I) (M := M) g r s S α Idx Jdx
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2 u (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open hu_smooth hu_compact hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial_smooth_ae_eq
      (d := Module.finrank ℝ E) hp_one hΩ_open hu_smooth hu_W1p k
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [euclidPartial_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_ae_eq_euclidPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_ae_eq_euclidPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_ae_eq_euclidPartial ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_ae_eq_euclidPartial

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartPushedRaw_rawComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (I := I) (M := M) g r s S α Idx Jdx).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_rawComponent_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_rawComponent_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_rawComponent_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_rawComponent_continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_chartPushedRaw_rawComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_chartPushedRaw_contDiffOn
    (I := I) (M := M) g r s S α k Idx Jdx).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_chartPushedRaw_rawComponent_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_chartPushedRaw_rawComponent_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_chartPushedRaw_rawComponent_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_chartPushedRaw_rawComponent_continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffComponentEuclid_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) :=
  (cutoffComponentEuclid_contDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_continuous ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_continuous

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
