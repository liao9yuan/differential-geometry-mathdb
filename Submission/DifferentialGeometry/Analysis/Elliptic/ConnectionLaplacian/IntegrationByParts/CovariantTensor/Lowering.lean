import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Basic

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
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SNabla _root_.Submission.DifferentialGeometry.TensorRSNabla
    DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
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
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
lemma tensor0SCovariantDerivative_natCast_transport
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {a b : ℕ} (h : a = b)
    (W : Π y : M, Tensor0SSpace b I y) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M a cov
        (fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) h.symm) (W y)) x v =
      cast (congrArg (fun n => Tensor0SSpace n I x) h.symm)
        (tensor0SCovariantDerivative I M b cov W x v) := by
  subst h
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensor0SCovariantDerivative_natCast_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensor0SCovariantDerivative_natCast_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensor0SCovariantDerivative_natCast_transport ``Submission.DifferentialGeometry.Analysis.Elliptic.tensor0SCovariantDerivative_natCast_transport

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_natCast_transport
    {a b : ℕ} (h : a = b) {x : M} (T : Tensor0SSpace b I x) :
    Tensor0SSpace.toModel
        (cast (congrArg (fun n => Tensor0SSpace n I x) h.symm) T) =
      (Tensor0SSpace.toModel T).domDomCongr (finCongr h.symm) := by
  cases h
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.toModel_natCast_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.toModel_natCast_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.toModel_natCast_transport ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_natCast_transport

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma liftedTensorSection_zero_eq_natCast_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (y : M) :
    liftedTensorSection (I := I) (M := M) g 0 s S y =
      cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
        ((S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
  refine Tensor0SSpace.toModel_injective ?_
  change Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 s S y) =
    Tensor0SSpace.toModel
      (cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
        ((S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))))
  rw [toModel_natCast_transport (Nat.zero_add s)]
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [toModel_liftedTensorSection_zero_eq_apply_unit_reindex (I := I) (M := M) g s S y u]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext j
  congr 1
  exact (Fin.ext (by simp)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.liftedTensorSection_zero_eq_natCast_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.liftedTensorSection_zero_eq_natCast_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.liftedTensorSection_zero_eq_natCast_unit ``Submission.DifferentialGeometry.Analysis.Elliptic.liftedTensorSection_zero_eq_natCast_unit

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v)) := by
  classical
  let unitSec : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
    ⟨fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
      contMDiff_unitZeroSection (I := I) (M := M)⟩
  have hcoe : (fun y : M => unitSec y) =
      fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hunit_model : Tensor0SSpace.toModel (unitSec x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    change Tensor0SSpace.toModel (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = _
    rw [Tensor0SSpace.toModel_ofModel]
  have hlowerA :
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v)) =
        (Tensor0SSpace.toModel
            ((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v :
                Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
              (unitSec x))).domDomCongr (finCongr (Nat.zero_add s).symm) := by
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v) (unitSec x)]
    rw [hunit_model]
    rw [lowerAllUpperIndices_apply, separableFormAt_zero]
    congr 1
    funext j
    congr 1
    exact (Fin.ext (by simp)).symm
  rw [hlowerA]
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) S unitSec x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitSec y) x v) = 0 from by
    rw [hcoe]
    exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]
  rw [loweredCovDerivAt_def]
  rw [show liftedTensorSection (I := I) (M := M) g 0 s S =
        (fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
          ((S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
            (Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
                (1 : ℝ))))) from by
      funext y
      exact liftedTensorSection_zero_eq_natCast_unit (I := I) (M := M) g s S y]
  rw [tensor0SCovariantDerivative_natCast_transport (LeviCivita (I := I) g)
    (Nat.zero_add s)
    (fun y : M => (S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) x v]
  rw [toModel_natCast_transport (Nat.zero_add s)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma loweringIntertwiner (g : SmoothRiemannianMetric I M) (s : ℕ) :
    LoweringIntertwiner (I := I) (M := M) g s :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor (I := I) (M := M) g s S x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner ``Submission.DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun
        (covGrad (I := I) (M := M) g 0 s v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap
    (I := I) (M := M) g s (loweringIntertwiner (I := I) (M := M) g s) T v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor

end Elliptic
end Analysis
end DifferentialGeometry

end
