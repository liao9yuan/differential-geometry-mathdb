import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.IntrinsicComponent
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
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
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def covDerivLowerOrderCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (∑ k : Fin r,
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          (if Jdx' = Jdx then (1 : ℝ) else 0))
      - ∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma covDerivLowerOrderCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx' y =
      (∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0))
        - ∑ l : Fin s,
            outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
              (if Idx' = Idx then (1 : ℝ) else 0) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_def

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivLowerOrderCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hinput : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine ContDiffOn.sum (fun k _ => ?_)
    exact (inputSlotCoeff_contDiffOn (I := I) (M := M) g r α m k Idx Idx').mul
      contDiffOn_const
  have houtput : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine ContDiffOn.sum (fun l _ => ?_)
    exact (outputSlotCoeff_contDiffOn (I := I) (M := M) g s α m l Jdx Jdx').mul
      contDiffOn_const
  have hsub := hinput.sub houtput
  refine hsub.congr (fun y _ => ?_)
  rw [covDerivLowerOrderCoeff_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderCoeff_contDiffOn

noncomputable def wrappedComponentProj
    (r s : ℕ) (α b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    TensorRSSpace r s I b →L[ℝ] ℝ :=
  (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
    ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma wrappedComponentProj_apply
    (r s : ℕ) (α b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T : TensorRSSpace r s I b) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx T =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          T) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_apply

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma wrappedComponentProj_intrinsic_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  rw [wrappedComponentProj_apply]
  exact tensorRSIntrinsicChartCLM_component_eq_euclidPartial
    (I := I) (M := M) g r s S α Idx Jdx m hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_intrinsic_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_intrinsic_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma wrappedComponentProj_inputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k) =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [wrappedComponentProj_apply]
  exact chartTensorRSInputSlotCorrection_component_eq
    (I := I) (M := M) g r s S α m k Idx Jdx hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_inputSlot_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_inputSlot_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma wrappedComponentProj_outputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l) =
      ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx'
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [wrappedComponentProj_apply]
  exact chartTensorRSOutputSlotCorrection_component_eq
    (I := I) (M := M) g r s S α m l Idx Jdx hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_outputSlot_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_outputSlot_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma inputSlot_sum_reindex
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (b : M) :
    (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx p.1 y *
          (if p.2 = Jdx then (1 : ℝ) else 0) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
  classical
  refine Eq.symm ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun Idx' _ => ?_)
  rw [Finset.sum_eq_single Jdx]
  · rw [if_pos rfl, mul_one]
  · intro Jdx' _ hJdx'
    rw [if_neg hJdx', _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ Jdx) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.inputSlot_sum_reindex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.inputSlot_sum_reindex target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma outputSlot_sum_reindex
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (b : M) :
    (∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx' b) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx p.2 y *
          (if p.1 = Idx then (1 : ℝ) else 0) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
  classical
  refine Eq.symm ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single Idx]
  · refine Finset.sum_congr rfl (fun Jdx' _ => ?_)
    rw [if_pos rfl, mul_one]
  · intro Idx' _ hIdx'
    refine Finset.sum_eq_zero (fun Jdx' _ => ?_)
    rw [if_neg hIdx', _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ Idx) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.outputSlot_sum_reindex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.outputSlot_sum_reindex target :: scope.openDecls } }

noncomputable def covDerivLowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
      tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma covDerivLowerOrderTerm_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_def

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma sum_inputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ k : Fin r,
        wrappedComponentProj (I := I) (M := M) r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k)) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        (∑ k : Fin r,
            inputSlotCoeff (I := I) (M := M) g r α m k Idx p.1 y *
              (if p.2 = Jdx then (1 : ℝ) else 0)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hstep : (∑ k : Fin r,
        wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b k)) =
      ∑ k : Fin r,
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          inputSlotCoeff (I := I) (M := M) g r α m k Idx p.1 y *
            (if p.2 = Jdx then (1 : ℝ) else 0) *
            tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [wrappedComponentProj_inputSlot_eq (I := I) (M := M) g r s S α m k
      Idx Jdx hy]
    exact inputSlot_sum_reindex (I := I) (M := M) g r s S α m k Idx Jdx y b
  rw [hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sum_inputSlot_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sum_inputSlot_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma sum_outputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ l : Fin s,
        wrappedComponentProj (I := I) (M := M) r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
          (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l)) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        (∑ l : Fin s,
            outputSlotCoeff (I := I) (M := M) g s α m l Jdx p.2 y *
              (if p.1 = Idx then (1 : ℝ) else 0)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hstep : (∑ l : Fin s,
        wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
          (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b l)) =
      ∑ l : Fin s,
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx p.2 y *
            (if p.1 = Idx then (1 : ℝ) else 0) *
            tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [wrappedComponentProj_outputSlot_eq (I := I) (M := M) g r s S α m l
      Idx Jdx hy]
    exact outputSlot_sum_reindex (I := I) (M := M) g r s S α m l Idx Jdx y b
  rw [hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sum_outputSlot_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sum_outputSlot_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma inputSlot_sub_outputSlot_eq_lowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ k : Fin r,
        wrappedComponentProj (I := I) (M := M) r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k))
      - (∑ l : Fin s,
          wrappedComponentProj (I := I) (M := M) r s α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
            (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l)) =
      covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y := by
  classical
  rw [sum_inputSlot_eq (I := I) (M := M) g r s S α m Idx Jdx hy,
    sum_outputSlot_eq (I := I) (M := M) g r s S α m Idx Jdx hy,
    covDerivLowerOrderTerm_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [covDerivLowerOrderCoeff_def, ← sub_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.inputSlot_sub_outputSlot_eq_lowerOrderTerm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.inputSlot_sub_outputSlot_eq_lowerOrderTerm target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma wrappedComponentProj_covDeriv_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
        (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b) =
      wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))
        + (∑ k : Fin r,
            wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
              (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b k))
        - (∑ l : Fin s,
            wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
              (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b l)) := by
  classical
  rw [chartTensorRSCovariantDerivative_def]
  rw [map_sub, map_add, map_sum, map_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_covDeriv_split
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_covDeriv_split target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
theorem covDerivComponent_eq_euclidPartial_add_lowerOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  rw [← wrappedComponentProj_apply (I := I) (M := M) r s α b Idx Jdx]
  rw [wrappedComponentProj_covDeriv_split (I := I) (M := M) g r s S α m
    Idx Jdx b]
  rw [wrappedComponentProj_intrinsic_eq (I := I) (M := M) g r s S α m
    Idx Jdx hy]
  rw [add_sub_assoc]
  rw [inputSlot_sub_outputSlot_eq_lowerOrderTerm (I := I) (M := M) g r s S α m
    Idx Jdx hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_eq_euclidPartial_add_lowerOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_eq_euclidPartial_add_lowerOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_eq_euclidPartial_add_lowerOrder ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_eq_euclidPartial_add_lowerOrder

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivComponent_lowerOrder_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (hraw : ∀ (Idx' : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hsummand : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
            tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro p
    have hcoeff : ContDiffOn ℝ ∞
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m
        Idx p.1 Jdx p.2
    have hrawfac : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine (hraw p.1 p.2).congr (fun y hy => ?_)
      exact (chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2) hy).symm
    exact hcoeff.mul hrawfac
  have hsum :
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
              tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
    ContDiffOn.sum (fun p _ => hsummand p)
  exact hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_contDiffOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem covDerivComponent_lowerOrder_eq_linearCombination
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
  covDerivLowerOrderTerm_def (I := I) (M := M) g r s S α m Idx Jdx y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_eq_linearCombination then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_eq_linearCombination"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_eq_linearCombination ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_lowerOrder_eq_linearCombination

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
