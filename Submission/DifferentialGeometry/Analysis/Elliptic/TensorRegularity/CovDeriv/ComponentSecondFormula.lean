import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartWeakIdentity

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma euclidPartial_contDiffOn_chartTarget'
    (α : M) (n : Fin (Module.finrank ℝ E))
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) n u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single n 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single n 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_contDiffOn_chartTarget'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_contDiffOn_chartTarget' target :: scope.openDecls } }

noncomputable def covDerivComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    tensorChartComponentProjection (E := E) r s Idx Jdx
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma covDerivComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx y =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_def

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma covDerivComponentEuclid_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EqOn (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx)
      (fun y =>
        euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
          + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [covDerivComponentEuclid_def]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s S α m Idx Jdx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_eqOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_eqOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
theorem covDerivComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h1 : ContDiffOn ℝ ∞
      (euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
  have h2 : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')
  have hsum := h1.add h2
  refine hsum.congr (fun y hy => ?_)
  exact covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α S m Idx Jdx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponentEuclid_contDiffOn

noncomputable def rawComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma rawComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx y =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_def

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma rawComponentEuclid_eqOn_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EqOn (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx)
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [rawComponentEuclid_def]
  exact (chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_eqOn_chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_eqOn_chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_eqOn_chartPushed ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_eqOn_chartPushed

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem rawComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h := chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (I := I) (M := M) g r s S α Idx Jdx
  refine h.congr (fun y hy => ?_)
  exact rawComponentEuclid_eqOn_chartPushed (I := I) (M := M)
    g r s α S Idx Jdx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rawComponentEuclid_contDiffOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_rawComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) n
        (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_chartTarget' (I := I) (M := M) α n
    (rawComponentEuclid_contDiffOn (I := I) (M := M) g r s α S Idx Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_contDiffOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma euclidPartial_rawComponentEuclid_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EqOn (euclidPartial (E := E) n
        (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx))
      (euclidPartial (E := E) n
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y hy
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have heq : _root_.Set.EqOn (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx)
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
    rawComponentEuclid_eqOn_chartPushed (I := I) (M := M) g r s α S Idx Jdx
  have hfderiv : fderiv ℝ
      (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx) y =
    fderiv ℝ
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y :=
    Filter.EventuallyEq.fderiv_eq
      (heq.eventuallyEq_of_mem (hopen.mem_nhds hy))
  rw [euclidPartial_def, euclidPartial_def, hfderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_eqOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_rawComponentEuclid_eqOn

noncomputable def lowerOrderSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E))) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
      rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma lowerOrderSummand_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E)))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p y =
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
        rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_def

omit [CompleteSpace E] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lowerOrderSummand_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E))) :
    ContDiffOn ℝ ∞ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1 Jdx p.2).mul
    (rawComponentEuclid_contDiffOn (I := I) (M := M) g r s α S p.1 p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.lowerOrderSummand_contDiffOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p y := by
  rw [covDerivLowerOrderTerm_def]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_eq_sum_lowerOrderSummand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_eq_sum_lowerOrderSummand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_eq_sum_lowerOrderSummand ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm_eq_sum_lowerOrderSummand

noncomputable def secondCovDerivLOGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOGradCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOGradCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOGradCoeff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOGradCoeff

noncomputable def secondCovDerivLOValueCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m n : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  euclidPartial (E := E) n
    (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOValueCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOValueCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOValueCoeff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLOValueCoeff

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovDerivLO_gradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDerivLOGradCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) :=
  covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_gradCoeff_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_gradCoeff_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_gradCoeff_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_gradCoeff_contDiffOn

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovDerivLO_valueCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m n : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDerivLOValueCoeff (I := I) (M := M) g r s α m n Idx Idx' Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_chartTarget' (I := I) (M := M) α n
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_valueCoeff_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_valueCoeff_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_valueCoeff_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.secondCovDerivLO_valueCoeff_contDiffOn

omit [CompleteSpace E] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_lowerOrderSummand_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E)))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y =
      secondCovDerivLOValueCoeff (I := I) (M := M) g r s α m n
          Idx p.1 Jdx p.2 y *
        rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y +
      secondCovDerivLOGradCoeff (I := I) (M := M) g r s α m
          Idx p.1 Jdx p.2 y *
        euclidPartial (E := E) n
          (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcoeff : ContDiffOn ℝ ∞
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1 Jdx p.2
  have hraw : ContDiffOn ℝ ∞
      (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    rawComponentEuclid_contDiffOn (I := I) (M := M) g r s α S p.1 p.2
  have hcoeff_diff : DifferentiableAt ℝ
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2) y := by
    have h : DifferentiableOn ℝ
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      hcoeff.differentiableOn (by norm_cast)
    exact (h.differentiableAt (hopen.mem_nhds hy))
  have hraw_diff : DifferentiableAt ℝ
      (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y := by
    have h : DifferentiableOn ℝ
        (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      hraw.differentiableOn (by norm_cast)
    exact (h.differentiableAt (hopen.mem_nhds hy))
  have hleib := euclidPartial_mul (E := E) n hcoeff_diff hraw_diff
  rw [show lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p =
      (fun z =>
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 z *
          rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 z) from rfl]
  rw [hleib]
  unfold secondCovDerivLOValueCoeff secondCovDerivLOGradCoeff
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_lowerOrderSummand_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_lowerOrderSummand_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_lowerOrderSummand_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_lowerOrderSummand_apply

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma euclidPartial_covDerivComponentEuclid_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
      euclidPartial (E := E) n
        (fun y' =>
          euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y'
            + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y') y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have heq := covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α S m Idx Jdx
  have hfderiv : fderiv ℝ
      (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
    fderiv ℝ
      (fun y' =>
        euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y'
          + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y') y :=
    Filter.EventuallyEq.fderiv_eq
      (heq.eventuallyEq_of_mem (hopen.mem_nhds hy))
  rw [euclidPartial_def, euclidPartial_def, hfderiv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_covDerivComponentEuclid_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_covDerivComponentEuclid_eq target :: scope.openDecls } }

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_sum_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (fun y' =>
          euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y'
            + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y') y =
      euclidPartial (E := E) n
          (euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y
        + euclidPartial (E := E) n
            (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h1 : ContDiffOn ℝ ∞
      (euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
  have h2 : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')
  have h1_diff : DifferentiableAt ℝ
      (euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y := by
    have hd : DifferentiableOn ℝ
        (euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h1.differentiableOn (by norm_cast)
    exact (hd.differentiableAt (hopen.mem_nhds hy))
  have h2_diff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y := by
    have hd : DifferentiableOn ℝ
        (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h2.differentiableOn (by norm_cast)
    exact (hd.differentiableAt (hopen.mem_nhds hy))
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def]
  rw [fderiv_fun_add h1_diff h2_diff]
  rw [add_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_sum_split
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_sum_split target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_covDerivLowerOrderTerm_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        euclidPartial (E := E) n
          (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have heq : _root_.Set.EqOn (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (fun z =>
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro z _
    exact covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
      (I := I) (M := M) g r s α S m Idx Jdx z
  have hfderiv : fderiv ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y =
    fderiv ℝ
      (fun z =>
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p z) y :=
    Filter.EventuallyEq.fderiv_eq
      (heq.eventuallyEq_of_mem (hopen.mem_nhds hy))
  have hsummand_diff : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      DifferentiableAt ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y := by
    intro p
    have h := lowerOrderSummand_contDiffOn (I := I) (M := M) g r s α S m Idx Jdx p
    have hd : DifferentiableOn ℝ
        (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h.differentiableOn (by norm_cast)
    exact hd.differentiableAt (hopen.mem_nhds hy)
  have hfsum :
      fderiv ℝ
        (fun z =>
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p z) y =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          fderiv ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y :=
    fderiv_fun_sum (fun p _ => hsummand_diff p)
  rw [euclidPartial_def, hfderiv, hfsum]
  rw [show (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          fderiv ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y)
        (EuclideanSpace.single n 1) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        fderiv ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y
          (EuclideanSpace.single n 1) by
    rw [sum_apply]]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_covDerivLowerOrderTerm_eq_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_covDerivLowerOrderTerm_eq_sum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
theorem covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
      euclidPartial (E := E) n
          (euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y
        + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            secondCovDerivLOValueCoeff (I := I) (M := M) g r s α m n
                Idx p.1 Jdx p.2 y *
              rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y)
        + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            secondCovDerivLOGradCoeff (I := I) (M := M) g r s α m
                Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) n
                (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y) := by
  classical
  rw [euclidPartial_covDerivComponentEuclid_eq (I := I) (M := M)
    g r s α S m n Idx Jdx hy]
  rw [euclidPartial_sum_split (I := I) (M := M) g r s α S m n Idx Jdx hy]
  rw [euclidPartial_covDerivLowerOrderTerm_eq_sum (I := I) (M := M)
    g r s α S m n Idx Jdx hy]
  rw [show
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          euclidPartial (E := E) n
            (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y) =
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          (secondCovDerivLOValueCoeff (I := I) (M := M) g r s α m n
                Idx p.1 Jdx p.2 y *
              rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y +
            secondCovDerivLOGradCoeff (I := I) (M := M) g r s α m
                Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) n
                (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y)) by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact euclidPartial_lowerOrderSummand_apply (I := I) (M := M)
      g r s α S m n Idx Jdx p hy]
  rw [Finset.sum_add_distrib]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
theorem covDerivComponent_second_existential
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (valueCoeff gradCoeff :
        (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) →
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ p, ContDiffOn ℝ ∞ (valueCoeff p)
              (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ p, ContDiffOn ℝ ∞ (gradCoeff p)
              (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
          euclidPartial (E := E) n
              (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
            euclidPartial (E := E) n
                (euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y
              + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E)),
                  valueCoeff p y *
                    rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y)
              + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E)),
                  gradCoeff p y *
                    euclidPartial (E := E) n
                      (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y)) := by
  classical
  refine ⟨fun p => secondCovDerivLOValueCoeff (I := I) (M := M)
            g r s α m n Idx p.1 Jdx p.2,
          fun p => secondCovDerivLOGradCoeff (I := I) (M := M)
            g r s α m Idx p.1 Jdx p.2, ?_, ?_, ?_⟩
  · intro p
    exact secondCovDerivLO_valueCoeff_contDiffOn (I := I) (M := M)
      g r s α m n Idx p.1 Jdx p.2
  · intro p
    exact secondCovDerivLO_gradCoeff_contDiffOn (I := I) (M := M)
      g r s α m Idx p.1 Jdx p.2
  · intro y hy
    exact covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder
      (I := I) (M := M) g r s α S m n Idx Jdx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_existential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_existential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_existential ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_second_existential

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
