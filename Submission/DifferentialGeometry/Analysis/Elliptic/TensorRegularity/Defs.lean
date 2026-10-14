import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def euclidPartial (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  fderiv ℝ u y (EuclideanSpace.single i 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma euclidPartial_def (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    euclidPartial (E := E) i u y = fderiv ℝ u y (EuclideanSpace.single i 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_def

def chartInvGramEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartInvGramOnE (I := I) g α k l (toEuclidean.symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma chartInvGramEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartInvGramEuclid (I := I) g α k l y =
      chartInvGramOnE (I := I) g α k l (toEuclidean.symm y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_def

def chartChristoffelEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartChristoffel (I := I) g α k l m (toEuclidean.symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma chartChristoffelEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartChristoffelEuclid (I := I) g α k l m y =
      chartChristoffel (I := I) g α k l m (toEuclidean.symm y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_def

def weightedInvGramEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartDensityOnE (I := I) g α (toEuclidean.symm y) *
      chartInvGramEuclid (I := I) g α k l y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma weightedInvGramEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    weightedInvGramEuclid (I := I) g α k l y =
      chartDensityOnE (I := I) g α (toEuclidean.symm y) *
        chartInvGramEuclid (I := I) g α k l y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_def

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma toEuclidean_symm_mem_extChartAt_target
    {α : M} {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (toEuclidean.symm y : E) ∈ (extChartAt I α).target := by
  classical
  obtain ⟨z, hz_mem, hz_eq⟩ := hy
  have hzy : (toEuclidean.symm y : E) = z := by
    rw [← hz_eq]
    exact toEuclidean.symm_apply_apply z
  rw [hzy]
  exact hz_mem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.toEuclidean_symm_mem_extChartAt_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.toEuclidean_symm_mem_extChartAt_target target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma extChartAt_target_eq_interior (α : M) :
    (extChartAt I α).target = interior ((extChartAt I α).target : Set E) :=
  (isOpen_extChartAt_target (I := I) α).interior_eq.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.extChartAt_target_eq_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.extChartAt_target_eq_interior target :: scope.openDecls } }

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGramEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α k l
  have hcomp :
      ContDiffOn ℝ ∞
        (chartInvGramOnE (I := I) g α k l ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartInvGramEuclid_contDiffOn

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffelEuclid (I := I) g α k l m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE_int : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α k l m)
      (interior ((extChartAt I α).target : Set E)) :=
    chartChristoffel_contDiffOn_interior (I := I) g α k l m
  have hE : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α k l m)
      (extChartAt I α).target := by
    rw [extChartAt_target_eq_interior (I := I) α]
    exact hE_int
  have hcomp :
      ContDiffOn ℝ ∞
        (chartChristoffel (I := I) g α k l m ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartChristoffelEuclid_contDiffOn

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem weightedInvGramEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramEuclid (I := I) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hdensity : ContDiffOn ℝ ∞
      (chartDensityOnE (I := I) g α ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (chartDensityOnE_contDiffOn (I := I) g α).comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  rw [show weightedInvGramEuclid (I := I) g α k l =
      fun y => (chartDensityOnE (I := I) g α ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E)) y *
        chartInvGramEuclid (I := I) g α k l y from rfl]
  exact hdensity.mul (chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_contDiffOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_contDiff
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) i u) := by
  have hfd : ContDiff ℝ ∞ (fun y => fderiv ℝ u y) :=
    hu.fderiv_right (m := ∞) (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])
  have hcomp : euclidPartial (E := E) i u =
      (fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i 1)) ∘ (fun y => fderiv ℝ u y) := by
    funext y; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single i 1)).contDiff.comp hfd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_contDiff target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_euclidPartial_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) i
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)) :=
  euclidPartial_contDiff (E := E)
    (tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_contDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_contDiff

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_euclidPartial_partial_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k
      (euclidPartial (E := E) l
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx))) :=
  euclidPartial_contDiff (E := E)
    (tensorChartComp_euclidPartial_contDiff (I := I) (M := M) g r s T α Idx Jdx l) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_partial_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_partial_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_partial_contDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_partial_contDiff

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComp_euclidPartial_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (euclidPartial (E := E) m
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)) := by
  classical
  have hcs : HasCompactSupport
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  have hfd : HasCompactSupport (fun y => fderiv ℝ
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) :=
    hcs.fderiv ℝ
  have hsubset : (Function.support (euclidPartial (E := E) m
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx))) ⊆
      tsupport (fun y => fderiv ℝ
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) := by
    intro y hy
    apply subset_tsupport _
    rw [Function.mem_support] at hy ⊢
    intro hcontra
    apply hy
    rw [euclidPartial_def, hcontra]
    rfl
  exact HasCompactSupport.of_support_subset_isCompact hfd hsubset

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComp_euclidPartial_hasCompactSupport target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma hasCompactSupport_finset_sum
    {ι : Type*} {β : Type*} [AddCommMonoid β]
    {s : Finset ι}
    {f : ι → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → β}
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a t ha ih =>
    have hsum_eq : (fun y => ∑ i ∈ _root_.Insert.insert a t, f i y) =
        (fun y => f a y + ∑ i ∈ t, f i y) := by
      funext y
      rw [Finset.sum_insert ha]
    rw [hsum_eq]
    refine HasCompactSupport.add ?_ ?_
    · exact hf a (Finset.mem_insert_self a t)
    · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.hasCompactSupport_finset_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.hasCompactSupport_finset_sum target :: scope.openDecls } }

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
