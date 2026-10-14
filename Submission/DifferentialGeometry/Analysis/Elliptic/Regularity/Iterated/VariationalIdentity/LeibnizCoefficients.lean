import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.BilinearH1Compl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedLeibnizCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def weightedInvGramMthDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _, y => weightedInvGramOnEuclid (I := I) g α i j y
  | m + 1, idx, y =>
      (fderiv ℝ
          (weightedInvGramMthDerivOnEuclid g α i j m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid

noncomputable def densityMthDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _, y => densityOnEuclid (I := I) g α y
  | m + 1, idx, y =>
      (fderiv ℝ
          (densityMthDerivOnEuclid g α m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] theorem weightedInvGramMthDerivOnEuclid_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (idx : Fin 0 → Fin (Module.finrank ℝ E)) (y : EuclN) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j 0 idx y =
      weightedInvGramOnEuclid (I := I) g α i j y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem weightedInvGramMthDerivOnEuclid_succ
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) (y : EuclN) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j (m + 1) idx y =
      (fderiv ℝ
          (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
            g α i j m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_succ ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_succ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] theorem densityMthDerivOnEuclid_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (idx : Fin 0 → Fin (Module.finrank ℝ E)) (y : EuclN) :
    densityMthDerivOnEuclid (I := I) (M := M) g α 0 idx y =
      densityOnEuclid (I := I) g α y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem densityMthDerivOnEuclid_succ
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) (y : EuclN) :
    densityMthDerivOnEuclid (I := I) (M := M) g α (m + 1) idx y =
      (fderiv ℝ
          (densityMthDerivOnEuclid (I := I) (M := M)
            g α m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_succ ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_succ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (idx : Fin 1 → Fin (Module.finrank ℝ E)) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j 1 idx =
      weightedInvGramDerivOnEuclid (I := I) g α i j (idx 0) := by
  funext y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (idx : Fin 1 → Fin (Module.finrank ℝ E)) :
    densityMthDerivOnEuclid (I := I) (M := M) g α 1 idx =
      densityDerivOnEuclid (I := I) g α (idx 0) := by
  funext y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem weightedInvGramMthDerivOnEuclid_two_eq_weightedInvGramSecondDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (idx : Fin 2 → Fin (Module.finrank ℝ E)) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j 2 idx =
      weightedInvGramSecondDerivOnEuclid (I := I) g α i j (idx 0) (idx 1) := by
  funext y
  rw [weightedInvGramMthDerivOnEuclid_succ]
  have h_last_1 : (Fin.last 1 : Fin 2) = 1 := rfl
  rw [h_last_1]
  rw [weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid]
  have h_initial_0 : (Fin.init idx) 0 = idx 0 := by
    simp [Fin.init]
  rw [h_initial_0]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_two_eq_weightedInvGramSecondDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_two_eq_weightedInvGramSecondDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_two_eq_weightedInvGramSecondDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_two_eq_weightedInvGramSecondDerivOnEuclid

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem densityMthDerivOnEuclid_two_eq_densitySecondDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (idx : Fin 2 → Fin (Module.finrank ℝ E)) :
    densityMthDerivOnEuclid (I := I) (M := M) g α 2 idx =
      densitySecondDerivOnEuclid (I := I) g α (idx 0) (idx 1) := by
  funext y
  rw [densityMthDerivOnEuclid_succ]
  have h_last_1 : (Fin.last 1 : Fin 2) = 1 := rfl
  rw [h_last_1]
  rw [densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid]
  have h_initial_0 : (Fin.init idx) 0 = idx 0 := by
    simp [Fin.init]
  rw [h_initial_0]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_two_eq_densitySecondDerivOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_two_eq_densitySecondDerivOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_two_eq_densitySecondDerivOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_two_eq_densitySecondDerivOnEuclid

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma weightedInvGramMthDerivOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
      g α i j m idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      have h_eq : weightedInvGramMthDerivOnEuclid (I := I) (M := M)
          g α i j 0 idx = weightedInvGramOnEuclid (I := I) g α i j := by
        funext y
        exact weightedInvGramMthDerivOnEuclid_zero
          (I := I) (M := M) g α i j idx y
      rw [h_eq]
      exact weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  | succ m ih =>
      have h_inner :
          ContDiffOn ℝ ∞ (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
            g α i j m (Fin.init idx))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (Fin.init idx)
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_fderiv :
          ContDiffOn ℝ ∞ (fun y => fderiv ℝ
            (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
              g α i j m (Fin.init idx)) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_inner).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) =>
            L (EuclideanSpace.single (idx (Fin.last m)) 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx (Fin.last m)) (1 : ℝ))).contDiff
      have h_eq : weightedInvGramMthDerivOnEuclid (I := I) (M := M)
          g α i j (m + 1) idx =
          (fun y => (fderiv ℝ
              (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
                g α i j m (Fin.init idx)) y)
            (EuclideanSpace.single (idx (Fin.last m)) 1)) := by
        funext y
        exact weightedInvGramMthDerivOnEuclid_succ
          (I := I) (M := M) g α i j m idx y
      rw [h_eq]
      exact h_eval.contDiffOn.comp h_fderiv (_root_.Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma densityMthDerivOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densityMthDerivOnEuclid (I := I) (M := M) g α m idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      have h_eq : densityMthDerivOnEuclid (I := I) (M := M)
          g α 0 idx = densityOnEuclid (I := I) g α := by
        funext y
        exact densityMthDerivOnEuclid_zero
          (I := I) (M := M) g α idx y
      rw [h_eq]
      exact densityOnEuclid_contDiffOn (I := I) g α
  | succ m ih =>
      have h_inner :
          ContDiffOn ℝ ∞ (densityMthDerivOnEuclid (I := I) (M := M)
            g α m (Fin.init idx))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (Fin.init idx)
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_fderiv :
          ContDiffOn ℝ ∞ (fun y => fderiv ℝ
            (densityMthDerivOnEuclid (I := I) (M := M)
              g α m (Fin.init idx)) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_inner).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) =>
            L (EuclideanSpace.single (idx (Fin.last m)) 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx (Fin.last m)) (1 : ℝ))).contDiff
      have h_eq : densityMthDerivOnEuclid (I := I) (M := M)
          g α (m + 1) idx =
          (fun y => (fderiv ℝ
              (densityMthDerivOnEuclid (I := I) (M := M)
                g α m (Fin.init idx)) y)
            (EuclideanSpace.single (idx (Fin.last m)) 1)) := by
        funext y
        exact densityMthDerivOnEuclid_succ
          (I := I) (M := M) g α m idx y
      rw [h_eq]
      exact h_eval.contDiffOn.comp h_fderiv (_root_.Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_contDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma weightedInvGramMthDerivOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
      g α i j m idx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramMthDerivOnEuclid_contDiffOn
    (I := I) (M := M) g α i j m idx).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_continuousOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma densityMthDerivOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContinuousOn (densityMthDerivOnEuclid (I := I) (M := M) g α m idx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityMthDerivOnEuclid_contDiffOn
    (I := I) (M := M) g α m idx).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_continuousOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma weightedInvGramMthDerivOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramMthDerivOnEuclid (I := I) (M := M)
        g α i j m idx y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j m idx) K :=
    (weightedInvGramMthDerivOnEuclid_continuousOn
      (I := I) (M := M) g α i j m idx).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramMthDerivOnEuclid (I := I) (M := M)
        g α i j m idx y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramMthDerivOnEuclid (I := I) (M := M)
    g α i j m idx y_max|, ?_⟩
  intro y hy
  exact h_max hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_bounded_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_bounded_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_bounded_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.weightedInvGramMthDerivOnEuclid_bounded_on_compact

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma densityMthDerivOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |densityMthDerivOnEuclid (I := I) (M := M) g α m idx y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (densityMthDerivOnEuclid (I := I) (M := M) g α m idx) K :=
    (densityMthDerivOnEuclid_continuousOn
      (I := I) (M := M) g α m idx).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densityMthDerivOnEuclid (I := I) (M := M)
        g α m idx y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densityMthDerivOnEuclid (I := I) (M := M)
    g α m idx y_max|, ?_⟩
  intro y hy
  exact h_max hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_bounded_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_bounded_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_bounded_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedLeibnizCoefficients.densityMthDerivOnEuclid_bounded_on_compact

end IteratedLeibnizCoefficients
end Laplacian
end Analysis
end DifferentialGeometry

end
