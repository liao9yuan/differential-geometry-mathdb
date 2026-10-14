import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.Regularity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RotationSobolevBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartSobolevBounds.Uniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergenceSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.LocalizedMultiplicationBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

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

section MainResults


def eigenvectorResolventChartWkpRegularity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ) : Prop :=
  ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
    MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorResolventChartWkpRegularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorResolventChartWkpRegularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorResolventChartWkpRegularity ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorResolventChartWkpRegularity

section Aggregate

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

def resolventH1ComplChartWkpNorm (N : ℕ) (β : M)
    (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))
        β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolventH1ComplChartWkpNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolventH1ComplChartWkpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolventH1ComplChartWkpNorm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolventH1ComplChartWkpNorm

def eigenvectorChartComponentWkpNorm : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm

def eigenvectorCrossLeftWkpControl : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ((∑ Q : TensorCompIdx (E := E) r s,
        resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i (K + 1) β Q)
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i (K + 1) β' Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl

def eigenvectorCrossRightWkpControl : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ∑ Q : TensorCompIdx (E := E) r s,
      resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i K β Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl

def eigenvectorPartialLimitWkpNormSum : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum

def eigenvectorComponentLimitWkpNormSum : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit (I := I) (M := M)
          g r s i α p :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum

def eigenvectorCrossRightLimitWkpNormSum : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum

def eigenvectorCutoffPartialLimitWkpNormSum : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P l :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum

def eigenvectorChartRHSWkpControl : ℝ≥0∞ :=
  eigenvectorChartComponentWkpNorm (I := I) (M := M) g r s i α P₀ K +
    eigenvectorCrossLeftWkpControl (I := I) (M := M) g r s i α K +
    eigenvectorCrossRightWkpControl (I := I) (M := M) g r s i α K +
    eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K +
    eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K +
    eigenvectorCrossRightLimitWkpNormSum (I := I) (M := M) g r s i α K +
    eigenvectorCutoffPartialLimitWkpNormSum (I := I) (M := M) g r s i α K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSWkpControl

end Aggregate

private lemma le_sevenSum (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₇ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a₁ ≤ a₁ + a₂ := le_self_add
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₂ ≤ a₁ + a₂ := le_add_self
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₃ ≤ a₁ + a₂ + a₃ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₄ ≤ a₁ + a₂ + a₃ + a₄ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · exact le_add_self

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sevenSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sevenSum target :: scope.openDecls } }

section Domination

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)


omit [CompleteSpace E] in
lemma eigenvectorChartComponentWkpNorm_le_rhsWkpControl :
    eigenvectorChartComponentWkpNorm (I := I) (M := M) g r s i α P₀ K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentWkpNorm_le_rhsWkpControl


omit [CompleteSpace E] in
lemma eigenvectorCrossLeftWkpControl_le_rhsWkpControl :
    eigenvectorCrossLeftWkpControl (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeftWkpControl_le_rhsWkpControl


omit [CompleteSpace E] in
lemma eigenvectorCrossRightWkpControl_le_rhsWkpControl :
    eigenvectorCrossRightWkpControl (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightWkpControl_le_rhsWkpControl


omit [CompleteSpace E] in
lemma eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorPartialLimitWkpNormSum_le_rhsWkpControl


omit [CompleteSpace E] in
lemma eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorComponentLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorComponentLimitWkpNormSum_le_rhsWkpControl


omit [CompleteSpace E] in
lemma eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorCrossRightLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightLimitWkpNormSum_le_rhsWkpControl


omit [CompleteSpace E] in
lemma eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl :
    eigenvectorCutoffPartialLimitWkpNormSum (I := I) (M := M) g r s i α K
      ≤ eigenvectorChartRHSWkpControl (I := I) (M := M) g r s i α P₀ K := by
  rw [eigenvectorChartRHSWkpControl]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffPartialLimitWkpNormSum_le_rhsWkpControl

omit [CompleteSpace E] in
lemma crossRightGradCoeffDivLimit_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_term7_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) Ω :=
    eigenvectorChartCrossRightDivergence_memWkp (I := I) (M := M) g r s i α P₀ K h_pou
  have h_term7_ae_zero : ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => by
      change (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0
      rw [crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp, _root_.MulZeroClass.mul_zero])
  obtain ⟨h_prod_memWkp, _⟩ := wkpNorm_smooth_coef_mul_ae_zero_factor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_term7_memWkp h_term7_ae_zero
  have h_ae_eq : (fun y => densityOnEuclid (I := I) g α y *
        eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀ y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω]
      crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ := by
    refine (_root_.MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hy' : y ∈ chartTargetEuclid (I := I) (M := M) α := hy
    have h_pos : densityOnEuclid (I := I) g α y ≠ 0 :=
      (densityOnEuclid_pos (I := I) g α hy').ne'
    change densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y)
      = crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y
    rw [← mul_assoc, mul_one_div, div_self h_pos, one_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memWkp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memWkp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memWkp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memWkp

end Domination

end MainResults

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
