import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Algebra.CovariantSumCross

import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.Uniform
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormBounds
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.FirstOrder
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }


def ccUnitField (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s :=
  MixedSection.toMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ W.toSection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccUnitField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccUnitField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccUnitField ``Submission.DifferentialGeometry.PDE.RicciFlow.ccUnitField

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma ccUnitField_apply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) :
    ccUnitField (I := I) g s W x =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccUnitField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccUnitField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccUnitField_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.ccUnitField_apply


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma ccUnitField_recast (g g' : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) :
    ccUnitField (I := I) g' s (W.recast (g' := g')) = ccUnitField (I := I) g s W := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccUnitField_recast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccUnitField_recast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccUnitField_recast ``Submission.DifferentialGeometry.PDE.RicciFlow.ccUnitField_recast

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem iterCovGrad_unit_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (j : ℕ) :
    (fun x : M => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + j) I x from
        (iteratedCovGrad (I := I) g 0 s j W).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
      (fun x : M => iterCov (I := I) g s (ccUnitField (I := I) g s W) j x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    set Tj : SmoothCcTensor g 0 (s + j) := iteratedCovGrad (I := I) g 0 s j W with hTj
    change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace ((s + j) + 1) I x from
        (covGrad (I := I) (M := M) g 0 (s + j) Tj).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      iterCov (I := I) g s (ccUnitField (I := I) g s W) (j + 1) x
    apply Tensor0SBundle.tensor0SSpace_ext (I := I) (s + j + 1) x
    intro v
    change Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace ((s + j) + 1) I x from
          (covGrad (I := I) (M := M) g 0 (s + j) Tj).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.eval
        (iterCov (I := I) g s (ccUnitField (I := I) g s W) (j + 1) x) v
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (v 0)
    have hcons : v = Fin.cons (v 0) (Matrix.vecTail v) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k; simp [Matrix.vecTail]
    rw [covGrad_apply_unit_eval (I := I) (M := M) g (s + j) Tj x v]
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 (s + j) Tj x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0)),
      ContinuousLinearEquiv.symm_apply_apply]
    rw [covDeriv_unit_eval_eq (I := I) (M := M) g (s + j) (Tj.toSection) x (v 0)]
    rw [ih]
    rw [← hXx]
    rw [← nabla0SFun_eq_tensor0SCovariantDerivative (I := I) g (s + j) X
      (iterCov (I := I) g s (ccUnitField (I := I) g s W) j) x]
    rw [iterCov_succ, covStep_apply]
    have hcons2 : v = Fin.cons (X x) (Matrix.vecTail v) := by rw [hXx]; exact hcons
    conv_rhs => rw [hcons2]
    rw [totalNabla0SFun_eval_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + j) (leviCivitaConnectionOfMetric (I := I) g) X
      (iterCov (I := I) g s (ccUnitField (I := I) g s W) j) x (Matrix.vecTail v)]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_unit_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iterCovGrad_unit_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_unit_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.iterCovGrad_unit_eq


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lowerAllUpper0_unit (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor g 0 s) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (unitZeroSec (I := I) (M := M) x)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lowerAllUpper0_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lowerAllUpper0_unit target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq0_unit_eq (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor g 0 s) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (W.toSection x) =
      normSq0S (I := I) g x s (ccUnitField (I := I) g s W x) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm)
      (finCongr (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl)))
      _ _ ?_
  intro slots
  rw [component0S_apply]
  rw [show ccUnitField (I := I) g s W x =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [lowerAllUpper0_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Function.comp_apply];
     congr 1;
     apply Fin.ext;
     simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq0_unit_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq0_unit_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq0_unit_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq0_unit_eq

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iterCovGrad_eq (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j W).toSection x) =
      normSq0S (I := I) g x (s + j)
        (iterCov (I := I) g s (ccUnitField (I := I) g s W) j x) := by
  have h : ccUnitField (I := I) g (s + j) (iteratedCovGrad (I := I) g 0 s j W) x =
      iterCov (I := I) g s (ccUnitField (I := I) g s W) j x :=
    congrFun (iterCovGrad_unit_eq (I := I) g s W j) x
  rw [riemannianFiberNormSq0_unit_eq (I := I) g (s + j) x (iteratedCovGrad (I := I) g 0 s j W)]
  exact congrArg (normSq0S (I := I) g x (s + j)) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_iterCovGrad_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_iterCovGrad_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_iterCovGrad_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_iterCovGrad_eq

private theorem dtowerNonneg (n : ℕ) {q : ℝ} (hq : 0 ≤ q) (r : ℕ) {Racc : ℕ → ℝ}
    (hR : ∀ m, 0 ≤ Racc m) (N : ℕ) : 0 ≤ Dtower n q r Racc N := by
  induction N with
  | zero => simp [Dtower]
  | succ N ih =>
      have h1 : 0 ≤ Racc N := hR N
      have h2 : (0 : ℝ) ≤ ((r + N : ℕ) : ℝ) * Real.sqrt ((n : ℝ) ^ (r + N + 1)) * q := by
        positivity
      have h3 : (0 : ℝ) ≤ (((r + N : ℕ) : ℝ) * Real.sqrt ((n : ℝ) ^ (r + N + 1)) * q) *
          Dtower n q r Racc N := mul_nonneg h2 ih
      simp only [Dtower]; linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.dtowerNonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.dtowerNonneg target :: scope.openDecls } }

def jetOnePt (n : ℕ) (Λ Λ' : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (Λ ^ (r + 1)) *
    (1 + Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r (fun _ => 0) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.jetOnePt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.jetOnePt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.jetOnePt ``Submission.DifferentialGeometry.PDE.RicciFlow.jetOnePt

lemma jetOnePt_nonneg {Λ Λ' : ℝ} (hΛ' : 0 ≤ Λ') (n r : ℕ) :
    0 ≤ jetOnePt n Λ Λ' r := by
  have hq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ')
  have hD : (0 : ℝ) ≤
      Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r (fun _ => 0) 1 :=
    dtowerNonneg n hq r (fun _ => le_refl 0) 1
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg zero_le_one hD)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.jetOnePt_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.jetOnePt_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.jetOnePt_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.jetOnePt_nonneg

private lemma raccTwoNonneg {Λ Λ' Λ'' : ℝ} (hΛ : 0 ≤ Λ) (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (n r : ℕ) (m : ℕ) :
    0 ≤ (if m = 1 then
      (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
      else 0) := by
  split
  · have h1 : (0 : ℝ) ≤ Λ'' + Λ * Λ' ^ 2 := add_nonneg hΛ'' (mul_nonneg hΛ (sq_nonneg Λ'))
    have h2 : (0 : ℝ) ≤ 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) := mul_nonneg (by positivity) h1
    have h3 : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
      mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ')
    have h4 : (0 : ℝ) ≤ (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) := by positivity
    exact mul_nonneg h4 (add_nonneg h2 h3)
  · exact le_refl 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.raccTwoNonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.raccTwoNonneg target :: scope.openDecls } }

def jetTowerPt (n : ℕ) (Λ Λ' Λ'' : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (Λ ^ (r + 2)) *
    (1
      + Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r (fun _ => 0) 1
      + Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r
          (fun m => if m = 1 then
            (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) *
              (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
            else 0) 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.jetTowerPt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.jetTowerPt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.jetTowerPt ``Submission.DifferentialGeometry.PDE.RicciFlow.jetTowerPt

lemma jetTowerPt_nonneg {Λ Λ' Λ'' : ℝ} (hΛ : 0 ≤ Λ) (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (n r : ℕ) : 0 ≤ jetTowerPt n Λ Λ' Λ'' r := by
  have hq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ')
  have hD1 : (0 : ℝ) ≤ Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r (fun _ => 0) 1 :=
    dtowerNonneg n hq r (fun _ => le_refl 0) 1
  have hD2 : (0 : ℝ) ≤ Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r
      (fun m => if m = 1 then
        (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
        else 0) 2 :=
    dtowerNonneg n hq r (raccTwoNonneg hΛ hΛ' hΛ'' n r) 2
  unfold jetTowerPt
  have := Real.sqrt_nonneg (Λ ^ (r + 2))
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.jetTowerPt_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.jetTowerPt_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.jetTowerPt_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.jetTowerPt_nonneg


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem covStepZero (gRef : SmoothRiemannianMetric I M) (s : ℕ) :
    covStep (I := I) gRef s 0 = 0 := by
  have h := covStep_add (I := I) gRef s 0 0
  rw [add_zero] at h
  have hc : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0 =
      covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.covStepZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.covStepZero target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem sqrtNormSq0SZero (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    Real.sqrt (normSq0S (I := I) g x s (0 : Tensor0SSpace s I x)) = 0 := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON)]
  rw [show (∑ slots : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      (component0S (I := I) basis (0 : Tensor0SSpace s I x) slots) ^ 2) = 0 from ?_]
  · exact Real.sqrt_zero
  · refine Finset.sum_eq_zero (fun slots _ => ?_)
    rw [component0S_apply]; simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrtNormSq0SZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sqrtNormSq0SZero target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
private theorem towerCrossOne_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (s : ℕ)
    (U : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    {j : ℕ} (hj : j ≤ 1) (x : M) :
    Real.sqrt (normSq0S (I := I) g₀ x (s + j) (iterCov (I := I) gBase s U j x)) ≤
      (1 + Dtower (Module.finrank ℝ E)
        ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s (fun _ => 0) 1) *
        ∑ k ∈ Finset.range 2,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k)
            (iterCov (I := I) g₀ s U k x)) := by
  classical
  have hΛ'nn : (0 : ℝ) ≤ Λ' :=
    le_trans (Real.sqrt_nonneg _) (hjet x (Set.mem_univ x))
  have hq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ'nn)
  have hD : (0 : ℝ) ≤ Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s (fun _ => 0) 1 :=
    dtowerNonneg _ hq s (fun _ => le_refl 0) 1
  have hS2 : (0 : ℝ) ≤ ∑ k ∈ Finset.range 2,
      Real.sqrt (normSq0S (I := I) g₀ x (s + k)
        (iterCov (I := I) g₀ s U k x)) :=
    Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _)
  interval_cases j
  · have hterm : Real.sqrt (normSq0S (I := I) g₀ x (s + 0)
        (iterCov (I := I) gBase s U 0 x)) ≤
        ∑ k ∈ Finset.range 2,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k)
            (iterCov (I := I) g₀ s U k x)) :=
      Finset.single_le_sum
        (f := fun k => Real.sqrt (normSq0S (I := I) g₀ x (s + k)
          (iterCov (I := I) g₀ s U k x)))
        (fun k _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by norm_num))
    nlinarith
  · have hacc : ∀ m, m < 1 →
        Real.sqrt (normSq0S (I := I) g₀ x (s + m + 1)
            (covStep (I := I) g₀ (s + m)
              (telescAccum (I := I) gBase g₀ s U m) x)) ≤
          (fun _ : ℕ => (0 : ℝ)) m * ∑ k ∈ Finset.range (m + 2),
            Real.sqrt (normSq0S (I := I) g₀ x (s + k)
              (iterCov (I := I) g₀ s U k x)) := by
      intro m hm
      have hm0 : m = 0 := Nat.lt_one_iff.mp hm
      subst hm0
      rw [show telescAccum (I := I) gBase g₀ s U 0 = 0 from rfl,
        covStepZero (I := I) g₀ (s + 0)]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sqrtNormSq0SZero,
        _root_.MulZeroClass.zero_mul, le_refl]
    have h1 := iterCovG1_le (I := I) gBase g₀ s U x (fun _ => (0 : ℝ))
      (fun _ => le_refl 0) hEq hjet (Set.mem_univ x) 1 hacc
    nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.towerCrossOne_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.towerCrossOne_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem sqrtRiemannianFiberNormSq_one_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) {j : ℕ} (hj : j ≤ 1) (x : M) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        ((iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))).toSection x)) ≤
      jetOnePt (Module.finrank ℝ E) Λ Λ' s *
        ∑ k ∈ Finset.range 2,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
            ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x)) := by
  classical
  have hL : riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        ((iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))).toSection x) =
      normSq0S (I := I) gBase x (s + j)
        (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x) := by
    rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) gBase s j (T.recast (g' := gBase)) x,
      ccUnitField_recast (I := I) g₀ gBase s T]
  have hR : ∀ k : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x) =
      normSq0S (I := I) g₀ x (s + k)
        (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x) :=
    fun k => riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ s k T x
  rw [hL]
  rw [show (∑ k ∈ Finset.range 2,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x))) =
      ∑ k ∈ Finset.range 2,
        Real.sqrt (normSq0S (I := I) g₀ x (s + k)
          (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x)) from
    Finset.sum_congr rfl (fun k _ => by rw [hR k])]
  have hfib := covsumCross_fibNorm (I := I) g₀ gBase
    (metricUniformEquivalentOn_symm (I := I) hEq) x (s + j)
    (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)
  have htow := towerCrossOne_le (I := I) gBase g₀ hEq hjet s
    (ccUnitField (I := I) g₀ s T) hj x
  have hle : Λ ^ (s + j) ≤ Λ ^ (s + 1) := by
    refine pow_le_pow_right₀ hEq.1 ?_
    omega
  have hpow : Real.sqrt (Λ ^ (s + j)) ≤ Real.sqrt (Λ ^ (s + 1)) :=
    Real.sqrt_le_sqrt hle
  have hnn : (0 : ℝ) ≤ Real.sqrt (normSq0S (I := I) g₀ x (s + j)
      (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)) :=
    Real.sqrt_nonneg _
  unfold jetOnePt
  calc
    Real.sqrt (normSq0S (I := I) gBase x (s + j)
        (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x))
        ≤ Real.sqrt (Λ ^ (s + j)) *
          Real.sqrt (normSq0S (I := I) g₀ x (s + j)
            (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)) := hfib
    _ ≤ Real.sqrt (Λ ^ (s + 1)) *
          ((1 + Dtower (Module.finrank ℝ E)
              ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s (fun _ => 0) 1) *
            ∑ k ∈ Finset.range 2,
              Real.sqrt (normSq0S (I := I) g₀ x (s + k)
                (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x))) :=
      mul_le_mul hpow htow hnn (Real.sqrt_nonneg _)
    _ = Real.sqrt (Λ ^ (s + 1)) *
          (1 + Dtower (Module.finrank ℝ E)
              ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s (fun _ => 0) 1) *
            ∑ k ∈ Finset.range 2,
              Real.sqrt (normSq0S (I := I) g₀ x (s + k)
                (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x)) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_one_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_one_le ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_one_le

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem towerCross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (s : ℕ)
    (U : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    {j : ℕ} (hj : j ≤ 2) (x : M) :
    Real.sqrt (normSq0S (I := I) g₀ x (s + j) (iterCov (I := I) gBase s U j x)) ≤
      (1
        + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
            (fun _ => 0) 1
        + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
            (fun m => if m = 1 then
              (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
                (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
                  (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
              else 0) 2) *
        ∑ k ∈ Finset.range 3,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hΛ'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hjet x (Set.mem_univ x))
  have hΛ''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x (Set.mem_univ x))
  have hq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ'nn)
  have hD1 : (0 : ℝ) ≤ Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s (fun _ => 0) 1 :=
    dtowerNonneg _ hq s (fun _ => le_refl 0) 1
  have hD2 : (0 : ℝ) ≤ Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
      (fun m => if m = 1 then
        (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
        else 0) 2 :=
    dtowerNonneg _ hq s (raccTwoNonneg hΛ0 hΛ'nn hΛ''nn _ s) 2
  have hS3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range 3,
      Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) :=
    Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _)
  interval_cases j
  · have hterm : Real.sqrt (normSq0S (I := I) g₀ x (s + 0) (iterCov (I := I) gBase s U 0 x)) ≤
        ∑ k ∈ Finset.range 3,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) :=
      Finset.single_le_sum
        (f := fun k => Real.sqrt (normSq0S (I := I) g₀ x (s + k)
          (iterCov (I := I) g₀ s U k x)))
        (fun k _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by norm_num))
    nlinarith
  · have hacc : ∀ m, m < 1 →
        Real.sqrt (normSq0S (I := I) g₀ x (s + m + 1)
            (covStep (I := I) g₀ (s + m) (telescAccum (I := I) gBase g₀ s U m) x)) ≤
          (fun _ : ℕ => (0 : ℝ)) m * ∑ k ∈ Finset.range (m + 2),
            Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) := by
      intro m hm
      have hm0 : m = 0 := Nat.lt_one_iff.mp hm
      subst hm0
      rw [show telescAccum (I := I) gBase g₀ s U 0 = 0 from rfl,
        covStepZero (I := I) g₀ (s + 0)]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sqrtNormSq0SZero, _root_.MulZeroClass.zero_mul, le_refl]
    have h1 := iterCovG1_le (I := I) gBase g₀ s U x (fun _ => (0 : ℝ))
      (fun _ => le_refl 0) hEq hjet (Set.mem_univ x) 1 hacc
    have hsubset : Finset.range 2 ⊆ Finset.range 3 := by
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    have hsub : ∑ k ∈ Finset.range 2,
        Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) ≤
        ∑ k ∈ Finset.range 3,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => Real.sqrt_nonneg _)
    nlinarith
  · have h2 := iterCovG1_two (I := I) gBase g₀ s U x hEq hjet hJet1 hJet2 (Set.mem_univ x)
    nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.towerCross_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.towerCross_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem sqrtRiemannianFiberNormSq_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) {j : ℕ} (hj : j ≤ 2) (x : M) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        ((iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))).toSection x)) ≤
      jetTowerPt (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ k ∈ Finset.range 3,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
            ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x)) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL : riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        ((iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))).toSection x) =
      normSq0S (I := I) gBase x (s + j)
        (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x) := by
    rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) gBase s j (T.recast (g' := gBase)) x,
      ccUnitField_recast (I := I) g₀ gBase s T]
  have hR : ∀ k : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x) =
      normSq0S (I := I) g₀ x (s + k)
        (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x) :=
    fun k => riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ s k T x
  rw [hL]
  rw [show (∑ k ∈ Finset.range 3,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x))) =
      ∑ k ∈ Finset.range 3,
        Real.sqrt (normSq0S (I := I) g₀ x (s + k)
          (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x)) from
    Finset.sum_congr rfl (fun k _ => by rw [hR k])]
  have hfib := covsumCross_fibNorm (I := I) g₀ gBase
    (metricUniformEquivalentOn_symm (I := I) hEq) x (s + j)
    (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)
  have htow := towerCross_le (I := I) gBase g₀ hEq hjet hJet1 hJet2 s
    (ccUnitField (I := I) g₀ s T) hj x
  have hle : Λ ^ (s + j) ≤ Λ ^ (s + 2) := by
    refine pow_le_pow_right₀ hEq.1 ?_
    omega
  have hpow : Real.sqrt (Λ ^ (s + j)) ≤ Real.sqrt (Λ ^ (s + 2)) := Real.sqrt_le_sqrt hle
  have hnn : (0 : ℝ) ≤ Real.sqrt (normSq0S (I := I) g₀ x (s + j)
      (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)) := Real.sqrt_nonneg _
  unfold jetTowerPt
  calc Real.sqrt (normSq0S (I := I) gBase x (s + j)
        (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x))
      ≤ Real.sqrt (Λ ^ (s + j)) * Real.sqrt (normSq0S (I := I) g₀ x (s + j)
          (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)) := hfib
    _ ≤ Real.sqrt (Λ ^ (s + 2)) *
          ((1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun _ => 0) 1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun m => if m = 1 then
                  (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
                    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
                      (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
                  else 0) 2) *
            ∑ k ∈ Finset.range 3,
              Real.sqrt (normSq0S (I := I) g₀ x (s + k)
                (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x))) :=
        mul_le_mul hpow htow hnn (Real.sqrt_nonneg _)
    _ = Real.sqrt (Λ ^ (s + 2)) *
          (1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun _ => 0) 1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun m => if m = 1 then
                  (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
                    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
                      (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
                  else 0) 2) *
            ∑ k ∈ Finset.range 3,
              Real.sqrt (normSq0S (I := I) g₀ x (s + k)
                (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x)) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_cross_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_cross_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_cross_le ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrtRiemannianFiberNormSq_cross_le

def kjetOneC (n : ℕ) (Λ Λ' : ℝ) (s : ℕ) : ℝ :=
  Real.sqrt (2 * Real.sqrt (Λ ^ n)) * jetOnePt n Λ Λ' s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.kjetOneC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.kjetOneC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.kjetOneC ``Submission.DifferentialGeometry.PDE.RicciFlow.kjetOneC

lemma kjetOneC_nonneg {Λ Λ' : ℝ} (hΛ' : 0 ≤ Λ') (n s : ℕ) :
    0 ≤ kjetOneC n Λ Λ' s :=
  mul_nonneg (Real.sqrt_nonneg _) (jetOnePt_nonneg hΛ' n s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.kjetOneC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.kjetOneC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.kjetOneC_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.kjetOneC_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem jetCross_l2_one
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hΛ' : 0 ≤ Λ')
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) {j : ℕ} (hj : j ≤ 1) :
    ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ≤
      kjetOneC (Module.finrank ℝ E) Λ Λ' s *
        ∑ k ∈ Finset.range 2, ‖iteratedCovGrad (I := I) g₀ 0 s k T‖ := by
  classical
  set P : ℝ := jetOnePt (Module.finrank ℝ E) Λ Λ' s with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact jetOnePt_nonneg hΛ' _ s
  set c : ℝ := Real.sqrt (Λ ^ Module.finrank ℝ E) with hcdef
  have hcnn : 0 ≤ c := by
    rw [hcdef]
    exact Real.sqrt_nonneg _
  set μB := riemannianVolumeMeasure (I := I) (M := M) gBase with hμB
  set μ0 := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ0
  set A : SmoothCcTensor gBase 0 (s + j) :=
    iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase)) with hA
  set b : ℕ → ℝ := fun k => ‖iteratedCovGrad (I := I) g₀ 0 s k T‖ with hb
  have hbnn : ∀ k, 0 ≤ b k := fun k => norm_nonneg _
  set R : ℕ → M → ℝ := fun k x =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
      ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x) with hR
  have hRnn : ∀ k x, 0 ≤ R k x := fun k x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + k) x _
  set F : M → ℝ := fun x => 2 * P ^ 2 * ∑ k ∈ Finset.range 2, R k x with hF
  have hFnn : ∀ x, 0 ≤ F x := by
    intro x
    have hsum : (0 : ℝ) ≤ ∑ k ∈ Finset.range 2, R k x :=
      Finset.sum_nonneg (fun k _ => hRnn k x)
    exact mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * P ^ 2) hsum
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        (A.toSection x) ≤ F x := by
    intro x
    have h := sqrtRiemannianFiberNormSq_one_le (I := I) gBase g₀ hEq hjet s T hj x
    have hLnn : (0 : ℝ) ≤
        riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
          (A.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) gBase 0 (s + j) x _
    have hcs : (∑ k ∈ Finset.range 2, Real.sqrt (R k x)) ^ 2 ≤
        2 * ∑ k ∈ Finset.range 2, R k x := by
      have hch := sq_sum_le_card_mul_sum_sq (s := Finset.range 2)
        (f := fun k => Real.sqrt (R k x))
      rw [Finset.card_range] at hch
      have hsq : ∑ k ∈ Finset.range 2, Real.sqrt (R k x) ^ 2 =
          ∑ k ∈ Finset.range 2, R k x :=
        Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hRnn k x))
      rw [hsq] at hch
      exact_mod_cast hch
    have hsq2 :
        riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
            (A.toSection x) ≤
          (P * ∑ k ∈ Finset.range 2, Real.sqrt (R k x)) ^ 2 := by
      have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rwa [Real.sq_sqrt hLnn] at hsquare
    have hstep : (P * ∑ k ∈ Finset.range 2, Real.sqrt (R k x)) ^ 2 ≤ F x := by
      have hmul := mul_le_mul_of_nonneg_left hcs (sq_nonneg P)
      calc
        (P * ∑ k ∈ Finset.range 2, Real.sqrt (R k x)) ^ 2 =
            P ^ 2 * (∑ k ∈ Finset.range 2, Real.sqrt (R k x)) ^ 2 := by ring
        _ ≤ P ^ 2 * (2 * ∑ k ∈ Finset.range 2, R k x) := hmul
        _ = F x := by rw [hF]; ring
    exact le_trans hsq2 hstep
  have hIntA : _root_.MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        (A.toSection x)) μB :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) gBase 0 (s + j) A
  have hIntR : ∀ k, _root_.MeasureTheory.Integrable (R k) μ0 := fun k =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (s + k) _
  have hIntF0 : _root_.MeasureTheory.Integrable F μ0 := by
    rw [hF]
    exact (_root_.MeasureTheory.integrable_finsetSum (Finset.range 2) (fun k _ => hIntR k)).const_mul
      (2 * P ^ 2)
  have hmeasle : μB ≤ ENNReal.ofReal c • μ0 :=
    (volumeMeasure_cross_le (I := I) gBase g₀ hEq).2
  have hIntFs : _root_.MeasureTheory.Integrable F (ENNReal.ofReal c • μ0) :=
    hIntF0.smul_measure ENNReal.ofReal_ne_top
  have hIntFB : _root_.MeasureTheory.Integrable F μB := hIntFs.mono_measure hmeasle
  have hnormA : ‖A‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        (A.toSection x) ∂μB := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) A, hμB]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) gBase (s + j) A
  have hnormB : ∀ k, b k ^ 2 = ∫ x, R k x ∂μ0 := by
    intro k
    rw [hb, hR, hμ0]
    simp only
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 s k T)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g₀ (s + k)
        (iteratedCovGrad (I := I) g₀ 0 s k T)
  have hIF0 : ∫ x, F x ∂μ0 =
      2 * P ^ 2 * ∑ k ∈ Finset.range 2, b k ^ 2 := by
    rw [hF, MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum (Finset.range 2) (fun k _ => hIntR k)]
    exact (Finset.sum_congr rfl (fun k _ => hnormB k)).symm
  have hchain : ‖A‖ ^ 2 ≤
      c * (2 * P ^ 2 * ∑ k ∈ Finset.range 2, b k ^ 2) := by
    rw [hnormA]
    calc
      ∫ x, riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
          (A.toSection x) ∂μB
          ≤ ∫ x, F x ∂μB := MeasureTheory.integral_mono hIntA hIntFB hpt
      _ ≤ ∫ x, F x ∂(ENNReal.ofReal c • μ0) :=
        MeasureTheory.integral_mono_measure hmeasle
          (Filter.Eventually.of_forall hFnn) hIntFs
      _ = c * ∫ x, F x ∂μ0 := by
        rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hcnn,
          smul_eq_mul]
      _ = c * (2 * P ^ 2 * ∑ k ∈ Finset.range 2, b k ^ 2) := by rw [hIF0]
  have hsumsq : ∑ k ∈ Finset.range 2, b k ^ 2 ≤
      (∑ k ∈ Finset.range 2, b k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => hbnn k)
  have hSnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range 2, b k :=
    Finset.sum_nonneg (fun k _ => hbnn k)
  have hfinal : ‖A‖ ^ 2 ≤
      (kjetOneC (Module.finrank ℝ E) Λ Λ' s *
        ∑ k ∈ Finset.range 2, b k) ^ 2 := by
    have hexp :
        (kjetOneC (Module.finrank ℝ E) Λ Λ' s *
          ∑ k ∈ Finset.range 2, b k) ^ 2 =
            2 * c * P ^ 2 * (∑ k ∈ Finset.range 2, b k) ^ 2 := by
      rw [kjetOneC, ← hPdef, ← hcdef, mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * c)]
    rw [hexp]
    have hstep : c * (2 * P ^ 2 * ∑ k ∈ Finset.range 2, b k ^ 2) ≤
        2 * c * P ^ 2 * (∑ k ∈ Finset.range 2, b k) ^ 2 := by
      have hcoef : (0 : ℝ) ≤ 2 * P ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsumsq hcoef]
    exact le_trans hchain hstep
  have hKnn : (0 : ℝ) ≤
      kjetOneC (Module.finrank ℝ E) Λ Λ' s *
        ∑ k ∈ Finset.range 2, b k :=
    mul_nonneg (kjetOneC_nonneg hΛ' _ s) hSnn
  have hsqrt := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hKnn] at hsqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.jetCross_l2_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.jetCross_l2_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.jetCross_l2_one ``Submission.DifferentialGeometry.PDE.RicciFlow.jetCross_l2_one

def kjetConst (n : ℕ) (Λ Λ' Λ'' : ℝ) (s : ℕ) : ℝ :=
  Real.sqrt (3 * Real.sqrt (Λ ^ n)) * jetTowerPt n Λ Λ' Λ'' s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.kjetConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.kjetConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.kjetConst ``Submission.DifferentialGeometry.PDE.RicciFlow.kjetConst

lemma kjetConst_nonneg {Λ Λ' Λ'' : ℝ} (hΛ : 0 ≤ Λ) (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (n s : ℕ) : 0 ≤ kjetConst n Λ Λ' Λ'' s :=
  mul_nonneg (Real.sqrt_nonneg _) (jetTowerPt_nonneg hΛ hΛ' hΛ'' n s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.kjetConst_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.kjetConst_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.kjetConst_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.kjetConst_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem jetCross_l2
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) {j : ℕ} (hj : j ≤ 2) :
    ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ≤
      kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ k ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 s k T‖ := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  set P : ℝ := jetTowerPt (Module.finrank ℝ E) Λ Λ' Λ'' s with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact jetTowerPt_nonneg hΛ0 hΛ' hΛ'' _ s
  set c : ℝ := Real.sqrt (Λ ^ Module.finrank ℝ E) with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; exact Real.sqrt_nonneg _
  set μB := riemannianVolumeMeasure (I := I) (M := M) gBase with hμB
  set μ0 := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ0
  set A : SmoothCcTensor gBase 0 (s + j) :=
    iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase)) with hA
  set b : ℕ → ℝ := fun k => ‖iteratedCovGrad (I := I) g₀ 0 s k T‖ with hb
  have hbnn : ∀ k, 0 ≤ b k := fun k => norm_nonneg _
  set R : ℕ → M → ℝ := fun k x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
    ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x) with hR
  have hRnn : ∀ k x, 0 ≤ R k x := fun k x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + k) x _
  set F : M → ℝ := fun x => 3 * P ^ 2 * ∑ k ∈ Finset.range 3, R k x with hF
  have hFnn : ∀ x, 0 ≤ F x := by
    intro x
    have : (0 : ℝ) ≤ ∑ k ∈ Finset.range 3, R k x :=
      Finset.sum_nonneg (fun k _ => hRnn k x)
    have h2 : (0 : ℝ) ≤ 3 * P ^ 2 := by positivity
    exact mul_nonneg h2 this
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ≤ F x := by
    intro x
    have h := sqrtRiemannianFiberNormSq_cross_le (I := I) gBase g₀ hEq hjet hJet1 hJet2 s T hj x
    have hLnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        (A.toSection x) := riemannianFiberNormSq_nonneg (I := I) (M := M) gBase 0 (s + j) x _
    have hcs : (∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 ≤
        3 * ∑ k ∈ Finset.range 3, R k x := by
      have hch := sq_sum_le_card_mul_sum_sq (s := Finset.range 3)
        (f := fun k => Real.sqrt (R k x))
      rw [Finset.card_range] at hch
      have hsq : ∑ k ∈ Finset.range 3, Real.sqrt (R k x) ^ 2 =
          ∑ k ∈ Finset.range 3, R k x :=
        Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hRnn k x))
      rw [hsq] at hch
      exact_mod_cast hch
    have hsq2 : riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ≤
        (P * ∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rwa [Real.sq_sqrt hLnn] at this
    have hstep : (P * ∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 ≤ F x := by
      have hmul := mul_le_mul_of_nonneg_left hcs (sq_nonneg P)
      calc (P * ∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2
          = P ^ 2 * (∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 := by ring
        _ ≤ P ^ 2 * (3 * ∑ k ∈ Finset.range 3, R k x) := hmul
        _ = F x := by rw [hF]; ring
    exact le_trans hsq2 hstep
  have hIntA : _root_.MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x)) μB :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) gBase 0 (s + j) A
  have hIntR : ∀ k, _root_.MeasureTheory.Integrable (R k) μ0 := fun k =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (s + k) _
  have hIntF0 : _root_.MeasureTheory.Integrable F μ0 := by
    rw [hF]
    exact (_root_.MeasureTheory.integrable_finsetSum (Finset.range 3) (fun k _ => hIntR k)).const_mul (3 * P ^ 2)
  have hmeasle : μB ≤ ENNReal.ofReal c • μ0 := (volumeMeasure_cross_le (I := I) gBase g₀ hEq).2
  have hIntFs : _root_.MeasureTheory.Integrable F (ENNReal.ofReal c • μ0) :=
    hIntF0.smul_measure ENNReal.ofReal_ne_top
  have hIntFB : _root_.MeasureTheory.Integrable F μB := hIntFs.mono_measure hmeasle
  have hnormA : ‖A‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ∂μB := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) A, hμB]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M)
      gBase (s + j) A
  have hnormB : ∀ k, b k ^ 2 = ∫ x, R k x ∂μ0 := by
    intro k
    rw [hb, hR, hμ0]
    simp only
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 s k T)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M)
      g₀ (s + k) (iteratedCovGrad (I := I) g₀ 0 s k T)
  have hIF0 : ∫ x, F x ∂μ0 = 3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2 := by
    rw [hF]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum (Finset.range 3) (fun k _ => hIntR k)]
    exact (Finset.sum_congr rfl (fun k _ => (hnormB k))).symm
  have hchain : ‖A‖ ^ 2 ≤ c * (3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2) := by
    rw [hnormA]
    calc ∫ x, riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ∂μB
        ≤ ∫ x, F x ∂μB := MeasureTheory.integral_mono hIntA hIntFB hpt
      _ ≤ ∫ x, F x ∂(ENNReal.ofReal c • μ0) :=
          MeasureTheory.integral_mono_measure hmeasle
            (Filter.Eventually.of_forall hFnn) hIntFs
      _ = c * ∫ x, F x ∂μ0 := by
          rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hcnn, smul_eq_mul]
      _ = c * (3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2) := by rw [hIF0]
  have hsumsq : ∑ k ∈ Finset.range 3, b k ^ 2 ≤ (∑ k ∈ Finset.range 3, b k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => hbnn k)
  have hSnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range 3, b k := Finset.sum_nonneg (fun k _ => hbnn k)
  have hfinal : ‖A‖ ^ 2 ≤
      (kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s * ∑ k ∈ Finset.range 3, b k) ^ 2 := by
    have hexp : (kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ k ∈ Finset.range 3, b k) ^ 2 =
          3 * c * P ^ 2 * (∑ k ∈ Finset.range 3, b k) ^ 2 := by
      rw [kjetConst, ← hPdef, ← hcdef, mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3 * c)]
    rw [hexp]
    have hstep : c * (3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2) ≤
        3 * c * P ^ 2 * (∑ k ∈ Finset.range 3, b k) ^ 2 := by
      have h1 : (0 : ℝ) ≤ 3 * P ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsumsq h1]
    exact le_trans hchain hstep
  have hKnn : (0 : ℝ) ≤ kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
      ∑ k ∈ Finset.range 3, b k :=
    mul_nonneg (kjetConst_nonneg hΛ0 hΛ' hΛ'' _ s) hSnn
  have := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hKnn] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.jetCross_l2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.jetCross_l2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.jetCross_l2 ``Submission.DifferentialGeometry.PDE.RicciFlow.jetCross_l2

omit [NeZero (Module.finrank ℝ E)] in
theorem kjet_of_class
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (hdim : Module.finrank ℝ E / 2 + 2 = 3)
    (s : ℕ) (S : SmoothCcTensor g₀ 0 s)
    (j : ℕ) (hj : j ∈ Finset.range (Module.finrank ℝ E / 2 + 2)) :
    ‖iteratedCovGrad (I := I) gBase 0 s j (S.recast (g' := gBase))‖ ≤
      kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s i S‖ := by
  rw [hdim] at hj ⊢
  have hj2 : j ≤ 2 := by
    have := Finset.mem_range.mp hj
    omega
  exact jetCross_l2 (I := I) gBase g₀ hEq hjet hJet1 hJet2 hΛ' hΛ'' s S hj2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.kjet_of_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.kjet_of_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.kjet_of_class ``Submission.DifferentialGeometry.PDE.RicciFlow.kjet_of_class

theorem fibreMorrey_uniform_class
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (hdim : Module.finrank ℝ E / 2 + 2 = 3)
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      morreyUniformConst Λ (baseMorreyConst (I := I) (M := M) gBase 0 s)
          (kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s) (Module.finrank ℝ E) s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 :=
  fibreMorrey_uniform_base (I := I) gBase g₀ hEq.1
    (fun y v => hEq.2 y (Set.mem_univ y) v) s
    (fun S j hj =>
      kjet_of_class (I := I) gBase g₀ hEq hjet hJet1 hJet2 hΛ' hΛ'' hdim s S j hj) T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_class ``Submission.DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_class

end RicciFlow
end PDE
end DifferentialGeometry

end
