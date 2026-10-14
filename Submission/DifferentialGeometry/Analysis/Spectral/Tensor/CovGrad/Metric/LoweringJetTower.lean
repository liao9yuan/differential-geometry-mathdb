import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormIdentity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.RankZeroInner
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.MixedCompatibility
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
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

def lowerRSField (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ (r + s) :=
  ⟨liftedTensorSection (I := I) (M := M) g r s T.toSection,
    liftedTensorSection_contMDiff (I := I) (M := M) g r s T.toSection⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerRSField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerRSField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerRSField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerRSField

def lowerCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : SmoothCcTensor g 0 (r + s) where
  toSection := (lowerRSField (I := I) (M := M) g r s T).toTensorRSField ∞
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem lowerCc_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    (lowerCc (I := I) (M := M) g r s T).toSection x =
      Tensor0SSpace.toRS0
        (liftedTensorSection (I := I) (M := M) g r s T.toSection x) := by
  change (lowerRSField (I := I) (M := M) g r s T).toTensorRSField ∞ x = _
  exact Tensor0SField.toRS0_eq (n := (∞ : WithTop ℕ∞))
    (lowerRSField (I := I) (M := M) g r s T) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_apply

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lowerCc_unit (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + s) I x from
      (lowerCc (I := I) (M := M) g r s T).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      liftedTensorSection (I := I) (M := M) g r s T.toSection x := by
  rw [lowerCc_apply, Tensor0SSpace.toRS0_apply]
  rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
  change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1 Fin.elim0 • _ = _
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_unit ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_unit

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lowerCc_riemannianFiberNormSq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + s) x
        ((lowerCc (I := I) (M := M) g r s T).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x) := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise,
    riemannianFiberNormSq_eq_tensorInnerPointwise, lowerCc_apply,
    inner_toRS0 (I := I) (M := M) g (r + s) x]
  exact (tensorInnerPointwise_eq_liftedTensorSection_inner
    (I := I) (M := M) g r s T.toSection T.toSection x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_riemannianFiberNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_riemannianFiberNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_riemannianFiberNormSq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_riemannianFiberNormSq

private def lowerGradPerm (r s : ℕ) : Equiv.Perm (Fin ((r + s) + 1)) :=
  Fin.cycleRange ⟨r, by omega⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerGradPerm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerGradPerm target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lowerCc_grad_rel (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    ∀ y : M,
      unitModel (I := I) (M := M) g ((r + s) + 1)
          (covGrad (I := I) (M := M) g 0 (r + s)
            (lowerCc (I := I) (M := M) g r s T)) y =
        ContinuousMultilinearMap.domDomCongr (lowerGradPerm r s)
          (unitModel (I := I) (M := M) g ((r + s) + 1)
            (lowerCc (I := I) (M := M) g r (s + 1)
              (covGrad (I := I) (M := M) g r s T)) y) := by
  classical
  intro y
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  unfold unitModel
  have hunit : unitTensor (I := I) (M := M) y =
      unitZeroSec (I := I) (M := M) y := rfl
  rw [hunit]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 (r + s)
    (lowerCc (I := I) (M := M) g r s T) y]
  rw [tensorCovDerivAt_def]
  rw [tensorRSCovariantDerivative_zeroS_unit_eval
    (I := I) (M := M) g (r + s)
    (lowerCc (I := I) (M := M) g r s T).toSection y]
  have hsec :
      (fun z : M =>
        (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (r + s) I z from
          (lowerCc (I := I) (M := M) g r s T).toSection z)
          (unitZeroSec (I := I) (M := M) z)) =
        fun z : M => liftedTensorSection (I := I) (M := M)
          g r s T.toSection z := by
    funext z
    exact lowerCc_unit (I := I) (M := M) g r s T z
  rw [hsec]
  change Tensor0SSpace.toModel
      (loweredCovDerivAt (I := I) (M := M) g r s T.toSection y (v 0))
        (Matrix.vecTail v) = _
  rw [loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs
    (I := I) (M := M) g r s T.toSection y (v 0)]
  have hright :
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace ((r + s) + 1) I y from
        (lowerCc (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T)).toSection y)
          (unitZeroSec (I := I) (M := M) y) =
        liftedTensorSection (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T).toSection y := by
    exact lowerCc_unit (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s T) y
  have hright_eval :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace ((r + s) + 1) I y from
            (lowerCc (I := I) (M := M) g r (s + 1)
              (covGrad (I := I) (M := M) g r s T)).toSection y)
            (unitZeroSec (I := I) (M := M) y))
          (fun i => v (lowerGradPerm r s i)) =
        Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s T).toSection y)
          (fun i => v (lowerGradPerm r s i)) := by
    exact congrArg
      (fun W : Tensor0SSpace ((r + s) + 1) I y =>
        Tensor0SSpace.toModel W (fun i => v (lowerGradPerm r s i))) hright
  apply Eq.trans ?_ hright_eval.symm
  rw [toModel_liftedTensorSection]
  rw [lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  have hcg (Dm : Tensor0SModel r ℝ E)
      (u : Fin (s + 1) → E) :
      TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s T).toSection y) Dm u =
        TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T y (u 0)) Dm
            (Matrix.vecTail u) := by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (covGrad (I := I) (M := M) g r s T).toSection y)
          (Tensor0SSpace.ofModel Dm)) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
          tensorCovDerivAt (I := I) (M := M) g r s T y (u 0))
          (Tensor0SSpace.ofModel Dm)) (Matrix.vecTail u)
    exact covGrad_toSection_apply_eval (I := I) (M := M) g r s T y
      (Tensor0SSpace.ofModel Dm) u
  rw [hcg]
  have hupper :
      (fun a : Fin r =>
        v (lowerGradPerm r s (Fin.castAdd (s + 1) a))) =
        fun a : Fin r => Matrix.vecTail v (Fin.castAdd s a) := by
    funext a
    have hidx : lowerGradPerm r s (Fin.castAdd (s + 1) a) =
        (Fin.castAdd s a).succ := by
      apply Fin.ext
      simp only [lowerGradPerm, Fin.val_succ, Fin.val_castAdd]
      rw [Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
      simp only [Fin.val_castAdd]
    exact congrArg v hidx
  have hdir : lowerGradPerm r s (Fin.natAdd r (0 : Fin (s + 1))) = 0 := by
    rw [lowerGradPerm,
      show Fin.natAdd r (0 : Fin (s + 1)) =
          (⟨r, by omega⟩ : Fin ((r + s) + 1)) from by ext; simp,
      Fin.cycleRange_self]
  have hlower :
      (fun a : Fin s =>
        v (lowerGradPerm r s (Fin.natAdd r a.succ))) =
        fun a : Fin s => Matrix.vecTail v (Fin.natAdd r a) := by
    funext a
    have hidx : lowerGradPerm r s (Fin.natAdd r a.succ) =
        (Fin.natAdd r a).succ := by
      rw [lowerGradPerm, Fin.cycleRange_of_gt
        (by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_succ]; omega)]
      ext
      simp only [Fin.val_natAdd, Fin.val_succ]
      omega
    exact congrArg v hidx
  rw [hupper, hdir]
  congr 1
  exact hlower.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_grad_rel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_grad_rel target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma lowerCc_grad_riemannianFiberNormSq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((r + s) + 1) x
        ((covGrad (I := I) (M := M) g 0 (r + s)
          (lowerCc (I := I) (M := M) g r s T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s T).toSection x) := by
  have hperm :=
    riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
      (I := I) (M := M) g ((r + s) + 1) (lowerGradPerm r s)
      (lowerCc (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T))
      (covGrad (I := I) (M := M) g 0 (r + s)
        (lowerCc (I := I) (M := M) g r s T))
      (lowerCc_grad_rel (I := I) (M := M) g r s T) 0 x
  have hlower := lowerCc_riemannianFiberNormSq (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T) x
  simpa only [iteratedCovGrad_zero, Nat.add_zero] using hperm.trans hlower

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_grad_riemannianFiberNormSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_grad_riemannianFiberNormSq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lowerCc_jet_riemannianFiberNormSq (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (T : SmoothCcTensor g r s) (hj : j ≤ 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((r + s) + j) x
        ((Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
          (lowerCc (I := I) (M := M) g r s T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g r s j T).toSection x) := by
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · simpa only [iteratedCovGrad_zero, Nat.add_zero] using
      lowerCc_riemannianFiberNormSq (I := I) (M := M) g r s T x
  · simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero] using
      lowerCc_grad_riemannianFiberNormSq (I := I) (M := M) g r s T x
  · have hperm :=
      riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
        (I := I) (M := M) g ((r + s) + 1) (lowerGradPerm r s)
        (lowerCc (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T))
        (covGrad (I := I) (M := M) g 0 (r + s)
          (lowerCc (I := I) (M := M) g r s T))
        (lowerCc_grad_rel (I := I) (M := M) g r s T) 1 x
    have hnext := lowerCc_grad_riemannianFiberNormSq (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s T) x
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero] using
      hperm.trans hnext

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_riemannianFiberNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_riemannianFiberNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_riemannianFiberNormSq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_riemannianFiberNormSq

omit [NeZero (Module.finrank ℝ E)] in
theorem lowerCc_jet_norm (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (T : SmoothCcTensor g r s) (hj : j ≤ 2) :
    ‖Analysis.Sobolev.iteratedCovGrad
        (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
        (lowerCc (I := I) (M := M) g r s T)‖ =
      ‖Analysis.Sobolev.iteratedCovGrad
        (E := E) (H := H) (I := I) (M := M) g r s j T‖ := by
  have hsq :
      ‖Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
          (lowerCc (I := I) (M := M) g r s T)‖ ^ 2 =
        ‖Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g r s j T‖ ^ 2 := by
    have hleftSq :
        ‖Analysis.Sobolev.iteratedCovGrad
            (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
            (lowerCc (I := I) (M := M) g r s T)‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 ((r + s) + j) x
            ((Analysis.Sobolev.iteratedCovGrad
              (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
              (lowerCc (I := I) (M := M) g r s T)).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [SmoothCcTensor.norm_def]
      have hbridge := tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g 0 ((r + s) + j)
        (fun x => (Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
          (lowerCc (I := I) (M := M) g r s T)).toSection x)
      rw [show (Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
          (lowerCc (I := I) (M := M) g r s T)).toFun =
        fun x => TensorRSSpace.toModel
          ((Analysis.Sobolev.iteratedCovGrad
            (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
            (lowerCc (I := I) (M := M) g r s T)).toSection x) from rfl]
      exact hbridge
    have hrightSq :
        ‖Analysis.Sobolev.iteratedCovGrad
            (E := E) (H := H) (I := I) (M := M) g r s j T‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
            ((Analysis.Sobolev.iteratedCovGrad
              (E := E) (H := H) (I := I) (M := M) g r s j T).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [SmoothCcTensor.norm_def]
      have hbridge := tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g r (s + j)
        (fun x => (Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g r s j T).toSection x)
      rw [show (Analysis.Sobolev.iteratedCovGrad
          (E := E) (H := H) (I := I) (M := M) g r s j T).toFun =
        fun x => TensorRSSpace.toModel
          ((Analysis.Sobolev.iteratedCovGrad
            (E := E) (H := H) (I := I) (M := M) g r s j T).toSection x) from rfl]
      exact hbridge
    rw [hleftSq, hrightSq]
    exact _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (lowerCc_jet_riemannianFiberNormSq (I := I) (M := M) g r s j T hj))
  have hleft : 0 ≤ ‖Analysis.Sobolev.iteratedCovGrad
      (E := E) (H := H) (I := I) (M := M) g 0 (r + s) j
      (lowerCc (I := I) (M := M) g r s T)‖ := norm_nonneg _
  have hright : 0 ≤ ‖Analysis.Sobolev.iteratedCovGrad
      (E := E) (H := H) (I := I) (M := M) g r s j T‖ := norm_nonneg _
  rw [← Real.sqrt_sq hleft, ← Real.sqrt_sq hright, hsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.lowerCc_jet_norm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
