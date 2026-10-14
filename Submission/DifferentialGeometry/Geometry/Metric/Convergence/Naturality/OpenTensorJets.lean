import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance openTensorJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsC1 target :: scope.openDecls } }
private local instance openTensorJetsC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsC2 target :: scope.openDecls } }
private local instance openTensorJetsRestrictedC1 (U : TopologicalSpace.Opens M) : IsManifold I 1 U :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsRestrictedC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsRestrictedC1 target :: scope.openDecls } }
private local instance openTensorJetsRestrictedC2 (U : TopologicalSpace.Opens M) : IsManifold I 2 U :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsRestrictedC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTensorJetsRestrictedC2 target :: scope.openDecls } }

omit [CompleteSpace E] [T2Space M] in
theorem restrictOpenTensor02Field_apply (U : TopologicalSpace.Opens M)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (x : U)
    (v : Fin 2 → TangentSpace I x) :
    restrictOpen0S (I := I) 2 (V := U) A x v = A (x : M) v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.restrictOpenTensor02Field_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.restrictOpenTensor02Field_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.restrictOpenTensor02Field_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.restrictOpenTensor02Field_apply


theorem tensor02CovDerivNormWith_restrictOpen0S (U : TopologicalSpace.Opens M)
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : U) :
    tensor02CovDerivNormWith a (restrictOpen0S (I := I) 2 (V := U) A)
        (gcov.restrictOpen U) (gnorm.restrictOpen U) x =
      tensor02CovDerivNormWith a A gcov gnorm (x : M) := by
  have htower := covDerivOfField_restrictOpen gcov U
    (restrictOpen0S (I := I) 2 (V := U) A) A
    (restrictOpenTensor02Field_apply U A) a x
  have htensor : covDerivOfField (gcov.restrictOpen U)
      (restrictOpen0S (I := I) 2 (V := U) A) a x = covDerivOfField gcov A a (x : M) :=
    ContinuousMultilinearMap.ext htower
  unfold tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field, htensor]
  congr 1
  exact normSq0S_restrictOpen_apply gnorm U (a + 2) x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_restrictOpen0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_restrictOpen0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_restrictOpen0S ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_restrictOpen0S

omit [CompleteSpace E] [T2Space M] in
theorem hasDerivWithinAt_restrictOpenTensor02Field (U : TopologicalSpace.Opens M)
    (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (A' : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    {times : Set ℝ} {t : ℝ} (x : U) (v : Fin 2 → TangentSpace I x)
    (hA : HasDerivWithinAt (fun s => A s (x : M) v) (A' (x : M) v) times t) :
    HasDerivWithinAt (fun s => restrictOpen0S (I := I) 2 (V := U) (A s) x v)
      (restrictOpen0S (I := I) 2 (V := U) A' x v) times t := hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_restrictOpenTensor02Field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_restrictOpenTensor02Field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_restrictOpenTensor02Field ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_restrictOpenTensor02Field

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
