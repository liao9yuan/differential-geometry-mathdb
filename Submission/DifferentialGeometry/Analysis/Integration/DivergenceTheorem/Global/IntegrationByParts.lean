import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula
import Submission.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.PartitionOfUnity
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Support
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

lemma Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact hf.integrable_of_hasCompactSupport hcs

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Integral.DivergenceTheorem.Continuous
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_mul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h) (x : M) :
    tangentSectionAction (I := I) X (f * h) x =
      tangentSectionAction (I := I) X f x * h x +
        f x * tangentSectionAction (I := I) X h x := by
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  have hh_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
    hh.mdifferentiableAt (by simp)
  set f' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x
  set h' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) h x
  set fh' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (f * h) x
  have hf_hasMF : HasMFDerivAt I 𝓘(ℝ, ℝ) f x f' := hf_mdiff.hasMFDerivAt
  have hh_hasMF : HasMFDerivAt I 𝓘(ℝ, ℝ) h x h' := hh_mdiff.hasMFDerivAt
  have hmul : HasMFDerivAt I 𝓘(ℝ, ℝ) (f * h) x (f x • h' + h x • f') :=
    hf_hasMF.mul hh_hasMF
  have hmfderiv_eq : fh' = f x • h' + h x • f' := hmul.mfderiv
  change fh' (X x) = f' (X x) * h x + f x * h' (X x)
  rw [hmfderiv_eq]
  rw [add_apply, smul_apply,
      smul_apply]
  rw [smul_eq_mul, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_mul ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_mul

theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := smoothSmul (I := I) f hf X with hY_def
  have hY_support : Function.support (Y : ∀ x, TangentSpace I x) ⊆
      Function.support (X : ∀ x, TangentSpace I x) := by
    intro x hx
    by_contra hneX
    have hXx : X x = 0 := Function.notMem_support.mp hneX
    have hYx : (Y : ∀ x, TangentSpace I x) x = (0 : TangentSpace I x) := by
      change f x • X x = (0 : TangentSpace I x)
      rw [hXx]
      exact smul_zero _
    exact hx hYx
  have hY_cs : HasCompactSupport Y := by
    refine HasCompactSupport.of_support_subset_isCompact (hX : IsCompact (tsupport X)) ?_
    exact hY_support.trans (subset_tsupport _)
  have hY_div : ∀ x : M,
      divergenceG (I := I) g Y x =
        f x * divergenceG (I := I) g X x + tangentSectionAction (I := I) X f x :=
    divergence_g_smoothSmul (I := I) g f hf X
  have hf_cont : Continuous f := hf.continuous
  have hX_div_cont : Continuous (divergenceG (I := I) g X) :=
    (divergence_g_contMDiff (I := I) g X).continuous
  have hAct_cont : Continuous (tangentSectionAction (I := I) X f) :=
    (tangentSectionAction_contMDiff (I := I) X hf).continuous
  have hX_div_cs : HasCompactSupport (divergenceG (I := I) g X) :=
    hasCompactSupport_divergence_g (I := I) g hX
  have hAct_cs : HasCompactSupport (tangentSectionAction (I := I) X f) :=
    hasCompactSupport_tangentSectionAction (I := I) hX f
  have hMul_cont : Continuous (fun x : M => f x * divergenceG (I := I) g X x) :=
    hf_cont.mul hX_div_cont
  have hMul_cs : HasCompactSupport (fun x : M => f x * divergenceG (I := I) g X x) :=
    hX_div_cs.mul_left
  have h_div_Y_zero :
      ∫ x, divergenceG (I := I) g Y x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Y hY_cs
  have h_eq_pointwise : ∀ x : M, divergenceG (I := I) g Y x =
      f x * divergenceG (I := I) g X x + tangentSectionAction (I := I) X f x :=
    hY_div
  have h_div_Y_split :
      ∫ x, divergenceG (I := I) g Y x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * divergenceG (I := I) g X x +
                tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_eq_pointwise x
  have h_int_mul : _root_.MeasureTheory.Integrable (fun x : M => f x * divergenceG (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hMul_cont hMul_cs
  have h_int_act : _root_.MeasureTheory.Integrable (tangentSectionAction (I := I) X f)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hAct_cont hAct_cs
  have h_int_split :
      ∫ x, (f x * divergenceG (I := I) g X x +
              tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, f x * divergenceG (I := I) g X x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
          ∫ x, tangentSectionAction (I := I) X f x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_add h_int_mul h_int_act
  have h_sum_zero :
      ∫ x, f x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ x, tangentSectionAction (I := I) X f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    rw [← h_int_split, ← h_div_Y_split]; exact h_div_Y_zero
  linarith [h_sum_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence

theorem integral_tangentSectionAction_mul_add_eq_neg
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * h x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hfh : ContMDiff I 𝓘(ℝ) ∞ (f * h) := hf.mul hh
  have h_a := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hfh X hX
  have h_leibniz : ∀ x : M,
      tangentSectionAction (I := I) X (f * h) x =
        tangentSectionAction (I := I) X f x * h x +
          f x * tangentSectionAction (I := I) X h x := fun x =>
    tangentSectionAction_mul (I := I) X hf hh x
  have h_lhs_eq :
      ∫ x, tangentSectionAction (I := I) X (f * h) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (tangentSectionAction (I := I) X f x * h x +
                f x * tangentSectionAction (I := I) X h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_leibniz x
  rw [← h_lhs_eq, h_a]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg

end DivergenceTheorem
end Integral
end DifferentialGeometry
