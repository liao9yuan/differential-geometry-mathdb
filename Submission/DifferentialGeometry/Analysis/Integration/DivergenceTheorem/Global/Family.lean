import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.CompactSupport
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Support
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.ENNReal

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
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

theorem integral_divergence_eq_zero_of_compact_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergenceG (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_eq_zero_of_compact (I := I) (g_fam t) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact_family ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact_family

theorem integral_divergence_eq_zero_of_hasCompactSupport_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, divergenceG (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_eq_zero_of_hasCompactSupport (I := I) (g_fam t) X hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport_family ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport_family

theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * divergenceG (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) (g_fam t) hf X hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence_family ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_eq_neg_integral_smul_divergence_family

theorem integral_tangentSectionAction_mul_add_eq_neg_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * h x * divergenceG (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_mul_add_eq_neg
    (I := I) (g_fam t) hf hh X hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg_family ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_tangentSectionAction_mul_add_eq_neg_family

theorem integral_inner_grad_eq_neg_integral_smul_laplacian_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_support : HasCompactSupport h) (t : ℝ) :
    ∫ x, (g_fam t).inner x
            ((gradG (I := I) (g_fam t) ⟨_, hf⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) (g_fam t) ⟨_, hh⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * ΔG (I := I) (g_fam t) ⟨_, hh⟩ x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) (g_fam t) hf hh hh_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_inner_grad_eq_neg_integral_smul_laplacian_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_inner_grad_eq_neg_integral_smul_laplacian_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_inner_grad_eq_neg_integral_smul_laplacian_family ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_inner_grad_eq_neg_integral_smul_laplacian_family

theorem integral_smul_laplacian_sub_eq_zero_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (t : ℝ) :
    ∫ x, (f x * ΔG (I := I) (g_fam t) ⟨_, hh⟩ x -
            h x * ΔG (I := I) (g_fam t) ⟨_, hf⟩ x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact green_second_integral_smul_laplacian_sub_eq_zero (I := I) (g_fam t) hf hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_smul_laplacian_sub_eq_zero_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_smul_laplacian_sub_eq_zero_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_smul_laplacian_sub_eq_zero_family ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_smul_laplacian_sub_eq_zero_family

theorem volumeVariation_hasDerivAt
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ :=
  first_variation_of_volume (I := I) (M := M) (g_fam := g_fam)
    (f := f) (t₀ := t₀) hg hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.volumeVariation_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.volumeVariation_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.volumeVariation_hasDerivAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.volumeVariation_hasDerivAt

end DivergenceTheorem
end Integral
end DifferentialGeometry
