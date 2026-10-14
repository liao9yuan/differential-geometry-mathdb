import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Laplacian
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Gradient
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import Submission.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hh_support : HasCompactSupport h) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * ΔGWithBoundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradGWithBoundarySection (I := I) g hh hh_int with hX_def
  have hX_cs : HasCompactSupport X :=
    hasCompactSupport_grad_g_with_boundary_section (I := I) g hh hh_int hh_support
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have h_ibp :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hf hf_int X hX_cs hX_int
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g X x]
    change g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergenceGWithBoundary (I := I) g X x =
        f x * ΔGWithBoundary (I := I) g hh hh_int x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergenceGWithBoundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * ΔGWithBoundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary

private theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hf_support : HasCompactSupport f) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * ΔGWithBoundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradGWithBoundarySection (I := I) g hf hf_int with hX_def
  have hX_cs : HasCompactSupport X :=
    hasCompactSupport_grad_g_with_boundary_section (I := I) g hf hf_int hf_support
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hf hf_int
  have h_ibp :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hh hh_int X hX_cs hX_int
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g X x]
    rfl
  have hRHS_eq : ∀ x : M,
      h x * divergenceGWithBoundary (I := I) g X x =
        h x * ΔGWithBoundary (I := I) g hf hf_int x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergenceGWithBoundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * ΔGWithBoundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary' target :: scope.openDecls } }

theorem integral_smul_laplacian_sub_eq_zero_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, (f x * ΔGWithBoundary (I := I) g hh hh_int x -
            h x * ΔGWithBoundary (I := I) g hf hf_int x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  have h1 := integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    (I := I) g hf hh hf_int hh_int hh_cs
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
    (I := I) g hf hh hf_int hh_int hf_cs
  have h_eq : ∫ x, f x * ΔGWithBoundary (I := I) g hh hh_int x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * ΔGWithBoundary (I := I) g hf hf_int x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have : -∫ x, f x * ΔGWithBoundary (I := I) g hh hh_int x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * ΔGWithBoundary (I := I) g hf hf_int x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔh_cont : Continuous (ΔGWithBoundary (I := I) g hh hh_int) :=
    Δ_g_with_boundary_continuous (I := I) g hh hh_int
  have hΔf_cont : Continuous (ΔGWithBoundary (I := I) g hf hf_int) :=
    Δ_g_with_boundary_continuous (I := I) g hf hf_int
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : _root_.MeasureTheory.Integrable (fun x : M => f x * ΔGWithBoundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * ΔGWithBoundary (I := I) g hh hh_int x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : _root_.MeasureTheory.Integrable (fun x : M => h x * ΔGWithBoundary (I := I) g hf hf_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * ΔGWithBoundary (I := I) g hf hf_int x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [_root_.MeasureTheory.integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_smul_laplacian_sub_eq_zero_with_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_smul_laplacian_sub_eq_zero_with_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_smul_laplacian_sub_eq_zero_with_boundary ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_smul_laplacian_sub_eq_zero_with_boundary

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
