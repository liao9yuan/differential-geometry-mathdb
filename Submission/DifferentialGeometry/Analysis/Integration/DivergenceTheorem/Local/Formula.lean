import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import Submission.DifferentialGeometry.Tensor.Coordinates.PartialDerivative
import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Vector
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
export DifferentialGeometry.Integral.Measure
  (chartDensityOnE chartDensityOnE_contDiffOn)
export DifferentialGeometry.Tensor.Coordinates
  (chartCoeff chartCoeff_contMDiffOn chartCoeff_def chartCoeff_recompose
    chartCoeffOnE chartCoeffOnE_contDiffOn)

def localDivergence (g : SmoothRiemannianMetric I M)
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    M → ℝ := fun x =>
  (∑ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
        (extChartAt I α x))
    / chartDensity (I := I) g α x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.localDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergence

@[simp] lemma localDivergence_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    localDivergence (I := I) g α X x =
      (∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y => chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_def

theorem localDivergence_eq_sum_fderiv
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    localDivergence (I := I) g α X ((extChartAt I α).symm y) =
      (∑ i : Fin (Module.finrank ℝ E),
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          chartCoeffOnE (I := I) α X i ((toEuclidean (E := E)).symm z) *
            chartDensityOnE (I := I) g α ((toEuclidean (E := E)).symm z))
          (toEuclidean (E := E) y) (EuclideanSpace.single i 1)) /
        chartDensityOnE (I := I) g α y := by
  rw [localDivergence, (extChartAt I α).right_inv hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let F : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun z =>
    chartCoeffOnE (I := I) α X i ((toEuclidean (E := E)).symm z) *
      chartDensityOnE (I := I) g α ((toEuclidean (E := E)).symm z)
  have heq : (fun y => chartCoeffOnE (I := I) α X i y *
      chartDensityOnE (I := I) g α y) = F ∘ toEuclidean (E := E) := by
    ext z
    simp only [Function.comp_apply, F, ContinuousLinearEquiv.symm_apply_apply]
  rw [DifferentialGeometry.Tensor.Coordinates.partialDeriv, heq,
    (toEuclidean (E := E)).comp_right_fderiv, ContinuousLinearMap.comp_apply,
    DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_eq_sum_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_eq_sum_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_eq_sum_fderiv ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_eq_sum_fderiv

lemma chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
  (chartCoeffOnE_contDiffOn (I := I) α X i).mul
    (chartDensityOnE_contDiffOn (I := I) g α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE_mul_chartDensityOnE_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE_mul_chartDensityOnE_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE_mul_chartDensityOnE_contDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE_mul_chartDensityOnE_contDiffOn

private lemma partialDeriv_contDiffOn_interior
    (i : Fin (Module.finrank ℝ E)) {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) (interior s) := by
  have hu_int : ContDiffOn ℝ ∞ u (interior s) := hu.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior s) :=
    hu_int.fderiv_of_isOpen isOpen_interior
      (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
      (interior s) := contDiffOn_const
  exact hfderiv.clm_apply hconst

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_contDiffOn_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_contDiffOn_interior target :: scope.openDecls } }

lemma partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior i
    (chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn

private def localDivergenceDomain (α : M) : Set M :=
  (extChartAt I α).source ∩
    (extChartAt I α) ⁻¹' interior (extChartAt I α).target

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergenceDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.localDivergenceDomain target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma localDivergenceDomain_subset_baseSet (α : M) :
    localDivergenceDomain (I := I) α ⊆
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  rw [← extChartAt_source_eq_chartAt_source (I := I)]
  exact hx.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergenceDomain_subset_baseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.localDivergenceDomain_subset_baseSet target :: scope.openDecls } }

private lemma localDivergence_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (localDivergenceDomain (I := I) α) := by
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
    partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (localDivergenceDomain (I := I) α) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  have hsubset : localDivergenceDomain (I := I) α ⊆
      (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_summand_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_summand_contMDiffOn target :: scope.openDecls } }

private lemma chartDensity_contMDiffOn_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (localDivergenceDomain (I := I) α) :=
  (chartDensity_contMDiffOn (I := I) g α).mono
    (localDivergenceDomain_subset_baseSet (I := I) α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartDensity_contMDiffOn_localDivergenceDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.chartDensity_contMDiffOn_localDivergenceDomain target :: scope.openDecls } }

private lemma chartDensity_ne_zero_on_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ localDivergenceDomain (I := I) α, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt
    (chartDensity_pos (I := I) g α
      (localDivergenceDomain_subset_baseSet (I := I) α hx))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartDensity_ne_zero_on_localDivergenceDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.chartDensity_ne_zero_on_localDivergenceDomain target :: scope.openDecls } }

theorem localDivergence_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  have hnum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (localDivergenceDomain (I := I) α) :=
    contMDiffOn_finsetSum
      (fun i _ => localDivergence_summand_contMDiffOn (I := I) g α X i)
  have hden :
      ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
        (localDivergenceDomain (I := I) α) :=
    chartDensity_contMDiffOn_localDivergenceDomain (I := I) g α
  exact hnum.div₀ hden
    (chartDensity_ne_zero_on_localDivergenceDomain (I := I) g α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_contMDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_contMDiffOn

def divergenceG (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergence (I := I) g x X x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.divergenceG then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.divergenceG"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.divergenceG ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.divergenceG

@[simp] lemma divergence_g_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g X x = localDivergence (I := I) g x X x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_def

theorem divergence_g_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g X x =
      (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (chartCoeffOnE (I := I) x X i) (extChartAt I x x)) +
        (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x X i (extChartAt I x x) *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
              (chartDensityOnE (I := I) g x) (extChartAt I x x)) /
          chartDensity (I := I) g x x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [hy₀_def]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  have hsymm : (extChartAt I x).symm y₀ = x := by
    simp [hy₀_def]
  have hρOnE :
      chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm y₀) =
      chartDensity (I := I) g x x
    rw [hsymm]
  have hcoeff_diff :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (chartCoeffOnE (I := I) x X i) y₀ := by
    intro i
    have hsmooth : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x X i)
        (extChartAt I x).target :=
      chartCoeffOnE_contDiffOn (I := I) x X i
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hprod :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀ =
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀ := by
    intro i
    unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
    have hmul : fderiv ℝ
        (fun y : E =>
          chartCoeffOnE (I := I) x X i y *
            chartDensityOnE (I := I) g x y) y₀ =
        chartCoeffOnE (I := I) x X i y₀ •
          fderiv ℝ (chartDensityOnE (I := I) g x) y₀ +
        chartDensityOnE (I := I) g x y₀ •
          fderiv ℝ (chartCoeffOnE (I := I) x X i) y₀ :=
      fderiv_fun_mul (hcoeff_diff i) hρ_diff
    rw [hmul]
    rw [add_apply,
      smul_apply, smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [divergence_g_def, localDivergence_def]
  change
    (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) /
      chartDensity (I := I) g x x = _
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) =
        ∑ i : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀) by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hprod i]
  rw [Finset.sum_add_distrib]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
          chartDensityOnE (I := I) g x y₀) =
        (∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀) *
          chartDensityOnE (I := I) g x y₀ by
      rw [Finset.sum_mul]]
  rw [hρOnE]
  rw [add_div]
  rw [mul_div_assoc, div_self hρ_ne, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_chart_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_chart_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_chart_product ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_chart_product

end DivergenceTheorem
end Integral
end DifferentialGeometry
