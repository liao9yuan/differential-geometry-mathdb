import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Gradient
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.Algebra.Support
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
namespace Geometry
namespace Operator
namespace WithBoundary

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.isOpen_interior_M
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.isOpen_interior_M target :: scope.openDecls } }

private lemma gradFun_eq_zero_on_compl_tsupport
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    {x : M} (hx : x ∈ (tsupport f)ᶜ) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hev

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_eq_zero_on_compl_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_eq_zero_on_compl_tsupport target :: scope.openDecls } }

private lemma gradFun_total_eq_zeroSection_on_compl_tsupport
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    {y : M} (hy : y ∈ (tsupport f)ᶜ) :
    TotalSpace.mk' E y (gradFun (I := I) g f y) =
      (Bundle.zeroSection E (TangentSpace I : M → Type _) y) := by
  have hzero : gradFun (I := I) g f y = (0 : TangentSpace I y) :=
    gradFun_eq_zero_on_compl_tsupport (I := I) g hy
  rw [hzero]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_total_eq_zeroSection_on_compl_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_total_eq_zeroSection_on_compl_tsupport target :: scope.openDecls } }

private lemma gradFun_total_contMDiffOn_compl_tsupport
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
      (tsupport f)ᶜ := by
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (Bundle.zeroSection E (TangentSpace I : M → Type _)) :=
    _root_.Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)
  refine (hzero.contMDiffOn).congr ?_
  intro y hy
  exact gradFun_total_eq_zeroSection_on_compl_tsupport (I := I) g hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_total_contMDiffOn_compl_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.gradFun_total_contMDiffOn_compl_tsupport target :: scope.openDecls } }

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma interior_union_compl_tsupport_eq_univ
    {f : M → ℝ} (hf_int : tsupport f ⊆ I.interior M) :
    I.interior M ∪ (tsupport f)ᶜ = (Set.univ : Set M) := by
  refine Set.eq_univ_of_forall ?_
  intro x
  by_cases hx : x ∈ I.interior M
  · exact Or.inl hx
  · refine Or.inr ?_
    intro hx_support
    exact hx (hf_int hx_support)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.interior_union_compl_tsupport_eq_univ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.interior_union_compl_tsupport_eq_univ target :: scope.openDecls } }

def gradGWithBoundarySection (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, by
    have hs_open : IsOpen (I.interior M) := isOpen_interior_M
    have ht_open : IsOpen ((tsupport f)ᶜ) := (isClosed_tsupport _).isOpen_compl
    have hs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
        (I.interior M) :=
      gradFun_contMDiffOn_interior (I := I) g hf
    have ht : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
        ((tsupport f)ᶜ) :=
      gradFun_total_contMDiffOn_compl_tsupport (I := I) g f
    have hcover : I.interior M ∪ (tsupport f)ᶜ = (Set.univ : Set M) :=
      interior_union_compl_tsupport_eq_univ (I := I) (M := M) hf_int
    exact contMDiff_of_contMDiffOn_union_of_isOpen hs ht hcover hs_open ht_open⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection

@[simp] lemma grad_g_with_boundary_section_apply (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    (gradGWithBoundarySection (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply

@[simp] lemma grad_g_with_boundary_section_coe (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    (gradGWithBoundarySection (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradGWithBoundary (I := I) g f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_coe ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_coe

lemma support_grad_g_with_boundary_section_subset (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Function.support
        ((gradGWithBoundarySection (I := I) g hf hf_int :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
          ∀ x, TangentSpace I x) ⊆ tsupport f :=
  support_grad_g_with_boundary_subset (I := I) g f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.support_grad_g_with_boundary_section_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.support_grad_g_with_boundary_section_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.support_grad_g_with_boundary_section_subset ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.support_grad_g_with_boundary_section_subset

lemma tsupport_grad_g_with_boundary_section_subset (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport ((gradGWithBoundarySection (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ∀ x, TangentSpace I x) ⊆ tsupport f :=
  closure_minimal
    (support_grad_g_with_boundary_section_subset (I := I) g hf hf_int)
    (isClosed_tsupport _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset

lemma tsupport_grad_g_with_boundary_section_subset_interior (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport ((gradGWithBoundarySection (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ∀ x, TangentSpace I x) ⊆ I.interior M :=
  (tsupport_grad_g_with_boundary_section_subset (I := I) g hf hf_int).trans hf_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset_interior ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_grad_g_with_boundary_section_subset_interior

lemma hasCompactSupport_grad_g_with_boundary_section [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (hf_cs : HasCompactSupport f) :
    HasCompactSupport
      ((gradGWithBoundarySection (I := I) g hf hf_int :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  exact support_grad_g_with_boundary_section_subset (I := I) g hf hf_int hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_grad_g_with_boundary_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_grad_g_with_boundary_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_grad_g_with_boundary_section ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_grad_g_with_boundary_section

def ΔGWithBoundary (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) : M → ℝ :=
  divergenceGWithBoundary (I := I) g
    (gradGWithBoundarySection (I := I) g hf hf_int)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary

@[simp] lemma Δ_g_with_boundary_def (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    ΔGWithBoundary (I := I) g hf hf_int x =
      divergenceGWithBoundary (I := I) g
        (gradGWithBoundarySection (I := I) g hf hf_int) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_def ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_def

theorem Δ_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ΔGWithBoundary (I := I) g hf hf_int)
      (I.interior M) :=
  divergence_g_with_boundary_contMDiffOn_interior (I := I) g
    (gradGWithBoundarySection (I := I) g hf hf_int)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_contMDiffOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_contMDiffOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_contMDiffOn_interior ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_contMDiffOn_interior

lemma tsupport_Δ_g_with_boundary_subset (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport (ΔGWithBoundary (I := I) g hf hf_int) ⊆ tsupport f := by
  have h1 : tsupport (ΔGWithBoundary (I := I) g hf hf_int) ⊆
      tsupport ((gradGWithBoundarySection (I := I) g hf hf_int :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x, TangentSpace I x) :=
    tsupport_divergence_g_with_boundary_subset
      (I := I) g (gradGWithBoundarySection (I := I) g hf hf_int)
  exact h1.trans (tsupport_grad_g_with_boundary_section_subset (I := I) g hf hf_int)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_Δ_g_with_boundary_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_Δ_g_with_boundary_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_Δ_g_with_boundary_subset ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.tsupport_Δ_g_with_boundary_subset

theorem Δ_g_with_boundary_continuous [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Continuous (ΔGWithBoundary (I := I) g hf hf_int) := by
  classical
  have hΔ_support_int : tsupport (ΔGWithBoundary (I := I) g hf hf_int) ⊆
      I.interior M :=
    (tsupport_Δ_g_with_boundary_subset (I := I) g hf hf_int).trans hf_int
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_support : x ∈ tsupport (ΔGWithBoundary (I := I) g hf hf_int)
  · have hx_int : x ∈ I.interior M := hΔ_support_int hx_support
    have hcont_int : ContinuousOn (ΔGWithBoundary (I := I) g hf hf_int)
        (I.interior M) :=
      (Δ_g_with_boundary_contMDiffOn_interior (I := I) g hf hf_int).continuousOn
    exact (hcont_int x hx_int).continuousAt (isOpen_interior_M.mem_nhds hx_int)
  · have h_open : IsOpen (tsupport (ΔGWithBoundary (I := I) g hf hf_int))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev_zero : (ΔGWithBoundary (I := I) g hf hf_int) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_support] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    exact (continuous_const.continuousAt.congr hev_zero.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_continuous ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Δ_g_with_boundary_continuous

lemma hasCompactSupport_Δ_g_with_boundary [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (hf_cs : HasCompactSupport f) :
    HasCompactSupport (ΔGWithBoundary (I := I) g hf hf_int) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  have h1 : x ∈ tsupport (ΔGWithBoundary (I := I) g hf hf_int) :=
    subset_tsupport _ hx
  exact tsupport_Δ_g_with_boundary_subset (I := I) g hf hf_int h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_Δ_g_with_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_Δ_g_with_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_Δ_g_with_boundary ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.hasCompactSupport_Δ_g_with_boundary

end WithBoundary
end Operator
end Geometry
end DifferentialGeometry
