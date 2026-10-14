import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X}
    {f h : X → ℝ} {s : Set X} (hs : MeasurableSet s)
    (h_restrict : f =ᵐ[μ.restrict s] h)
    (h_compl : ∀ x, x ∉ s → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ s := by
    intro x hx
    by_contra hxs
    exact hx (h_compl x hxs)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ s :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact hs.nullMeasurableSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_of_ae_eq_restrict_of_eqOn_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_of_ae_eq_restrict_of_eqOn_compl target :: scope.openDecls } }


def transportCoeffManifold
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) : M → ℝ :=
  fun x =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma transportCoeffManifold_apply
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (x : M) :
    transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x =
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_apply

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportCoeffManifold_eq_zero_of_cutoffα_zero
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x = 0 := by
  rw [transportCoeffManifold_apply, hx]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_eq_zero_of_cutoffα_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_eq_zero_of_cutoffα_zero target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportCoeffManifold_eq_zero_of_cutoffβ_zero
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x = 0 := by
  rw [transportCoeffManifold_apply, hx]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_eq_zero_of_cutoffβ_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffManifold_eq_zero_of_cutoffβ_zero target :: scope.openDecls } }

private def transportSupportSet (α β : M) : Set M :=
  tsupport ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∩
    tsupport ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_isCompact (α β : M) :
    IsCompact (transportSupportSet (I := I) (M := M) α β) :=
  (chartKernelCutoff_hasCompactSupport (I := I) (M := M) α).inter_right
    (isClosed_tsupport _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_isCompact target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_isClosed (α β : M) :
    IsClosed (transportSupportSet (I := I) (M := M) α β) :=
  (isClosed_tsupport _).inter (isClosed_tsupport _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_isClosed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_isClosed target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_subset_sourceα (α β : M) :
    transportSupportSet (I := I) (M := M) α β ⊆ (chartAt H α).source :=
  fun _ hx => chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_subset_sourceα
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_subset_sourceα target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_subset_sourceβ (α β : M) :
    transportSupportSet (I := I) (M := M) α β ⊆ (chartAt H β).source :=
  fun _ hx => chartKernelCutoff_tsupport_subset_source (I := I) (M := M) β hx.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_subset_sourceβ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportSupportSet_subset_sourceβ target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_transportCoeffManifold_subset
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    tsupport (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) ⊆
      transportSupportSet (I := I) (M := M) α β := by
  refine closure_minimal ?_ (transportSupportSet_isClosed (I := I) (M := M) α β)
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨?_, ?_⟩
  · by_contra hxα
    exact hx (transportCoeffManifold_eq_zero_of_cutoffα_zero
      (I := I) (M := M) r s β α P₀ Q
      (image_eq_zero_of_notMem_tsupport hxα))
  · by_contra hxβ
    exact hx (transportCoeffManifold_eq_zero_of_cutoffβ_zero
      (I := I) (M := M) r s β α P₀ Q
      (image_eq_zero_of_notMem_tsupport hxβ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasCompactSupport_transportCoeffManifold
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) :=
  HasCompactSupport.of_support_subset_isCompact
    (transportSupportSet_isCompact (I := I) (M := M) α β)
    (fun _ hx => tsupport_transportCoeffManifold_subset
      (I := I) (M := M) r s β α P₀ Q (subset_tsupport _ hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.hasCompactSupport_transportCoeffManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.hasCompactSupport_transportCoeffManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.hasCompactSupport_transportCoeffManifold ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.hasCompactSupport_transportCoeffManifold

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_transportCoeffManifold_subset_sourceα
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    tsupport (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) ⊆
      (chartAt H α).source :=
  (tsupport_transportCoeffManifold_subset (I := I) (M := M) r s β α P₀ Q).trans
    (transportSupportSet_subset_sourceα (I := I) (M := M) α β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceα then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceα"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceα ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceα

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_transportCoeffManifold_subset_sourceβ
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    tsupport (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) ⊆
      (chartAt H β).source :=
  (tsupport_transportCoeffManifold_subset (I := I) (M := M) r s β α P₀ Q).trans
    (transportSupportSet_subset_sourceβ (I := I) (M := M) α β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceβ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceβ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceβ ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tsupport_transportCoeffManifold_subset_sourceβ

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem contMDiff_transportCoeffManifold
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) := by
  classical
  intro x
  by_cases hx_overlap : x ∈ (chartAt H β).source ∩ (chartAt H α).source
  · have hcutα : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (fun y : M => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
          M → ℝ) y) x :=
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt
    have hcutβ : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (fun y : M => ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
          M → ℝ) y) x :=
      ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt
    have h_overlap_open : IsOpen
        ((chartAt H β).source ∩ (chartAt H α).source) :=
      (chartAt H β).open_source.inter (chartAt H α).open_source
    have hcoeff_on :=
      contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q
    have hcoeff_at : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q) x :=
      hcoeff_on.contMDiffAt (h_overlap_open.mem_nhds hx_overlap)
    have hprod : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) x := by
      have := (hcutα.mul hcutβ).mul hcoeff_at
      unfold transportCoeffManifold
      convert this using 1
      funext y
      rfl
    exact hprod
  · have hsupp_sub := tsupport_transportCoeffManifold_subset
      (I := I) (M := M) r s β α P₀ Q
    have hx_notin : x ∉ tsupport (transportCoeffManifold
        (I := I) (M := M) r s β α P₀ Q) := by
      intro hxsupp
      have hxss := hsupp_sub hxsupp
      exact hx_overlap ⟨transportSupportSet_subset_sourceβ
        (I := I) (M := M) α β hxss,
        transportSupportSet_subset_sourceα (I := I) (M := M) α β hxss⟩
    refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : M => (0 : ℝ)) contMDiffAt_const ?_
    have hopen : IsOpen (tsupport (transportCoeffManifold
        (I := I) (M := M) r s β α P₀ Q))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notin : y ∉ Function.support (transportCoeffManifold
        (I := I) (M := M) r s β α P₀ Q) := fun h => hy (subset_tsupport _ h)
    by_contra hne
    exact hy_notin hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_transportCoeffManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_transportCoeffManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_transportCoeffManifold ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_transportCoeffManifold

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma continuous_transportCoeffManifold
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    Continuous (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) :=
  (contMDiff_transportCoeffManifold (I := I) (M := M) r s β α P₀ Q).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_transportCoeffManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_transportCoeffManifold target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_bound_transportCoeffManifold
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_transportCoeffManifold (I := I) (M := M) r s β α P₀
      Q).exists_bound_of_continuous
      (continuous_transportCoeffManifold (I := I) (M := M) r s β α P₀ Q)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx := hC x
  rw [Real.norm_eq_abs] at hx
  exact hx.trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_transportCoeffManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_transportCoeffManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_transportCoeffManifold ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_transportCoeffManifold

private def transportCoeffPushed
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffPushed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportCoeffPushed target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_bound_transportCoeffPushed
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, |transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y| ≤ C := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_transportCoeffManifold (I := I) (M := M) r s β α P₀ Q
  refine ⟨C, hC_nn, fun y => ?_⟩
  unfold transportCoeffPushed
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    exact hC _
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy, abs_zero]
    exact hC_nn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_transportCoeffPushed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_transportCoeffPushed target :: scope.openDecls } }

private structure TransportDiffeoData
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) where
  Ωαβ : Set EuclN
  Ωβα : Set EuclN
  hΩαβ_open : IsOpen Ωαβ
  hΩαβ_subset_target : Ωαβ ⊆ chartTargetEuclid (I := I) (M := M) α
  hΩβα_subset_target : Ωβα ⊆ chartTargetEuclid (I := I) (M := M) β
  Φ : SmoothDiffeoBoundedAtOrder (Module.finrank ℝ E) Ωαβ Ωβα 0
  hΦ_eq : ∀ y ∈ Ωαβ, Φ.toFun y = chartTransitionEuclid (I := I) (M := M) α β y
  hsupp_subset : ∀ y, transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y ≠ 0 →
    y ∈ Ωαβ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TransportDiffeoData
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TransportDiffeoData target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_transportDiffeoData
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    Nonempty (TransportDiffeoData (I := I) (M := M) r s β α P₀ Q) := by
  classical
  obtain ⟨Ωαβ, Ωβα, hΩαβ_open, _hΩβα_open, hΩαβ_subset_target,
    hΩβα_subset_target, _hΩαβ_overlap, _hΩβα_overlap, h_image_subset, Φ,
    hΦ_eq, _hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α β
      (transportSupportSet_isCompact (I := I) (M := M) α β)
      (transportSupportSet_subset_sourceα (I := I) (M := M) α β)
      (transportSupportSet_subset_sourceβ (I := I) (M := M) α β)
      0
  refine ⟨{
    Ωαβ := Ωαβ
    Ωβα := Ωβα
    hΩαβ_open := hΩαβ_open
    hΩαβ_subset_target := hΩαβ_subset_target
    hΩβα_subset_target := hΩβα_subset_target
    Φ := Φ
    hΦ_eq := hΦ_eq
    hsupp_subset := ?_ }⟩
  intro y hy
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hcoeff_ne : transportCoeffManifold (I := I) (M := M) r s β α P₀ Q z ≠ 0 := by
      intro h0
      apply hy
      unfold transportCoeffPushed
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target, ← hz_def, h0]
    have hz_support : z ∈ transportSupportSet (I := I) (M := M) α β :=
      tsupport_transportCoeffManifold_subset (I := I) (M := M) r s β α P₀ Q
        (subset_tsupport _ (Function.mem_support.mpr hcoeff_ne))
    have hy_eq_image : (toEuclidean (E := E)) (extChartAt I α z) = y := by
      rw [hz_def, (extChartAt I α).right_inv hsymm_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hy_in_image :
        y ∈ ((toEuclidean : E ≃L[ℝ] _) ∘ extChartAt I α) ''
          (transportSupportSet (I := I) (M := M) α β) :=
      ⟨z, hz_support, hy_eq_image⟩
    exact h_image_subset hy_in_image
  · exact absurd
      (by unfold transportCoeffPushed
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target) hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_transportDiffeoData
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_transportDiffeoData target :: scope.openDecls } }

private def transportFun
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ :=
  fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
    (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_eq_comp_Φ
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    transportFun (I := I) (M := M) r s β α P₀ Q f =
      fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
        (f : EuclN → ℝ) (D.Φ.toFun y) := by
  funext y
  unfold transportFun
  by_cases hy : transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y = 0
  · rw [hy, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
  · rw [D.hΦ_eq y (D.hsupp_subset y hy)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_eq_comp_Φ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_eq_comp_Φ target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_eq_zero_off_Ωαβ
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) {y : EuclN}
    (hy : y ∉ D.Ωαβ) :
    transportFun (I := I) (M := M) r s β α P₀ Q f y = 0 := by
  unfold transportFun
  have hcoeff : transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y = 0 := by
    by_contra hne
    exact hy (D.hsupp_subset y hne)
  rw [hcoeff, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_eq_zero_off_Ωαβ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_eq_zero_off_Ωαβ target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_eq_indicator
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    transportFun (I := I) (M := M) r s β α P₀ Q f =
      D.Ωαβ.indicator (fun y => transportCoeffPushed
        (I := I) (M := M) r s β α P₀ Q y * (f : EuclN → ℝ) (D.Φ.toFun y)) := by
  funext y
  by_cases hy : y ∈ D.Ωαβ
  · rw [Set.indicator_of_mem hy,
      transportFun_eq_comp_Φ (I := I) (M := M) r s β α P₀ Q D f]
  · rw [Set.indicator_of_notMem hy,
      transportFun_eq_zero_off_Ωαβ (I := I) (M := M) r s β α P₀ Q D f hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_eq_indicator
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_eq_indicator target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartLebesgueMeasure_restrict_Ωαβ
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q) :
    (chartLebesgueMeasure (I := I) (M := M) α).restrict D.Ωαβ =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωαβ := by
  rw [chartLebesgueMeasure, Measure.restrict_restrict_of_subset D.hΩαβ_subset_target]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLebesgueMeasure_restrict_Ωαβ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLebesgueMeasure_restrict_Ωαβ target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Ωαβ_measurableSet
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q) :
    MeasurableSet D.Ωαβ :=
  D.hΩαβ_open.measurableSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Ωαβ_measurableSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Ωαβ_measurableSet target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma aestronglyMeasurable_transportCoeffPushed
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (transportCoeffPushed (I := I) (M := M) r s β α P₀ Q)
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  unfold transportCoeffPushed chartLebesgueMeasure
  refine ContinuousOn.aestronglyMeasurable ?_
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_inner : ContinuousOn
      (fun y : EuclN => (transportCoeffManifold
        (I := I) (M := M) r s β α P₀ Q)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (continuous_transportCoeffManifold
      (I := I) (M := M) r s β α P₀ Q).comp_continuousOn ?_
    refine (continuousOn_extChartAt_symm α).comp
      (toEuclidean (E := E)).symm.continuous.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  refine h_inner.congr ?_
  intro y hy
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_transportCoeffPushed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_transportCoeffPushed target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma aestronglyMeasurable_transportFun
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    AEStronglyMeasurable (transportFun (I := I) (M := M) r s β α P₀ Q f)
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  rw [transportFun_eq_indicator (I := I) (M := M) r s β α P₀ Q D f]
  rw [aestronglyMeasurable_indicator_iff
    (Ωαβ_measurableSet (I := I) (M := M) r s β α P₀ Q D),
    chartLebesgueMeasure_restrict_Ωαβ (I := I) (M := M) r s β α P₀ Q D]
  have h_coeff : _root_.MeasureTheory.AEStronglyMeasurable
      (transportCoeffPushed (I := I) (M := M) r s β α P₀ Q)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωαβ) := by
    have h := aestronglyMeasurable_transportCoeffPushed
      (I := I) (M := M) r s β α P₀ Q
    rw [← chartLebesgueMeasure_restrict_Ωαβ (I := I) (M := M) r s β α P₀ Q D]
    exact h.restrict
  have h_f_meas : _root_.MeasureTheory.AEStronglyMeasurable (f : EuclN → ℝ)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωβα) :=
    (Lp.aestronglyMeasurable f).mono_measure
      (by rw [chartLebesgueMeasure]
          exact Measure.restrict_mono D.hΩβα_subset_target le_rfl)
  have h_comp : _root_.MeasureTheory.AEStronglyMeasurable (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωαβ) :=
    h_f_meas.comp_quasiMeasurePreserving D.Φ.toFun_quasiMeasurePreserving
  exact h_coeff.mul h_comp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_transportFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_transportFun target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_eLpNorm_transportFun_bound
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β),
        eLpNorm (transportFun (I := I) (M := M) r s β α P₀ Q f) 2
            (chartLebesgueMeasure (I := I) (M := M) α) ≤
          ENNReal.ofReal K * _root_.MeasureTheory.eLpNorm (f : EuclN → ℝ) 2
            (chartLebesgueMeasure (I := I) (M := M) β) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_transportCoeffPushed (I := I) (M := M) r s β α P₀ Q
  set Kchg : ℝ := (1 / D.Φ.jacobianLowerBound) ^ (1 / (2 : ℝ≥0∞).toReal)
    with hKchg_def
  have hjLB_pos : 0 < D.Φ.jacobianLowerBound := D.Φ.jacobian_lower_bound_pos
  have hKchg_nn : 0 ≤ Kchg := by
    rw [hKchg_def]
    have h_inv_nn : (0 : ℝ) ≤ 1 / D.Φ.jacobianLowerBound := by positivity
    exact Real.rpow_nonneg h_inv_nn _
  refine ⟨C * Kchg, mul_nonneg hC_nn hKchg_nn, fun f => ?_⟩
  have h_pointwise : ∀ y, ‖transportFun (I := I) (M := M) r s β α P₀ Q f y‖ ≤
      ‖(C • D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) y‖ := by
    intro y
    rw [transportFun_eq_indicator (I := I) (M := M) r s β α P₀ Q D f]
    by_cases hy : y ∈ D.Ωαβ
    · rw [Set.indicator_of_mem hy, Pi.smul_apply, Set.indicator_of_mem hy,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, smul_eq_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ((hC _).trans ?_) (abs_nonneg _)
      exact le_abs_self C
    · rw [Set.indicator_of_notMem hy, norm_zero]
      positivity
  have h_step1 : _root_.MeasureTheory.eLpNorm (transportFun (I := I) (M := M) r s β α P₀ Q f) 2
      (chartLebesgueMeasure (I := I) (M := M) α) ≤
        ENNReal.ofReal C *
          _root_.MeasureTheory.eLpNorm (D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) 2
            (chartLebesgueMeasure (I := I) (M := M) α) := by
    refine (_root_.MeasureTheory.eLpNorm_mono_ae (Filter.Eventually.of_forall h_pointwise)).trans ?_
    rw [show (C • D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) =
        (C : ℝ) • D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) from rfl]
    refine (_root_.MeasureTheory.eLpNorm_const_smul_le).trans ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_nn]
  have h_indic : _root_.MeasureTheory.eLpNorm
      (D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) 2
        (chartLebesgueMeasure (I := I) (M := M) α) =
      _root_.MeasureTheory.eLpNorm (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωαβ) := by
    rw [_root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
      (Ωαβ_measurableSet (I := I) (M := M) r s β α P₀ Q D),
      chartLebesgueMeasure_restrict_Ωαβ (I := I) (M := M) r s β α P₀ Q D]
  have h_chg : _root_.MeasureTheory.eLpNorm (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωαβ) ≤
        ENNReal.ofReal Kchg *
          eLpNorm (f : EuclN → ℝ) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωβα) := by
    rw [hKchg_def]
    exact D.Φ.eLpNorm_comp_toFun_le_const (by norm_num) (by norm_num)
      D.hΩαβ_open (f : EuclN → ℝ)
  have h_mono : _root_.MeasureTheory.eLpNorm (f : EuclN → ℝ) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωβα) ≤
        eLpNorm (f : EuclN → ℝ) 2 (chartLebesgueMeasure (I := I) (M := M) β) := by
    have h_le : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωβα ≤
        chartLebesgueMeasure (I := I) (M := M) β :=
      Measure.restrict_mono D.hΩβα_subset_target le_rfl
    exact _root_.MeasureTheory.eLpNorm_mono_measure _ h_le
  calc _root_.MeasureTheory.eLpNorm (transportFun (I := I) (M := M) r s β α P₀ Q f) 2
        (chartLebesgueMeasure (I := I) (M := M) α)
      ≤ ENNReal.ofReal C *
          _root_.MeasureTheory.eLpNorm (D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) 2
            (chartLebesgueMeasure (I := I) (M := M) α) := h_step1
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωαβ) := by rw [h_indic]
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal Kchg *
            _root_.MeasureTheory.eLpNorm (f : EuclN → ℝ) 2
              ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωβα)) :=
          mul_le_mul_of_nonneg_left h_chg (zero_le)
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal Kchg *
            eLpNorm (f : EuclN → ℝ) 2 (chartLebesgueMeasure (I := I) (M := M) β)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_mono (zero_le)) (zero_le)
    _ = ENNReal.ofReal (C * Kchg) *
            eLpNorm (f : EuclN → ℝ) 2 (chartLebesgueMeasure (I := I) (M := M) β) := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_transportFun_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_transportFun_bound target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_transportFun
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    MemLp (transportFun (I := I) (M := M) r s β α P₀ Q f) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  refine ⟨aestronglyMeasurable_transportFun (I := I) (M := M) r s β α P₀ Q D f,
    ?_⟩
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_eLpNorm_transportFun_bound (I := I) (M := M) r s β α P₀ Q D
  refine lt_of_le_of_lt (hK f) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact (Lp.memLp f).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_transportFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_transportFun target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_aux_ae_eq
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    {u₁ u₂ : EuclN → ℝ}
    (huv : u₁ =ᵐ[chartLebesgueMeasure (I := I) (M := M) β] u₂) :
    (fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
        u₁ (chartTransitionEuclid (I := I) (M := M) α β y)) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
        u₂ (chartTransitionEuclid (I := I) (M := M) α β y) := by
  classical
  set Ωαβ := D.Ωαβ with hΩαβ_def
  have hΩαβ_meas : MeasurableSet Ωαβ :=
    Ωαβ_measurableSet (I := I) (M := M) r s β α P₀ Q D
  have huv_Ωβα : u₁ =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict D.Ωβα] u₂ :=
    huv.filter_mono
      (_root_.MeasureTheory.ae_mono (Measure.restrict_mono D.hΩβα_subset_target le_rfl))
  have h_comp_Ωαβ : (fun y => u₁ (D.Φ.toFun y)) =ᵐ[
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ωαβ]
        fun y => u₂ (D.Φ.toFun y) :=
    D.Φ.toFun_quasiMeasurePreserving.ae_eq huv_Ωβα
  have h_meas_eq : (chartLebesgueMeasure (I := I) (M := M) α).restrict Ωαβ =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ωαβ :=
    chartLebesgueMeasure_restrict_Ωαβ (I := I) (M := M) r s β α P₀ Q D
  have h_restrict : (fun y => transportCoeffPushed
      (I := I) (M := M) r s β α P₀ Q y *
        u₁ (chartTransitionEuclid (I := I) (M := M) α β y)) =ᵐ[
      (chartLebesgueMeasure (I := I) (M := M) α).restrict Ωαβ]
        fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
          u₂ (chartTransitionEuclid (I := I) (M := M) α β y) := by
    rw [h_meas_eq]
    have h_self : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ωαβ), y ∈ Ωαβ :=
      _root_.MeasureTheory.self_mem_ae_restrict hΩαβ_meas
    filter_upwards [h_comp_Ωαβ, h_self] with y hy_eq hy_mem
    have hΦ : chartTransitionEuclid (I := I) (M := M) α β y = D.Φ.toFun y :=
      (D.hΦ_eq y hy_mem).symm
    rw [hΦ, hy_eq]
  refine ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩαβ_meas h_restrict ?_
  intro y hy
  have hcoeff : transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y = 0 := by
    by_contra hne
    exact hy (D.hsupp_subset y hne)
  rw [hcoeff, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_aux_ae_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_aux_ae_eq target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_ae_eq_of_coeFn_ae_eq
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    {f₁ f₂ : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)}
    (h : (f₁ : EuclN → ℝ) =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (f₂ : EuclN → ℝ)) :
    transportFun (I := I) (M := M) r s β α P₀ Q f₁ =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      transportFun (I := I) (M := M) r s β α P₀ Q f₂ :=
  transportFun_aux_ae_eq (I := I) (M := M) r s β α P₀ Q D h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_ae_eq_of_coeFn_ae_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_ae_eq_of_coeFn_ae_eq target :: scope.openDecls } }

private def transportLp
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (memLp_transportFun (I := I) (M := M) r s β α P₀ Q D f).toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLp_coeFn
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    ((transportLp (I := I) (M := M) r s β α P₀ Q D f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      transportFun (I := I) (M := M) r s β α P₀ Q f := by
  unfold transportLp
  exact MemLp.coeFn_toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp_coeFn target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLp_add
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f₁ f₂ : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    transportLp (I := I) (M := M) r s β α P₀ Q D (f₁ + f₂) =
      transportLp (I := I) (M := M) r s β α P₀ Q D f₁ +
        transportLp (I := I) (M := M) r s β α P₀ Q D f₂ := by
  classical
  apply Lp.ext
  refine (transportLp_coeFn (I := I) (M := M) r s β α P₀ Q D (f₁ + f₂)).trans ?_
  have h_sum : transportFun (I := I) (M := M) r s β α P₀ Q (f₁ + f₂) =ᵐ[
      chartLebesgueMeasure (I := I) (M := M) α]
        fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
          (((f₁ : EuclN → ℝ) + (f₂ : EuclN → ℝ))
            (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    transportFun_aux_ae_eq (I := I) (M := M) r s β α P₀ Q D
      (Lp.coeFn_add f₁ f₂)
  refine h_sum.trans ?_
  have h_split : (fun y => transportCoeffPushed
      (I := I) (M := M) r s β α P₀ Q y *
        (((f₁ : EuclN → ℝ) + (f₂ : EuclN → ℝ))
          (chartTransitionEuclid (I := I) (M := M) α β y))) =
      fun y => transportFun (I := I) (M := M) r s β α P₀ Q f₁ y +
        transportFun (I := I) (M := M) r s β α P₀ Q f₂ y := by
    funext y
    unfold transportFun
    simp only [Pi.add_apply]
    ring
  rw [h_split]
  refine (Filter.EventuallyEq.add
    (transportLp_coeFn (I := I) (M := M) r s β α P₀ Q D f₁)
    (transportLp_coeFn (I := I) (M := M) r s β α P₀ Q D f₂)).symm.trans
    (Lp.coeFn_add _ _).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp_add target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLp_smul
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (c : ℝ) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    transportLp (I := I) (M := M) r s β α P₀ Q D (c • f) =
      c • transportLp (I := I) (M := M) r s β α P₀ Q D f := by
  classical
  apply Lp.ext
  refine (transportLp_coeFn (I := I) (M := M) r s β α P₀ Q D (c • f)).trans ?_
  have h_smul : transportFun (I := I) (M := M) r s β α P₀ Q (c • f) =ᵐ[
      chartLebesgueMeasure (I := I) (M := M) α]
        fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
          ((c • (f : EuclN → ℝ))
            (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    transportFun_aux_ae_eq (I := I) (M := M) r s β α P₀ Q D
      (Lp.coeFn_smul c f)
  refine h_smul.trans ?_
  have h_eq : (fun y => transportCoeffPushed
      (I := I) (M := M) r s β α P₀ Q y *
        ((c • (f : EuclN → ℝ))
          (chartTransitionEuclid (I := I) (M := M) α β y))) =
      fun y => c • transportFun (I := I) (M := M) r s β α P₀ Q f y := by
    funext y
    unfold transportFun
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_eq]
  refine ((transportLp_coeFn (I := I) (M := M) r s β α P₀ Q D f).const_smul
    c).symm.trans (Lp.coeFn_smul c _).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLp_smul target :: scope.openDecls } }

private def transportLpLin
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β) →ₗ[ℝ]
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) where
  toFun f := transportLp (I := I) (M := M) r s β α P₀ Q D f
  map_add' f₁ f₂ := transportLp_add (I := I) (M := M) r s β α P₀ Q D f₁ f₂
  map_smul' c f := transportLp_smul (I := I) (M := M) r s β α P₀ Q D c f

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLpLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLpLin target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma transportLpLin_apply
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    transportLpLin (I := I) (M := M) r s β α P₀ Q D f =
      transportLp (I := I) (M := M) r s β α P₀ Q D f := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLpLin_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLpLin_apply target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLpLin_norm_le
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) r s β α P₀ Q) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β),
        ‖transportLpLin (I := I) (M := M) r s β α P₀ Q D f‖ ≤ K * ‖f‖ := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_eLpNorm_transportFun_bound (I := I) (M := M) r s β α P₀ Q D
  refine ⟨K, hK_nn, fun f => ?_⟩
  have h_norm_eq : ‖transportLpLin (I := I) (M := M) r s β α P₀ Q D f‖ =
      (_root_.MeasureTheory.eLpNorm (transportFun (I := I) (M := M) r s β α P₀ Q f) 2
        (chartLebesgueMeasure (I := I) (M := M) α)).toReal := by
    rw [transportLpLin_apply]
    unfold transportLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_f_norm : ‖f‖ = (_root_.MeasureTheory.eLpNorm (f : EuclN → ℝ) 2
      (chartLebesgueMeasure (I := I) (M := M) β)).toReal := by
    rw [Lp.norm_def]
  have h_rhs_ne_top :
      ENNReal.ofReal K *
        eLpNorm (f : EuclN → ℝ) 2 (chartLebesgueMeasure (I := I) (M := M) β) ≠
          (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).2).ne
  have h_toReal_le :
      (_root_.MeasureTheory.eLpNorm (transportFun (I := I) (M := M) r s β α P₀ Q f) 2
        (chartLebesgueMeasure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal K *
          _root_.MeasureTheory.eLpNorm (f : EuclN → ℝ) 2
            (chartLebesgueMeasure (I := I) (M := M) β)).toReal :=
    ENNReal.toReal_mono h_rhs_ne_top (hK f)
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK_nn, h_f_norm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLpLin_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportLpLin_norm_le target :: scope.openDecls } }

private def transportDiffeoData
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    TransportDiffeoData (I := I) (M := M) r s β α P₀ Q :=
  (exists_transportDiffeoData (I := I) (M := M) r s β α P₀ Q).some

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportDiffeoData
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportDiffeoData target :: scope.openDecls } }

def chartTransitionTransportCLM
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β) →L[ℝ]
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (transportLpLin (I := I) (M := M) r s β α P₀ Q
    (transportDiffeoData (I := I) (M := M) r s β α P₀ Q)).mkContinuous
    (transportLpLin_norm_le (I := I) (M := M) r s β α P₀ Q
      (transportDiffeoData (I := I) (M := M) r s β α P₀ Q)).choose
    (transportLpLin_norm_le (I := I) (M := M) r s β α P₀ Q
      (transportDiffeoData (I := I) (M := M) r s β α P₀ Q)).choose_spec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartTransitionTransportCLM_coeFn
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      transportFun (I := I) (M := M) r s β α P₀ Q f := by
  have h_eq : chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f =
      transportLp (I := I) (M := M) r s β α P₀ Q
        (transportDiffeoData (I := I) (M := M) r s β α P₀ Q) f := by
    unfold chartTransitionTransportCLM
    rw [LinearMap.mkContinuous_apply, transportLpLin_apply]
  rw [h_eq]
  exact transportLp_coeFn (I := I) (M := M) r s β α P₀ Q
    (transportDiffeoData (I := I) (M := M) r s β α P₀ Q) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTransitionTransportCLM_coeFn_aeEq
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
    ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      (fun y => chartPushedRaw (I := I) (M := M) α
          (transportCoeffManifold (I := I) (M := M) r s β α P₀ Q) y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) := by
  refine (chartTransitionTransportCLM_coeFn
    (I := I) (M := M) r s β α P₀ Q f).trans ?_
  refine Filter.EventuallyEq.of_eq ?_
  funext y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_aeEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_aeEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_aeEq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_aeEq

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_tensorChartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (S : SmoothCcTensor g r s)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
        tensorChartComponent (I := I) (M := M) g r s S β Q.1 Q.2
          (chartTransitionEuclid (I := I) (M := M) α β y)) =
      chartPushedRaw (I := I) (M := M) α
        (fun x => transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) := by
  classical
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_rhs : chartPushedRaw (I := I) (M := M) α
        (fun x => transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y =
        transportCoeffManifold (I := I) (M := M) r s β α P₀ Q z *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 z := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy, ← hz_def]
    have h_coeff_push : transportCoeffPushed
        (I := I) (M := M) r s β α P₀ Q y =
          transportCoeffManifold (I := I) (M := M) r s β α P₀ Q z := by
      unfold transportCoeffPushed
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy, ← hz_def]
    rw [h_rhs, h_coeff_push]
    by_cases hcoeff : transportCoeffManifold (I := I) (M := M) r s β α P₀ Q z = 0
    · rw [hcoeff, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
    · have hz_support : z ∈ transportSupportSet (I := I) (M := M) α β :=
        tsupport_transportCoeffManifold_subset (I := I) (M := M) r s β α P₀ Q
          (subset_tsupport _ (Function.mem_support.mpr hcoeff))
      have hz_chartα : z ∈ (chartAt H α).source :=
        transportSupportSet_subset_sourceα (I := I) (M := M) α β hz_support
      have hz_chartβ : z ∈ (chartAt H β).source :=
        transportSupportSet_subset_sourceβ (I := I) (M := M) α β hz_support
      have hy_eq_image : (toEuclidean (E := E)) (extChartAt I α z) = y := by
        rw [hz_def, (extChartAt I α).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      have hT_eq : chartTransitionEuclid (I := I) (M := M) α β y =
          (toEuclidean (E := E)) (extChartAt I β z) := by
        rw [← hy_eq_image]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α β hz_chartα
      rw [hT_eq, tensorChartComponent_def]
      have hz_extβ_source : z ∈ (extChartAt I β).source := by
        rw [extChartAt_source (I := I)]; exact hz_chartβ
      have h_imageβ_mem :
          (toEuclidean (E := E)) (extChartAt I β z) ∈
            chartTargetEuclid (I := I) (M := M) β := by
        refine ⟨extChartAt I β z, ?_, rfl⟩
        exact (extChartAt I β).map_source hz_extβ_source
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ h_imageβ_mem]
      rw [(toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I β).left_inv hz_extβ_source]
  · have h_lhs : transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y = 0 := by
      unfold transportCoeffPushed
      exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy
    rw [h_lhs, _root_.MulZeroClass.zero_mul,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_tensorChartComponent_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transportFun_tensorChartComponent_eq target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTransitionTransportCLM_coeFn_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (S : SmoothCcTensor g r s)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (S : TensorL2 r s g) β Q) :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      chartPushedRaw (I := I) (M := M) α
        (fun x => transportCoeffManifold (I := I) (M := M) r s β α P₀ Q x *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) := by
  classical
  refine (chartTransitionTransportCLM_coeFn (I := I) (M := M) r s β α P₀ Q
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (S : TensorL2 r s g) β Q)).trans ?_
  have h_comp : transportFun (I := I) (M := M) r s β α P₀ Q
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) β Q) =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => transportCoeffPushed (I := I) (M := M) r s β α P₀ Q y *
          tensorChartComponent (I := I) (M := M) g r s S β Q.1 Q.2
            (chartTransitionEuclid (I := I) (M := M) α β y) :=
    transportFun_aux_ae_eq (I := I) (M := M) r s β α P₀ Q
      (transportDiffeoData (I := I) (M := M) r s β α P₀ Q)
      (tensorL2ChartComponent_smoothToTensorL2_coeFn
        (I := I) (M := M) g r s S β Q)
  refine h_comp.trans ?_
  rw [transportFun_tensorChartComponent_eq (I := I) (M := M) g r s β α S P₀ Q]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransitionTransportCLM_coeFn_smooth

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
