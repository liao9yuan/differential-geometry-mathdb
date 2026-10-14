import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Smoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [ChartedSpace H M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma locallyCompactSpace_M (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] : LocallyCompactSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.locallyCompactSpace_M
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.locallyCompactSpace_M target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [ChartedSpace H M] [CompactSpace M] [T2Space M] in
private lemma regularSpace_M (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [T2Space M] : RegularSpace M := by
  have : LocallyCompactSpace M := locallyCompactSpace_M (E := E) (H := H) (M := M) I
  have : WeaklyLocallyCompactSpace M := inferInstance
  have : R1Space M := T2Space.r1Space
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.regularSpace_M
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.regularSpace_M target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_subset_chartAt_source (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.pouTsupport_subset_chartAt_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.pouTsupport_subset_chartAt_source target :: scope.openDecls } }

omit [ChartedSpace H M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma exists_open_closure_subset_open_of_isCompact
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    {K U : Set M} (hK : IsCompact K) (hU_open : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U := by
  have : RegularSpace M := regularSpace_M (E := E) (H := H) (M := M) I
  have hU_nhdsSet : U ∈ 𝓝ˢ K := hU_open.mem_nhdsSet.mpr hKU
  exact hK.exists_isOpen_closure_subset hU_nhdsSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_open_closure_subset_open_of_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.exists_open_closure_subset_open_of_isCompact target :: scope.openDecls } }

omit [ChartedSpace H M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_open_closure_open_closure_subset_open_of_isCompact
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    {K U : Set M} (hK : IsCompact K) (hU_open : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ V₁ V₂ : Set M, IsOpen V₁ ∧ IsOpen V₂ ∧
      K ⊆ V₁ ∧ closure V₁ ⊆ V₂ ∧ closure V₂ ⊆ U := by
  obtain ⟨V₁, hV₁_open, hKV₁, hclos_V₁_U⟩ :=
    exists_open_closure_subset_open_of_isCompact (E := E) (H := H)
      (M := M) I hK hU_open hKU
  have hclos_V₁_compact : IsCompact (closure V₁) := isClosed_closure.isCompact
  obtain ⟨V₂, hV₂_open, hclos_V₁_V₂, hclos_V₂_U⟩ :=
    exists_open_closure_subset_open_of_isCompact (E := E) (H := H)
      (M := M) I hclos_V₁_compact hU_open hclos_V₁_U
  refine ⟨V₁, V₂, hV₁_open, hV₂_open, hKV₁, hclos_V₁_V₂, hclos_V₂_U⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_open_closure_open_closure_subset_open_of_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.exists_open_closure_open_closure_subset_open_of_isCompact target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_globalBump_data (α : M) :
    ∃ V₁ V₂ : Set M, ∃ ψ : M → ℝ,
      IsOpen V₁ ∧ IsOpen V₂ ∧
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ V₁ ∧
      closure V₁ ⊆ V₂ ∧
      closure V₂ ⊆ (chartAt H α).source ∧
      ContMDiff I 𝓘(ℝ) ∞ ψ ∧
      _root_.Set.range ψ ⊆ _root_.Set.Icc (0 : ℝ) 1 ∧
      (∀ x, x ∈ closure V₁ ↔ ψ x = 1) ∧
      (∀ x, x ∈ (V₂ᶜ : Set M) ↔ ψ x = 0) := by
  classical
  obtain ⟨V₁, V₂, hV₁_open, hV₂_open, hKV₁, hclos_V₁_V₂, hclos_V₂_source⟩ :=
    exists_open_closure_open_closure_subset_open_of_isCompact
      (E := E) (H := H) (M := M) I
      (pouTsupport_isCompact (I := I) (M := M) α)
      ((chartAt H α).open_source)
      (pouTsupport_subset_chartAt_source (I := I) (M := M) α)
  set s : Set M := V₂ᶜ
  set t : Set M := closure V₁
  have hs_closed : IsClosed s := isClosed_compl_iff.mpr hV₂_open
  have ht_closed : IsClosed t := isClosed_closure
  have hdisjoint : Disjoint s t := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    refine ⟨?_, fun hx => (Set.notMem_empty x hx).elim⟩
    rintro ⟨hx_s, hx_t⟩
    have hx_V₂ : x ∈ V₂ := hclos_V₁_V₂ hx_t
    have hx_notV₂ : x ∉ V₂ := hx_s
    exact (hx_notV₂ hx_V₂).elim
  have h_urysohn :
      ∃ f : M → ℝ,
        ContMDiff I 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
        _root_.Set.range f ⊆ _root_.Set.Icc (0 : ℝ) 1 ∧
        (∀ x, x ∈ s ↔ f x = 0) ∧
        (∀ x, x ∈ t ↔ f x = 1) :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) I
      hs_closed ht_closed hdisjoint
  obtain ⟨ψ, hψ_smooth, hψ_range, hψ_s, hψ_t⟩ := h_urysohn
  have hψ_smooth' : ContMDiff I 𝓘(ℝ) ∞ ψ := by
    have : ((⊤ : ℕ∞) : WithTop ℕ∞) = (∞ : WithTop ℕ∞) := rfl
    rw [this] at hψ_smooth
    exact hψ_smooth
  exact ⟨V₁, V₂, ψ, hV₁_open, hV₂_open, hKV₁, hclos_V₁_V₂, hclos_V₂_source,
    hψ_smooth', hψ_range, hψ_t, hψ_s⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_globalBump_data
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.exists_globalBump_data target :: scope.openDecls } }

private noncomputable def globalBumpV₁ (α : M) : Set M :=
  Classical.choose (exists_globalBump_data (I := I) (M := M) α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpV₁
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpV₁ target :: scope.openDecls } }

private noncomputable def globalBumpV₂ (α : M) : Set M :=
  Classical.choose (Classical.choose_spec
    (exists_globalBump_data (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpV₂
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpV₂ target :: scope.openDecls } }

private noncomputable def globalBumpψ (α : M) : M → ℝ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_globalBump_data (I := I) (M := M) α)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpψ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpψ target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpData_spec (α : M) :
    IsOpen (globalBumpV₁ (I := I) (M := M) α) ∧
      IsOpen (globalBumpV₂ (I := I) (M := M) α) ∧
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        globalBumpV₁ (I := I) (M := M) α ∧
      closure (globalBumpV₁ (I := I) (M := M) α) ⊆
        globalBumpV₂ (I := I) (M := M) α ∧
      closure (globalBumpV₂ (I := I) (M := M) α) ⊆ (chartAt H α).source ∧
      ContMDiff I 𝓘(ℝ) ∞ (globalBumpψ (I := I) (M := M) α) ∧
      range (globalBumpψ (I := I) (M := M) α) ⊆ _root_.Set.Icc (0 : ℝ) 1 ∧
      (∀ x, x ∈ closure (globalBumpV₁ (I := I) (M := M) α) ↔
        globalBumpψ (I := I) (M := M) α x = 1) ∧
      (∀ x, x ∈ (globalBumpV₂ (I := I) (M := M) α)ᶜ ↔
        globalBumpψ (I := I) (M := M) α x = 0) := by
  classical
  unfold globalBumpV₁ globalBumpV₂ globalBumpψ
  exact Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec (exists_globalBump_data (I := I) (M := M) α)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpData_spec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpData_spec target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpV₁_isOpen (α : M) :
    IsOpen (globalBumpV₁ (I := I) (M := M) α) :=
  (globalBumpData_spec (I := I) (M := M) α).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpV₁_isOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpV₁_isOpen target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pouTsupport_subset_globalBumpV₁ (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      globalBumpV₁ (I := I) (M := M) α :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.pouTsupport_subset_globalBumpV₁
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.pouTsupport_subset_globalBumpV₁ target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma closure_globalBumpV₁_subset_globalBumpV₂ (α : M) :
    closure (globalBumpV₁ (I := I) (M := M) α) ⊆
      globalBumpV₂ (I := I) (M := M) α :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.closure_globalBumpV₁_subset_globalBumpV₂
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.closure_globalBumpV₁_subset_globalBumpV₂ target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma closure_globalBumpV₂_subset_chartAt_source (α : M) :
    closure (globalBumpV₂ (I := I) (M := M) α) ⊆ (chartAt H α).source :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.closure_globalBumpV₂_subset_chartAt_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.closure_globalBumpV₂_subset_chartAt_source target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpψ_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ) ∞ (globalBumpψ (I := I) (M := M) α) :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.2.2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpψ_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpψ_contMDiff target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpψ_eq_one_on_closure_V₁ (α : M) {b : M}
    (hb : b ∈ closure (globalBumpV₁ (I := I) (M := M) α)) :
    globalBumpψ (I := I) (M := M) α b = 1 :=
  ((globalBumpData_spec (I := I) (M := M) α).2.2.2.2.2.2.2.1 b).mp hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpψ_eq_one_on_closure_V₁
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpψ_eq_one_on_closure_V₁ target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpψ_eq_zero_off_V₂ (α : M) {b : M}
    (hb : b ∈ (globalBumpV₂ (I := I) (M := M) α)ᶜ) :
    globalBumpψ (I := I) (M := M) α b = 0 :=
  ((globalBumpData_spec (I := I) (M := M) α).2.2.2.2.2.2.2.2 b).mp hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.globalBumpψ_eq_zero_off_V₂
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.globalBumpψ_eq_zero_off_V₂ target :: scope.openDecls } }

noncomputable def chartFrameNormGlobalSmooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := by
  classical
  set u : Set M := (chartAt H α).source with hu_def
  have hu_open : IsOpen u := (chartAt H α).open_source
  have hψ_tsupport_subset_clV₂ :
      tsupport (globalBumpψ (I := I) (M := M) α) ⊆
        closure (globalBumpV₂ (I := I) (M := M) α) := by
    have h_support : Function.support (globalBumpψ (I := I) (M := M) α) ⊆
        globalBumpV₂ (I := I) (M := M) α := by
      intro x hx
      by_contra hxV₂
      have hx_in : x ∈ (globalBumpV₂ (I := I) (M := M) α)ᶜ := hxV₂
      have hψx : globalBumpψ (I := I) (M := M) α x = 0 :=
        globalBumpψ_eq_zero_off_V₂ (I := I) (M := M) α hx_in
      exact hx hψx
    exact closure_mono h_support
  have hψ_tsupport_subset_u :
      tsupport (globalBumpψ (I := I) (M := M) α) ⊆ u :=
    hψ_tsupport_subset_clV₂.trans
      (closure_globalBumpV₂_subset_chartAt_source (I := I) (M := M) α)
  have hψ_smoothOn : ContMDiffOn I 𝓘(ℝ) ∞ (globalBumpψ (I := I) (M := M) α) u :=
    (globalBumpψ_contMDiff (I := I) (M := M) α).contMDiffOn
  have hs_smoothOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => chartFrameNorm (I := I) g α i b)) u := by
    rw [show u = (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet from rfl]
    exact chartFrameNorm_contMDiffOn (I := I) g α i
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smoothOn hu_open hψ_tsupport_subset_u hs_smoothOn
  refine ⟨fun b : M =>
    globalBumpψ (I := I) (M := M) α b • chartFrameNorm (I := I) g α i b, ?_⟩
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth

omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmooth_toFun_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      globalBumpψ (I := I) (M := M) α b • chartFrameNorm (I := I) g α i b := by
  classical
  unfold chartFrameNormGlobalSmooth
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_toFun_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_toFun_apply target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ U : Set M, IsOpen U ∧
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ U ∧
      U ⊆ (chartAt H α).source ∧
      ∀ b ∈ U, (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
        chartFrameNorm (I := I) g α i b := by
  classical
  refine ⟨globalBumpV₁ (I := I) (M := M) α, ?_, ?_, ?_, ?_⟩
  · exact globalBumpV₁_isOpen (I := I) (M := M) α
  · exact pouTsupport_subset_globalBumpV₁ (I := I) (M := M) α
  · intro b hb
    have h₁ : b ∈ closure (globalBumpV₁ (I := I) (M := M) α) := subset_closure hb
    have h₂ : b ∈ globalBumpV₂ (I := I) (M := M) α :=
      closure_globalBumpV₁_subset_globalBumpV₂ (I := I) (M := M) α h₁
    have h₃ : b ∈ closure (globalBumpV₂ (I := I) (M := M) α) := subset_closure h₂
    exact closure_globalBumpV₂_subset_chartAt_source (I := I) (M := M) α h₃
  · intro b hb
    have hψ : globalBumpψ (I := I) (M := M) α b = 1 :=
      globalBumpψ_eq_one_on_closure_V₁ (I := I) (M := M) α (subset_closure hb)
    rw [chartFrameNormGlobalSmooth_toFun_apply, hψ, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
      if i = j then 1 else 0 := by
  classical
  obtain ⟨U_i, _hU_i_open, htsupp_U_i, hU_i_source, hU_eq_i⟩ :=
    chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood
      (I := I) (M := M) g α i
  obtain ⟨U_j, _hU_j_open, htsupp_U_j, _hU_j_source, hU_eq_j⟩ :=
    chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNeighborhood
      (I := I) (M := M) g α j
  have hb_pou : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb.1
  have hb_U_i : b ∈ U_i := htsupp_U_i hb_pou
  have hb_U_j : b ∈ U_j := htsupp_U_j hb_pou
  have hb_source : b ∈ (chartAt H α).source := hU_i_source hb_U_i
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb_source
  have h_eq_i : (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      chartFrameNorm (I := I) g α i b := hU_eq_i b hb_U_i
  have h_eq_j : (chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b =
      chartFrameNorm (I := I) g α j b := hU_eq_j b hb_U_j
  rw [h_eq_i, h_eq_j]
  exact chartFrameNorm_orthonormal (I := I) g α hb_base i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet

end Elliptic
end Analysis
end DifferentialGeometry
