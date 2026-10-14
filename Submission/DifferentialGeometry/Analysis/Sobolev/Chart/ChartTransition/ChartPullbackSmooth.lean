import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
private theorem isCompact_chartInverse_prod_image
    {P : Type*} [TopologicalSpace P] (α : M) {K : Set (P × EuclN)}
    (hK : IsCompact K) (hKt : K ⊆ _root_.Set.univ ×ˢ chartTargetEuclid (I := I) α) :
    IsCompact ((fun p : P × EuclN =>
      (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))) '' K) := by
  apply hK.image_of_continuousOn
  apply continuousOn_fst.prodMk
  apply (continuousOn_extChartAt_symm (I := I) α).comp
    ((toEuclidean (E := E)).symm.continuous.comp continuous_snd).continuousOn
  intro p hp
  have ht := (hKt hp).2
  rwa [chartTargetEuclid_eq_preimage_symm] at ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.isCompact_chartInverse_prod_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.isCompact_chartInverse_prod_image target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
theorem tsupport_chartPullback_prod_subset
    [T2Space M] {P : Type*} [TopologicalSpace P] [T2Space P]
    (α : M) {φ : P × EuclN → ℝ} (hφc : HasCompactSupport φ)
    (hφt : tsupport φ ⊆ _root_.Set.univ ×ˢ chartTargetEuclid (I := I) α) :
    tsupport (fun p : P × M => chartPullback I α (fun y => φ (p.1, y)) p.2) ⊆
      (fun p : P × EuclN => (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))) ''
        tsupport φ := by
  apply closure_minimal ?_ (isCompact_chartInverse_prod_image α hφc hφt).isClosed
  intro p hp
  by_cases hx : p.2 ∈ (chartAt H α).source
  · refine ⟨(p.1, toEuclidean (extChartAt I α p.2)), ?_, ?_⟩
    · apply subset_tsupport φ
      simpa only [Function.mem_support, chartPullback_apply_of_mem (I := I) α _ hx] using hp
    · simp only [ContinuousLinearEquiv.symm_apply_apply]
      congr 1
      exact (extChartAt I α).left_inv (by simpa only [extChartAt_source] using hx)
  · exact (hp (chartPullback_apply_of_notMem (I := I) α _ hx)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset

omit [IsManifold I ∞ M] in
theorem hasCompactSupport_chartPullback_prod
    [T2Space M] {P : Type*} [TopologicalSpace P] [T2Space P]
    (α : M) {φ : P × EuclN → ℝ} (hφc : HasCompactSupport φ)
    (hφt : tsupport φ ⊆ _root_.Set.univ ×ˢ chartTargetEuclid (I := I) α) :
    HasCompactSupport (fun p : P × M => chartPullback I α (fun y => φ (p.1, y)) p.2) :=
  (isCompact_chartInverse_prod_image α hφc hφt).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_chartPullback_prod_subset α hφc hφt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartPullback_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartPullback_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartPullback_prod ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartPullback_prod

omit [IsManifold I ∞ M] in
theorem tsupport_chartPullback_prod_subset_interior
    [T2Space M] [IsManifold I 1 M] {P : Type*} [TopologicalSpace P] [T2Space P]
    (α : M) {φ : P × EuclN → ℝ} (hφc : HasCompactSupport φ) {J : Set P}
    (hφt : tsupport φ ⊆ J ×ˢ (toEuclidean (E := E) '' interior (extChartAt I α).target)) :
    tsupport (fun p : P × M => chartPullback I α (fun y => φ (p.1, y)) p.2) ⊆
      J ×ˢ I.interior M := by
  have hs : tsupport φ ⊆ _root_.Set.univ ×ˢ chartTargetEuclid (I := I) α :=
    hφt.trans (_root_.Set.prod_mono (_root_.Set.subset_univ _) (_root_.Set.image_mono interior_subset))
  rintro p hp
  obtain ⟨z, hz, rfl⟩ := tsupport_chartPullback_prod_subset α hφc hs hp
  refine ⟨(hφt hz).1, ?_⟩
  obtain ⟨y, hy, heq⟩ := (hφt hz).2
  change (extChartAt I α).symm ((toEuclidean (E := E)).symm z.2) ∈ I.interior M
  rw [← heq, ContinuousLinearEquiv.symm_apply_apply]
  have hsrc := (extChartAt I α).map_target (interior_subset hy)
  rw [extChartAt_source] at hsrc
  apply (I.isInteriorPoint_iff_of_mem_atlas (M := M) (n := 1)
    (by simp) (chart_mem_atlas H α) hsrc).2
  change extChartAt I α ((extChartAt I α).symm y) ∈ interior (extChartAt I α).target
  rwa [(extChartAt I α).right_inv (interior_subset hy)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset_interior ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_prod_subset_interior

omit [IsManifold I ∞ M] in
lemma tsupport_chartPullback_subset
    [T2Space M]
    (α : M)
    {ψ : EuclN → ℝ}
    (hψ_compact : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPullback I α ψ) ⊆
      (extChartAt I α).symm '' ((toEuclidean (E := E)).symm '' tsupport ψ) := by
  let φ : Unit × EuclN → ℝ := fun p => ψ p.2
  have hc : HasCompactSupport φ :=
    hψ_compact.comp_homeomorph (Homeomorph.uniqueProd Unit EuclN)
  have hs : tsupport φ ⊆ _root_.Set.univ ×ˢ chartTargetEuclid (I := I) α := by
    change tsupport (ψ ∘ Homeomorph.uniqueProd Unit EuclN) ⊆ _
    rw [tsupport_comp_eq_preimage]
    exact fun _ hp => ⟨mem_univ _, hψ_support hp⟩
  intro x hx
  have hp : ((), x) ∈ tsupport (fun p : Unit × M => chartPullback I α (fun y => φ (p.1, y)) p.2) := by
    change ((), x) ∈ tsupport (chartPullback I α ψ ∘ Homeomorph.uniqueProd Unit M)
    rw [tsupport_comp_eq_preimage]
    exact hx
  obtain ⟨z, hz, heq⟩ := tsupport_chartPullback_prod_subset α hc hs hp
  have hzs : z.2 ∈ tsupport ψ := by
    change z ∈ tsupport (ψ ∘ Homeomorph.uniqueProd Unit EuclN) at hz
    rwa [tsupport_comp_eq_preimage] at hz
  exact ⟨_, ⟨z.2, hzs, rfl⟩, congrArg Prod.snd heq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset

omit [IsManifold I ∞ M] in
private lemma tsupport_chartPullback_image_subset_chartAt_source
    (α : M)
    {ψ : EuclN → ℝ}
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm '' ((toEuclidean (E := E)).symm '' tsupport ψ) ⊆
      (chartAt H α).source := by
  intro x hx
  rcases hx with ⟨z, hz, hxz⟩
  rcases hz with ⟨y, hy_in, hyz⟩
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_support hy_in
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hyz]; exact hy_target
  have hx_in_source : x ∈ (extChartAt I α).source := by
    rw [← hxz]
    exact (extChartAt I α).map_target hz_target
  rw [extChartAt_source (I := I)] at hx_in_source
  exact hx_in_source

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_image_subset_chartAt_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_image_subset_chartAt_source target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
theorem tsupport_chartPullback_subset_interior
    [T2Space M] [IsManifold I 1 M]
    (α : M) {ψ : EuclN → ℝ}
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      toEuclidean (E := E) '' interior (extChartAt I α).target) :
    tsupport (chartPullback I α ψ) ⊆ I.interior M := by
  have hs : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hψ_supp.trans (Set.image_mono interior_subset)
  intro x hx
  obtain ⟨z, ⟨y, hy, rfl⟩, rfl⟩ := tsupport_chartPullback_subset α hψ_cpt hs hx
  obtain ⟨z, hz, rfl⟩ := hψ_supp hy
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hsrc := (extChartAt I α).map_target (interior_subset hz)
  rw [extChartAt_source] at hsrc
  apply (I.isInteriorPoint_iff_of_mem_atlas (M := M) (n := 1)
    (by simp) (chart_mem_atlas H α) hsrc).2
  change extChartAt I α ((extChartAt I α).symm z) ∈ interior (extChartAt I α).target
  rwa [(extChartAt I α).right_inv (interior_subset hz)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset_interior ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset_interior

theorem chartPullback_contMDiff_prod
    [T2Space M] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (α : M) {φ : P × EuclN → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set EuclN} (hK : IsCompact K)
    (hKt : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hφK : tsupport φ ⊆ _root_.Set.univ ×ˢ K) :
    ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => chartPullback I α (fun y => φ (p.1, y)) p.2) := by
  classical
  let e := toEuclidean (E := E)
  let K_M := (extChartAt I α).symm '' (e.symm '' K)
  have hEt : e.symm '' K ⊆ (extChartAt I α).target := by
    rintro z ⟨y, hy, rfl⟩
    have hy' := hKt hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy'
    exact hy'
  have hKM : IsCompact K_M :=
    (hK.image e.symm.continuous).image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) α).mono hEt)
  have hKMs : K_M ⊆ (chartAt H α).source := by
    rintro x ⟨y, hy, rfl⟩
    have hsrc := (extChartAt I α).map_target (hEt hy)
    rwa [extChartAt_source (I := I)] at hsrc
  have hs (p : P) : tsupport (fun y => φ (p, y)) ⊆ K := by
    have h := tsupport_comp_subset_preimage φ (f := fun y : EuclN => (p, y))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun y hy => (hφK hy).2
  have hsp (p : P) : tsupport (chartPullback I α (fun y => φ (p, y))) ⊆ K_M :=
    (tsupport_chartPullback_subset α (hK.of_isClosed_subset (isClosed_tsupport _) (hs p))
      ((hs p).trans hKt)).trans
        (Set.image_mono (Set.image_mono (hs p)))
  have hts : tsupport
      (fun p : P × M => chartPullback I α (fun y => φ (p.1, y)) p.2) ⊆ _root_.Set.univ ×ˢ K_M := by
    apply closure_minimal ?_ (isClosed_univ.prod hKM.isClosed)
    intro p hp
    exact ⟨mem_univ _, hsp p.1 (subset_tsupport _ hp)⟩
  apply contMDiff_of_tsupport
  intro p hp
  have hx : p.2 ∈ (chartAt H α).source := hKMs (hts hp).2
  have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) p.2 :=
    (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).contMDiffAt
      ((chartAt H α).open_source.mem_nhds hx)
  have hcoord : ContMDiffAt I 𝓘(ℝ, EuclN) ∞
      (fun x => e (extChartAt I α x)) p.2 :=
    e.toContinuousLinearMap.contMDiff.contMDiffAt.comp p.2 hext
  have hmap : ContMDiffAt (𝓘(ℝ, P).prod I) 𝓘(ℝ, P × EuclN) ∞
      (fun r : P × M => (r.1, e (extChartAt I α r.2))) p := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffAt_fst.prodMk (hcoord.comp p contMDiffAt_snd)
  apply (hφ.comp_contMDiffAt hmap).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.eventually ((chartAt H α).open_source.mem_nhds hx)] with r hr
  exact chartPullback_apply_of_mem (I := I) (M := M) α (fun y => φ (r.1, y)) hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod

theorem chartPullback_contMDiff_prod_of_hasCompactSupport
    [T2Space M] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (α : M) {φ : P × EuclN → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hφt : tsupport φ ⊆ _root_.Set.univ ×ˢ chartTargetEuclid (I := I) (M := M) α) :
    ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => chartPullback I α (fun y => φ (p.1, y)) p.2) := by
  apply chartPullback_contMDiff_prod α hφ (hφc.image continuous_snd)
  · rintro y ⟨p, hp, rfl⟩
    exact (hφt hp).2
  · intro p hp
    exact ⟨mem_univ _, ⟨p, hp, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff_prod_of_hasCompactSupport

theorem chartPullback_contMDiff
    [T2Space M]
    (α : M)
    {ψ : EuclN → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartPullback I α ψ) := by
  classical
  have h_tsupp : tsupport (chartPullback I α ψ) ⊆ (chartAt H α).source := by
    refine subset_trans ?_
      (tsupport_chartPullback_image_subset_chartAt_source (I := I) (M := M) α hψ_support)
    exact tsupport_chartPullback_subset (I := I) (M := M) α hψ_compact hψ_support
  set T : Set M := tsupport (chartPullback I α ψ) with hT_def
  have hT_closed : IsClosed T := isClosed_tsupport _
  refine contMDiff_of_locally_contMDiffOn ?_
  intro x
  by_cases hx_source : x ∈ (chartAt H α).source
  · refine ⟨(chartAt H α).source, (chartAt H α).open_source, hx_source, ?_⟩
    have h_eq_on : Set.EqOn (chartPullback I α ψ)
        (fun y => ψ ((toEuclidean (E := E)) (extChartAt I α y)))
        (chartAt H α).source := by
      intro y hy
      exact chartPullback_apply_of_mem (I := I) (M := M) α ψ hy
    have h_comp_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => ψ ((toEuclidean (E := E)) (extChartAt I α y)))
        (chartAt H α).source := by
      have h_ext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
          (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      have h_toE : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclN) ∞
          ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
        ContinuousLinearMap.contMDiff
          (toEuclidean : E ≃L[ℝ] EuclN).toContinuousLinearMap
      have h_toE_ext : ContMDiffOn I 𝓘(ℝ, EuclN) ∞
          (fun y => (toEuclidean (E := E)) (extChartAt I α y))
          (chartAt H α).source := by
        intro y hy
        exact h_toE.contMDiffAt.comp_contMDiffWithinAt y (h_ext y hy)
      intro y hy
      have hcomp : ContDiff ℝ (⊤ : ℕ∞) ψ := hψ_smooth
      exact hcomp.comp_contMDiffWithinAt (h_toE_ext y hy)
    refine h_comp_smooth.congr ?_
    intro y hy
    exact h_eq_on hy
  · have hxT : x ∉ T := by
      intro hxT
      apply hx_source
      exact h_tsupp hxT
    refine ⟨Tᶜ, hT_closed.isOpen_compl, hxT, ?_⟩
    have h_zero_on : Set.EqOn (chartPullback I α ψ) (fun _ : M => (0 : ℝ)) Tᶜ := by
      intro y hy
      simp only [Set.mem_compl_iff] at hy
      have hy_not_support : y ∉ Function.support (chartPullback I α ψ) := by
        intro hy_support
        exact hy (subset_tsupport _ hy_support)
      simpa [Function.mem_support, _root_.Classical.not_not] using hy_not_support
    have h_const : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) Tᶜ :=
      contMDiff_const.contMDiffOn
    refine h_const.congr ?_
    intro y hy
    exact h_zero_on hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff

def chartTransitionEuclid (γ α : M) :
    EuclN → EuclN := fun y =>
  (toEuclidean (E := E)) (extChartAt I α
    ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_apply (γ α : M) (y : EuclN) :
    chartTransitionEuclid (I := I) (M := M) γ α y =
      (toEuclidean (E := E)) (extChartAt I α
        ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_apply

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_eq_chartα_image
    (γ α : M) {x : M}
    (hx_γ : x ∈ (chartAt H γ).source) :
    chartTransitionEuclid (I := I) (M := M) γ α
        ((toEuclidean (E := E)) (extChartAt I γ x)) =
      (toEuclidean (E := E)) (extChartAt I α x) := by
  unfold chartTransitionEuclid
  rw [(toEuclidean (E := E)).symm_apply_apply]
  have hx_source : x ∈ (extChartAt I γ).source := by
    rw [extChartAt_source (I := I)]
    exact hx_γ
  rw [(extChartAt I γ).left_inv hx_source]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_eq_chartα_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_eq_chartα_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_eq_chartα_image ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_eq_chartα_image

def chartCenterEuclid (α : M) : EuclN :=
  (toEuclidean (E := E)) (extChartAt I α α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartCenterEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartCenterEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartCenterEuclid ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartCenterEuclid

def chartTransitionExtended
    (γ α : M)
    (η : EuclN → ℝ)
    (c : EuclN) : EuclN → EuclN := fun y =>
  η y • chartTransitionEuclid (I := I) (M := M) γ α y + (1 - η y) • c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended

omit [IsManifold I ∞ M] in
lemma chartTransitionExtended_sub_const
    (γ α : M)
    (η : EuclN → ℝ)
    (c : EuclN) (y : EuclN) :
    chartTransitionExtended (I := I) (M := M) γ α η c y - c =
      η y • (chartTransitionEuclid (I := I) (M := M) γ α y - c) := by
  unfold chartTransitionExtended
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_sub_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_sub_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_sub_const ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_sub_const

omit [IsManifold I ∞ M] in
lemma chartTransitionExtended_eq_const_off_tsupport
    (γ α : M)
    {η : EuclN → ℝ}
    (c : EuclN) {y : EuclN} (hy : y ∉ tsupport η) :
    chartTransitionExtended (I := I) (M := M) γ α η c y = c := by
  have hη_zero : η y = 0 := image_eq_zero_of_notMem_tsupport hy
  unfold chartTransitionExtended
  rw [hη_zero]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_const_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_const_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_const_off_tsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_const_off_tsupport

omit [IsManifold I ∞ M] in
lemma chartTransitionExtended_eq_chartTransition_on_eta_eq_one
    (γ α : M)
    {η : EuclN → ℝ}
    (c : EuclN) {y : EuclN} (hy_eta : η y = 1) :
    chartTransitionExtended (I := I) (M := M) γ α η c y =
      chartTransitionEuclid (I := I) (M := M) γ α y := by
  unfold chartTransitionExtended
  rw [hy_eta]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_chartTransition_on_eta_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_chartTransition_on_eta_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_chartTransition_on_eta_eq_one ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_eq_chartTransition_on_eta_eq_one

def chartOverlapEuclid (γ α : M) : Set EuclN :=
  (toEuclidean (E := E)) '' (extChartAt I γ '' ((chartAt H γ).source ∩ (chartAt H α).source))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid

omit [IsManifold I ∞ M] in
lemma chartOverlapEuclid_subset_chartTarget
    (γ α : M) :
    chartOverlapEuclid (I := I) (M := M) γ α ⊆
      chartTargetEuclid (I := I) (M := M) γ := by
  intro y hy
  rcases hy with ⟨z, ⟨x, hx, hxz⟩, hzy⟩
  refine ⟨z, ?_, hzy⟩
  rw [← hxz]
  have hx_source : x ∈ (extChartAt I γ).source := by
    rw [extChartAt_source (I := I)]
    exact hx.1
  exact (extChartAt I γ).map_source hx_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_subset_chartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_subset_chartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_subset_chartTarget ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_subset_chartTarget

omit [IsManifold I ∞ M] in
lemma chartOverlapEuclid_isOpen
    [I.Boundaryless]
    (γ α : M) :
    IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) := by
  unfold chartOverlapEuclid
  have h_open_M : IsOpen ((chartAt H γ).source ∩ (chartAt H α).source) :=
    (chartAt H γ).open_source.inter (chartAt H α).open_source
  have h_subset_source :
      (chartAt H γ).source ∩ (chartAt H α).source ⊆ (chartAt H γ).source := by
    intro x hx; exact hx.1
  have h_image_chart_open : IsOpen ((chartAt H γ) ''
      ((chartAt H γ).source ∩ (chartAt H α).source)) :=
    (chartAt H γ).isOpen_image_of_subset_source h_open_M h_subset_source
  have h_extChart_eq :
      (extChartAt I γ) '' ((chartAt H γ).source ∩ (chartAt H α).source) =
        I '' ((chartAt H γ) '' ((chartAt H γ).source ∩ (chartAt H α).source)) := by
    rw [Set.image_image]
    rfl
  rw [h_extChart_eq]
  have h_I_image : IsOpen (I ''
    ((chartAt H γ) '' ((chartAt H γ).source ∩ (chartAt H α).source))) := by
    have : (I.toHomeomorph : H → E) =
        (I : H → E) := rfl
    rw [show (I : H → E) = ((I.toHomeomorph : H → E)) from rfl]
    exact I.toHomeomorph.isOpenMap _ h_image_chart_open
  exact (toEuclidean (E := E)).toHomeomorph.isOpenMap _ h_I_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_isOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartOverlapEuclid_isOpen

omit [IsManifold I ∞ M] in
lemma kEuclid_subset_overlap
    (γ α : M) {K : Set M}
    (hK_γ : K ⊆ (chartAt H γ).source)
    (hK_α : K ⊆ (chartAt H α).source) :
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K ⊆
      chartOverlapEuclid (I := I) (M := M) γ α := by
  intro y hy
  rcases hy with ⟨x, hx_in, hxy⟩
  refine ⟨extChartAt I γ x, ?_, hxy⟩
  exact ⟨x, ⟨hK_γ hx_in, hK_α hx_in⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_subset_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_subset_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_subset_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_subset_overlap

omit [IsManifold I ∞ M] in
lemma kEuclid_compact
    (γ : M) {K : Set M} (hK_compact : IsCompact K)
    (hK_γ : K ⊆ (chartAt H γ).source) :
    IsCompact ((fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K) := by
  refine hK_compact.image_of_continuousOn ?_
  have hcont_extChart : ContinuousOn (extChartAt I γ) (chartAt H γ).source := by
    have hco := continuousOn_extChartAt (I := I) γ
    rw [extChartAt_source (I := I)] at hco
    exact hco
  have hcont_toE : Continuous ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
    (toEuclidean : E ≃L[ℝ] EuclN).continuous
  have hcomp : ContinuousOn (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x))
      (chartAt H γ).source := by
    intro x hx
    exact hcont_toE.continuousAt.continuousWithinAt.comp
      (hcont_extChart x hx) (Set.mapsTo_univ _ _)
  exact hcomp.mono hK_γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.kEuclid_compact

lemma chartTransitionEuclid_contDiffOn_overlap
    (γ α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  classical
  set S_M : Set M := (chartAt H γ).source ∩ (chartAt H α).source with hS_M_def
  set S_E : Set E := (extChartAt I γ) '' S_M with hS_E_def
  have h_ext_coord :
      ContDiffOn ℝ (⊤ : ℕ∞) (extChartAt I α ∘ (extChartAt I γ).symm)
        ((extChartAt I γ).symm ≫ extChartAt I α).source :=
    contDiffOn_ext_coord_change (I := I) (n := ∞) α γ
  have hS_E_subset_coord_source :
      S_E ⊆ ((extChartAt I γ).symm ≫ extChartAt I α).source := by
    intro z hz
    rcases hz with ⟨x, hx_in, hxz⟩
    rcases hx_in with ⟨hx_γ, hx_α⟩
    refine ⟨?_, ?_⟩
    · have hx_extγ_source : x ∈ (extChartAt I γ).source := by
        rw [extChartAt_source (I := I)]; exact hx_γ
      rw [← hxz]
      exact (extChartAt I γ).map_source hx_extγ_source
    · have hx_extγ_source : x ∈ (extChartAt I γ).source := by
        rw [extChartAt_source (I := I)]; exact hx_γ
      have h_lr : (extChartAt I γ).symm (extChartAt I γ x) = x :=
        (extChartAt I γ).left_inv hx_extγ_source
      change (extChartAt I γ).symm z ∈ (extChartAt I α).source
      rw [← hxz, h_lr]
      rw [extChartAt_source (I := I)]; exact hx_α
  have h_ext_coord_S : ContDiffOn ℝ (⊤ : ℕ∞)
      (extChartAt I α ∘ (extChartAt I γ).symm) S_E :=
    h_ext_coord.mono hS_E_subset_coord_source
  have htoE_symm_contDiff : ContDiff ℝ (⊤ : ℕ∞)
      ((toEuclidean (E := E)).symm : EuclN → E) :=
    (toEuclidean (E := E)).symm.contDiff
  have htoE_contDiff : ContDiff ℝ (⊤ : ℕ∞)
      ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
    (toEuclidean : E ≃L[ℝ] EuclN).contDiff
  have hsymm_image_eq :
      ((toEuclidean (E := E)).symm) ⁻¹' S_E =
        chartOverlapEuclid (I := I) (M := M) γ α := by
    ext y
    simp only [Set.mem_preimage]
    refine ⟨fun h => ⟨(toEuclidean (E := E)).symm y, h, by
      exact (toEuclidean (E := E)).apply_symm_apply y⟩, ?_⟩
    rintro ⟨z, hz_in, hzy⟩
    have h_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy, (toEuclidean (E := E)).symm_apply_apply]
    rw [h_symm]; exact hz_in
  have hmapsTo : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartOverlapEuclid (I := I) (M := M) γ α) S_E := by
    intro y hy
    rw [← hsymm_image_eq] at hy
    exact hy
  have h_step2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (extChartAt I α ∘ (extChartAt I γ).symm)
          ((toEuclidean (E := E)).symm y))
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    h_ext_coord_S.comp htoE_symm_contDiff.contDiffOn hmapsTo
  have h_step3 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (toEuclidean (E := E))
        ((extChartAt I α ∘ (extChartAt I γ).symm)
          ((toEuclidean (E := E)).symm y)))
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    htoE_contDiff.comp_contDiffOn h_step2
  exact h_step3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_contDiffOn_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_contDiffOn_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_contDiffOn_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_contDiffOn_overlap

def chartTransitionCutoffShifted
    (γ α : M)
    (η : EuclN → ℝ)
    (c : EuclN) : EuclN → EuclN := fun y =>
  η y • (chartTransitionEuclid (I := I) (M := M) γ α y - c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionCutoffShifted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionCutoffShifted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionCutoffShifted ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionCutoffShifted

omit [IsManifold I ∞ M] in
lemma chartTransitionExtensionSubC_zero_off_tsupport
    (γ α : M)
    {η : EuclN → ℝ}
    (c : EuclN) {y : EuclN} (hy : y ∉ tsupport η) :
    chartTransitionCutoffShifted (I := I) (M := M) γ α η c y = 0 := by
  have hη_zero : η y = 0 := image_eq_zero_of_notMem_tsupport hy
  unfold chartTransitionCutoffShifted
  rw [hη_zero]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_zero_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_zero_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_zero_off_tsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_zero_off_tsupport

omit [IsManifold I ∞ M] in
lemma chartTransitionExtensionSubC_contDiffOn_off_tsupport
    (γ α : M)
    {η : EuclN → ℝ}
    (c : EuclN) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartTransitionCutoffShifted (I := I) (M := M) γ α η c)
      ((tsupport η)ᶜ) := by
  have h_zero : Set.EqOn (chartTransitionCutoffShifted (I := I) (M := M) γ α η c)
      (fun _ : EuclN => (0 : EuclN)) ((tsupport η)ᶜ) := by
    intro y hy
    simp only [Set.mem_compl_iff] at hy
    exact chartTransitionExtensionSubC_zero_off_tsupport (I := I) (M := M) γ α c hy
  have h_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : EuclN => (0 : EuclN)) ((tsupport η)ᶜ) :=
    contDiffOn_const
  exact h_const.congr (fun y hy => h_zero hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_off_tsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_off_tsupport

lemma chartTransitionExtensionSubC_contDiffOn_overlap
    (γ α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (c : EuclN) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartTransitionCutoffShifted (I := I) (M := M) γ α η c)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  unfold chartTransitionCutoffShifted
  have h_T : ContDiffOn ℝ (⊤ : ℕ∞)
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
  have h_T_sub_c : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => chartTransitionEuclid (I := I) (M := M) γ α y - c)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    h_T.sub contDiffOn_const
  exact hη_smooth.contDiffOn.smul h_T_sub_c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiffOn_overlap

lemma chartTransitionExtensionSubC_contDiff
    [I.Boundaryless]
    (γ α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : tsupport η ⊆ chartOverlapEuclid (I := I) (M := M) γ α)
    (c : EuclN) :
    ContDiff ℝ (⊤ : ℕ∞) (chartTransitionCutoffShifted (I := I) (M := M) γ α η c) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_support : y ∈ tsupport η
  · have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := hη_support hy_support
    have h_overlap_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) γ α
    have h_smooth_on : ContDiffOn ℝ (⊤ : ℕ∞)
        (chartTransitionCutoffShifted (I := I) (M := M) γ α η c)
        (chartOverlapEuclid (I := I) (M := M) γ α) :=
      chartTransitionExtensionSubC_contDiffOn_overlap (I := I) (M := M) γ α
        hη_smooth c
    exact h_smooth_on.contDiffAt (h_overlap_open.mem_nhds hy_overlap)
  · have h_open : IsOpen ((tsupport η)ᶜ) := (isClosed_tsupport _).isOpen_compl
    have hy_in : y ∈ ((tsupport η)ᶜ) := hy_support
    have h_smooth_on : ContDiffOn ℝ (⊤ : ℕ∞)
        (chartTransitionCutoffShifted (I := I) (M := M) γ α η c)
        ((tsupport η)ᶜ) :=
      chartTransitionExtensionSubC_contDiffOn_off_tsupport (I := I) (M := M) γ α c
    exact h_smooth_on.contDiffAt (h_open.mem_nhds hy_in)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtensionSubC_contDiff

lemma chartTransitionExtended_contDiff
    [I.Boundaryless]
    (γ α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : tsupport η ⊆ chartOverlapEuclid (I := I) (M := M) γ α)
    (c : EuclN) :
    ContDiff ℝ (⊤ : ℕ∞) (chartTransitionExtended (I := I) (M := M) γ α η c) := by
  have h_eq : chartTransitionExtended (I := I) (M := M) γ α η c =
      fun y => c + chartTransitionCutoffShifted (I := I) (M := M) γ α η c y := by
    funext y
    have h_sub := chartTransitionExtended_sub_const (I := I) (M := M) γ α η c y
    rw [show (chartTransitionExtended (I := I) (M := M) γ α η c) y =
        c + (chartTransitionExtended (I := I) (M := M) γ α η c y - c) by abel]
    rw [h_sub]
    rfl
  rw [h_eq]
  exact contDiff_const.add (chartTransitionExtensionSubC_contDiff (I := I) (M := M)
    γ α hη_smooth hη_support c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_contDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_contDiff

omit [IsManifold I ∞ M] in
lemma chartTransitionExtended_hasCompactSupport_sub
    (γ α : M)
    {η : EuclN → ℝ}
    (hη_compact : HasCompactSupport η)
    (c : EuclN) :
    HasCompactSupport
      (fun y => chartTransitionExtended (I := I) (M := M) γ α η c y - c) := by
  have h_eq : (fun y => chartTransitionExtended (I := I) (M := M) γ α η c y - c) =
      chartTransitionCutoffShifted (I := I) (M := M) γ α η c := by
    funext y
    exact chartTransitionExtended_sub_const (I := I) (M := M) γ α η c y
  rw [h_eq]
  have h_support_sub : Function.support
      (chartTransitionCutoffShifted (I := I) (M := M) γ α η c) ⊆ tsupport η := by
    intro y hy
    by_contra hy_not
    apply hy
    exact chartTransitionExtensionSubC_zero_off_tsupport (I := I) (M := M) γ α c hy_not
  have h_tsupport_compact : IsCompact (tsupport η) := hη_compact
  refine HasCompactSupport.intro' (K := tsupport η)
    h_tsupport_compact (isClosed_tsupport _) ?_
  intro y hy
  have hy_not : y ∉ Function.support
      (chartTransitionCutoffShifted (I := I) (M := M) γ α η c) := by
    intro hy_support
    exact hy (h_support_sub hy_support)
  simpa [Function.mem_support, _root_.Classical.not_not] using hy_not

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_hasCompactSupport_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_hasCompactSupport_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_hasCompactSupport_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_hasCompactSupport_sub

lemma chartTransitionExtended_iter_deriv_bound
    [I.Boundaryless]
    (γ α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η)
    (hη_support : tsupport η ⊆ chartOverlapEuclid (I := I) (M := M) γ α)
    (c : EuclN) (kmax : ℕ) :
    ∃ M_bd : ℝ, 0 < M_bd ∧
      ∀ i, i ≤ kmax → ∀ x : EuclN,
        ‖iteratedFDeriv ℝ i (chartTransitionExtended (I := I) (M := M) γ α η c) x‖ ≤ M_bd := by
  have hT_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (chartTransitionExtended (I := I) (M := M) γ α η c) :=
    chartTransitionExtended_contDiff (I := I) (M := M) γ α hη_smooth hη_support c
  have hT_diff_compact : HasCompactSupport
      (fun y => chartTransitionExtended (I := I) (M := M) γ α η c y - c) :=
    chartTransitionExtended_hasCompactSupport_sub (I := I) (M := M) γ α hη_compact c
  exact
    Analysis.Sobolev.Euclidean.iter_deriv_bound_of_eq_const_offCompactSupport_atOrder
    (d := Module.finrank ℝ E) hT_smooth hT_diff_compact kmax

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_iter_deriv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_iter_deriv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_iter_deriv_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionExtended_iter_deriv_bound

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_mapsTo_overlap
    (γ α : M) {y : EuclN}
    (hy : y ∈ chartOverlapEuclid (I := I) (M := M) γ α) :
    chartTransitionEuclid (I := I) (M := M) γ α y ∈
      chartOverlapEuclid (I := I) (M := M) α γ := by
  rcases hy with ⟨z, ⟨x, hx_in, hxz⟩, hzy⟩
  have h_T_eq : chartTransitionEuclid (I := I) (M := M) γ α y =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    rw [← hzy, ← hxz]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_in.1
  rw [h_T_eq]
  refine ⟨extChartAt I α x, ?_, rfl⟩
  refine ⟨x, ⟨hx_in.2, hx_in.1⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_mapsTo_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_mapsTo_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_mapsTo_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_mapsTo_overlap

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_left_inv
    (γ α : M) {y : EuclN}
    (hy : y ∈ chartOverlapEuclid (I := I) (M := M) γ α) :
    chartTransitionEuclid (I := I) (M := M) α γ
      (chartTransitionEuclid (I := I) (M := M) γ α y) = y := by
  rcases hy with ⟨z, ⟨x, hx_in, hxz⟩, hzy⟩
  have hy_eq : y = (toEuclidean (E := E)) (extChartAt I γ x) := by
    rw [← hzy, ← hxz]
  have h_T1 : chartTransitionEuclid (I := I) (M := M) γ α y =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    rw [hy_eq]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_in.1
  rw [h_T1]
  have h_T2 : chartTransitionEuclid (I := I) (M := M) α γ
      ((toEuclidean (E := E)) (extChartAt I α x)) =
      (toEuclidean (E := E)) (extChartAt I γ x) :=
    chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ hx_in.2
  rw [h_T2, hy_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_left_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_left_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_left_inv ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_left_inv

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_injOn_overlap
    (γ α : M) :
    Set.InjOn (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  intro y₁ hy₁ y₂ hy₂ heq
  have h1 := chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy₁
  have h2 := chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy₂
  rw [← h1, ← h2, heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_injOn_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_injOn_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_injOn_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_injOn_overlap

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_surjOn_overlap
    (γ α : M) :
    Set.SurjOn (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) α γ) := by
  intro z hz
  rcases hz with ⟨w, ⟨x, hx_in, hxw⟩, hwz⟩
  refine ⟨(toEuclidean (E := E)) (extChartAt I γ x), ?_, ?_⟩
  · refine ⟨extChartAt I γ x, ?_, rfl⟩
    refine ⟨x, ⟨hx_in.2, hx_in.1⟩, rfl⟩
  · rw [chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_in.2]
    rw [← hwz, ← hxw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_surjOn_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_surjOn_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_surjOn_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_surjOn_overlap

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_bijOn_overlap
    (γ α : M) :
    Set.BijOn (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) α γ) :=
  ⟨fun _ hy => chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy,
    chartTransitionEuclid_injOn_overlap (I := I) (M := M) γ α,
    chartTransitionEuclid_surjOn_overlap (I := I) (M := M) γ α⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_bijOn_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_bijOn_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_bijOn_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionEuclid_bijOn_overlap

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
