import Submission.DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Compactness.Lindelof
import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.Topology.Piecewise
import Mathlib.Geometry.Manifold.HasGroupoid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Function _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.Interval

namespace AbsolutelyContinuousOnInterval
open _root_.AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

open _root_.AbsolutelyContinuousOnInterval in
theorem ae_mdifferentiableAt_of_extChartAt
    {a b : ℝ} {gamma : ℝ → M} (p : M)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) a b)
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.uIcc a b) (chartAt H p).source) :
    ∀ᵐ r ∂volume.restrict (_root_.Set.uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
  have hmaps : _root_.Set.MapsTo ((extChartAt I p) ∘ gamma) (_root_.Set.uIcc a b)
      (extChartAt I p).target := by
    intro r hr
    exact (extChartAt I p).map_source (by
      simpa only [extChartAt_source] using hsrc hr)
  have hcont : ContinuousOn gamma (_root_.Set.uIcc a b) := by
    have h := (continuousOn_extChartAt_symm p).comp hAC.continuousOn hmaps
    refine h.congr ?_
    intro r hr
    exact ((extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hsrc hr)).symm
  have hmem : ∀ᵐ r ∂volume.restrict (_root_.Set.uIcc a b), r ∈ _root_.Set.Ioo (_root_.Min.min a b) (_root_.Max.max a b) := by
    rw [_root_.Set.uIcc, ← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hdiff : ∀ᵐ r ∂volume.restrict (_root_.Set.uIcc a b),
      r ∈ _root_.Set.uIcc a b → DifferentiableAt ℝ ((extChartAt I p) ∘ gamma) r :=
    _root_.MeasureTheory.ae_mono Measure.restrict_le_self
      hAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff, hmem] with r hr hri
  have hcc : r ∈ _root_.Set.uIcc a b := ⟨hri.1.le, hri.2.le⟩
  apply (mdifferentiableAt_iff_target_of_mem_source (hsrc hcc)).mpr
  refine ⟨(hcont r hcc).continuousAt (Icc_mem_nhds hri.1 hri.2), ?_⟩
  exact mdifferentiableAt_iff_differentiableAt.mpr (hr hcc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.ae_mdifferentiableAt_of_extChartAt then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.ae_mdifferentiableAt_of_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.ae_mdifferentiableAt_of_extChartAt ``Submission.AbsolutelyContinuousOnInterval.ae_mdifferentiableAt_of_extChartAt

end AbsolutelyContinuousOnInterval

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def absolutelyContinuousOnInterval (gamma : ℝ → M) (a b : ℝ) : Prop :=
  ContinuousOn gamma (_root_.Set.uIcc a b) ∧
    ∀ (p : M) (c d : ℝ), _root_.Set.uIcc c d ⊆ _root_.Set.uIcc a b →
      _root_.Set.MapsTo gamma (_root_.Set.uIcc c d) (chartAt H p).source →
      AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval ``Submission.Manifold.absolutelyContinuousOnInterval

variable {I} {gamma : ℝ → M} {a b c d : ℝ}

theorem absolutelyContinuousOnInterval_continuousOn
    (h : absolutelyContinuousOnInterval I gamma a b) :
    ContinuousOn gamma (_root_.Set.uIcc a b) := h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_continuousOn then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_continuousOn ``Submission.Manifold.absolutelyContinuousOnInterval_continuousOn

theorem absolutelyContinuousOnInterval_mono
    (h : absolutelyContinuousOnInterval I gamma a b) (hsub : _root_.Set.uIcc c d ⊆ _root_.Set.uIcc a b) :
    absolutelyContinuousOnInterval I gamma c d :=
  ⟨h.1.mono hsub, fun p e f hef hmaps => h.2 p e f (hef.trans hsub) hmaps⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_mono then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_mono ``Submission.Manifold.absolutelyContinuousOnInterval_mono

theorem absolutelyContinuousOnInterval_symm
    (h : absolutelyContinuousOnInterval I gamma a b) :
    absolutelyContinuousOnInterval I gamma b a := by
  simpa only [absolutelyContinuousOnInterval, _root_.Set.uIcc_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_symm then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_symm ``Submission.Manifold.absolutelyContinuousOnInterval_symm

variable [IsManifold I 1 M]

theorem absolutelyContinuousOnInterval_of_contMDiffOn
    (h : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.uIcc a b)) :
    absolutelyContinuousOnInterval I gamma a b := by
  refine ⟨h.continuousOn, fun p c d hsub hmaps => ?_⟩
  exact ((contMDiffOn_extChartAt (I := I) (x := p) (n := 1)).comp
    (h.mono hsub) hmaps).contDiffOn.absolutelyContinuousOnInterval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_of_contMDiffOn ``Submission.Manifold.absolutelyContinuousOnInterval_of_contMDiffOn

variable [FiniteDimensional ℝ E]

theorem absolutelyContinuousOnInterval_ae_mdifferentiableAt
    (h : absolutelyContinuousOnInterval I gamma a b) :
    ∀ᵐ t ∂volume.restrict (_root_.Set.uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t := by
  have hlocal : ∀ t ∈ _root_.Set.Ioo (_root_.Min.min a b) (_root_.Max.max a b), ∃ c d : ℝ,
      _root_.Set.Icc c d ∈ 𝓝 t ∧
      ∀ᵐ r ∂volume.restrict (_root_.Set.Icc c d), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
    intro t ht
    have htcc : t ∈ _root_.Set.uIcc a b := ⟨ht.1.le, ht.2.le⟩
    have hcont := (h.1 t htcc).continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hsrc : gamma ⁻¹' (chartAt H (gamma t)).source ∈ 𝓝 t :=
      hcont.preimage_mem_nhds ((chartAt H (gamma t)).open_source.mem_nhds (mem_chart_source H (gamma t)))
    obtain ⟨c, d, htcd, hnhds, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds
      (_root_.Filter.inter_mem (Icc_mem_nhds ht.1 ht.2) hsrc)
    have hcd : c ≤ d := htcd.1.trans htcd.2
    have hmaps : _root_.Set.MapsTo gamma (_root_.Set.uIcc c d) (chartAt H (gamma t)).source := by
      rw [_root_.Set.uIcc_of_le hcd]
      exact fun r hr => (hsub hr).2
    have hac := h.2 (gamma t) c d (by
      rw [_root_.Set.uIcc_of_le hcd]
      exact fun r hr => (hsub hr).1) hmaps
    refine ⟨c, d, hnhds, ?_⟩
    simpa only [_root_.Set.uIcc_of_le hcd] using hac.ae_mdifferentiableAt_of_extChartAt (gamma t) hmaps
  choose c d hnhds hae using hlocal
  obtain ⟨s, hs, hcover⟩ := (isLindelof_iff_lindelofSpace.mpr
    (inferInstance : LindelofSpace (_root_.Set.Ioo (_root_.Min.min a b) (_root_.Max.max a b)))).elim_nhds_subcover'
      (fun t ht => _root_.Set.Icc (c t ht) (d t ht)) hnhds
  have hunion : ∀ᵐ r ∂volume.restrict
      (⋃ t ∈ s, _root_.Set.Icc (c t t.2) (d t t.2)), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r :=
    (_root_.MeasureTheory.ae_restrict_biUnion_iff _ hs _).mpr (fun t _ => hae t t.2)
  have hinner := _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hcover) hunion
  rw [_root_.Set.uIcc, ← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  exact hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt ``Submission.Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt

end Manifold

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem absolutelyContinuousOnInterval_piecewise_Iic
    {alpha beta : ℝ → M} {a c b : ℝ}
    (hα : absolutelyContinuousOnInterval I alpha a c)
    (hβ : absolutelyContinuousOnInterval I beta c b)
    (hac : a ≤ c) (hcb : c ≤ b) (hnode : alpha c = beta c) :
    absolutelyContinuousOnInterval I (_root_.Set.piecewise (_root_.Set.Iic c) alpha beta) a b := by
  classical
  let gamma := _root_.Set.piecewise (_root_.Set.Iic c) alpha beta
  have hleft : ∀ t ≤ c, gamma t = alpha t := fun t ht => _root_.Set.piecewise_eq_of_mem _ _ _ ht
  have hright : ∀ t, c ≤ t → gamma t = beta t := by
    intro t ht
    by_cases htc : t = c
    · subst t
      exact (hleft c le_rfl).trans hnode
    · exact _root_.Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr (lt_of_le_of_ne ht (Ne.symm htc)))
  constructor
  · rw [_root_.Set.uIcc_of_le (hac.trans hcb)]
    apply ContinuousOn.piecewise
    · intro t ht
      have htc : t = c := by simpa only [frontier_Iic, _root_.Set.mem_singleton_iff] using ht.2
      simpa only [htc] using hnode
    · apply hα.1.mono
      rw [isClosed_Iic.closure_eq, _root_.Set.uIcc_of_le hac]
      exact fun t ht => ⟨ht.1.1, ht.2⟩
    · apply hβ.1.mono
      rw [_root_.Set.compl_Iic, closure_Ioi, _root_.Set.uIcc_of_le hcb]
      exact fun t ht => ⟨ht.2, ht.1.2⟩
  have hordered : ∀ (p : M) (x y : ℝ), x ≤ y → _root_.Set.Icc x y ⊆ _root_.Set.Icc a b →
      _root_.Set.MapsTo gamma (_root_.Set.Icc x y) (chartAt H p).source →
      AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) x y := by
    intro p x y hxy hsub hsrc
    have hax : a ≤ x := (hsub (left_mem_Icc.mpr hxy)).1
    have hyb : y ≤ b := (hsub (right_mem_Icc.mpr hxy)).2
    by_cases hyc : y ≤ c
    · have hsrα : _root_.Set.MapsTo alpha (_root_.Set.uIcc x y) (chartAt H p).source := by
        rw [_root_.Set.uIcc_of_le hxy]
        intro t ht
        rw [← hleft t (ht.2.trans hyc)]
        exact hsrc ht
      have hsα : _root_.Set.uIcc x y ⊆ _root_.Set.uIcc a c := by
        rw [_root_.Set.uIcc_of_le hxy, _root_.Set.uIcc_of_le hac]
        exact _root_.Set.Icc_subset_Icc hax hyc
      apply (hα.2 p x y hsα hsrα).congr
      intro t ht
      dsimp only [Function.comp_apply]
      rw [hleft t ((show t ≤ y from (show t ∈ _root_.Set.Icc x y by simpa only [_root_.Set.uIcc_of_le hxy] using ht).2).trans hyc)]
    by_cases hcx : c ≤ x
    · have hsrβ : _root_.Set.MapsTo beta (_root_.Set.uIcc x y) (chartAt H p).source := by
        rw [_root_.Set.uIcc_of_le hxy]
        intro t ht
        rw [← hright t (hcx.trans ht.1)]
        exact hsrc ht
      have hsβ : _root_.Set.uIcc x y ⊆ _root_.Set.uIcc c b := by
        rw [_root_.Set.uIcc_of_le hxy, _root_.Set.uIcc_of_le hcb]
        exact _root_.Set.Icc_subset_Icc hcx hyb
      apply (hβ.2 p x y hsβ hsrβ).congr
      intro t ht
      dsimp only [Function.comp_apply]
      rw [hright t (hcx.trans (show x ≤ t from (show t ∈ _root_.Set.Icc x y by simpa only [_root_.Set.uIcc_of_le hxy] using ht).1))]
    have hxc : x ≤ c := (lt_of_not_ge hcx).le
    have hcy : c ≤ y := (lt_of_not_ge hyc).le
    have hsrα : _root_.Set.MapsTo alpha (_root_.Set.uIcc x c) (chartAt H p).source := by
      rw [_root_.Set.uIcc_of_le hxc]
      intro t ht
      rw [← hleft t ht.2]
      exact hsrc ⟨ht.1, ht.2.trans hcy⟩
    have hsrβ : _root_.Set.MapsTo beta (_root_.Set.uIcc c y) (chartAt H p).source := by
      rw [_root_.Set.uIcc_of_le hcy]
      intro t ht
      rw [← hright t ht.1]
      exact hsrc ⟨hxc.trans ht.1, ht.2⟩
    have hsα : _root_.Set.uIcc x c ⊆ _root_.Set.uIcc a c := by
      rw [_root_.Set.uIcc_of_le hxc, _root_.Set.uIcc_of_le hac]
      exact _root_.Set.Icc_subset_Icc_left hax
    have hsβ : _root_.Set.uIcc c y ⊆ _root_.Set.uIcc c b := by
      rw [_root_.Set.uIcc_of_le hcy, _root_.Set.uIcc_of_le hcb]
      exact _root_.Set.Icc_subset_Icc_right hyb
    have hjoin := (hα.2 p x c hsα hsrα).piecewise_Iic hxc hcy
      (hβ.2 p c y hsβ hsrβ) (congrArg (extChartAt I p) hnode)
    apply hjoin.congr
    intro t _
    by_cases htc : t ≤ c
    · simp only [_root_.Set.piecewise_eq_of_mem (_root_.Set.Iic c) _ _ htc, Function.comp_apply, hleft t htc]
    · simp only [_root_.Set.piecewise_eq_of_notMem (_root_.Set.Iic c) _ _ htc, Function.comp_apply,
        hright t (le_of_not_ge htc)]
  intro p x y hsub hsrc
  rcases le_total x y with hxy | hyx
  · apply hordered p x y hxy
    · simpa only [_root_.Set.uIcc_of_le hxy, _root_.Set.uIcc_of_le (hac.trans hcb)] using hsub
    · simpa only [_root_.Set.uIcc_of_le hxy] using hsrc
  · apply AbsolutelyContinuousOnInterval.symm
    apply hordered p y x hyx
    · simpa only [_root_.Set.uIcc_of_ge hyx, _root_.Set.uIcc_of_le (hac.trans hcb)] using hsub
    · simpa only [_root_.Set.uIcc_of_ge hyx] using hsrc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_piecewise_Iic then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_piecewise_Iic"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_piecewise_Iic ``Submission.Manifold.absolutelyContinuousOnInterval_piecewise_Iic

end Manifold

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem absolutelyContinuousOnInterval_congr
    {gamma eta : ℝ → M} {a b : ℝ}
    (h : absolutelyContinuousOnInterval I gamma a b) (heq : _root_.Set.EqOn gamma eta (_root_.Set.uIcc a b)) :
    absolutelyContinuousOnInterval I eta a b := by
  refine ⟨h.1.congr (fun t ht => (heq ht).symm), ?_⟩
  intro p c d hsub hsrc
  have hsrc' : _root_.Set.MapsTo gamma (_root_.Set.uIcc c d) (chartAt H p).source := by
    intro t ht
    rw [heq (hsub ht)]
    exact hsrc ht
  apply (h.2 p c d hsub hsrc').congr
  intro t ht
  exact congrArg (extChartAt I p) (heq (hsub ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_congr then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_congr ``Submission.Manifold.absolutelyContinuousOnInterval_congr

theorem absolutelyContinuousOnInterval_subtype_of_val
    (U : TopologicalSpace.Opens M) {eta : ℝ → U} {a b : ℝ}
    (h : absolutelyContinuousOnInterval I (Subtype.val ∘ eta) a b) :
    absolutelyContinuousOnInterval I eta a b := by
  have hcont : ContinuousOn eta (_root_.Set.uIcc a b) := by
    exact Topology.IsInducing.subtypeVal.continuousOn_iff.mpr h.1
  refine ⟨hcont, ?_⟩
  intro p c d hsub hsrc
  have hsrc' : _root_.Set.MapsTo (Subtype.val ∘ eta) (_root_.Set.uIcc c d) (chartAt H p.val).source := by
    intro t ht
    have hp := hsrc ht
    simpa only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
      _root_.Set.mem_preimage, Function.comp_apply] using hp
  have hac := h.2 p.val c d hsub hsrc'
  exact hac

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_subtype_of_val then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_subtype_of_val"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_subtype_of_val ``Submission.Manifold.absolutelyContinuousOnInterval_subtype_of_val

theorem exists_absolutelyContinuousOnInterval_openSubtype
    (U : TopologicalSpace.Opens M) {gamma : ℝ → M} {a b : ℝ}
    (h : absolutelyContinuousOnInterval I gamma a b)
    (hU : _root_.Set.MapsTo gamma (_root_.Set.uIcc a b) U) :
    ∃ eta : ℝ → U, absolutelyContinuousOnInterval I eta a b ∧
      EqOn (Subtype.val ∘ eta) gamma (_root_.Set.uIcc a b) := by
  classical
  let eta : ℝ → U := fun t => if ht : t ∈ _root_.Set.uIcc a b then ⟨gamma t, hU ht⟩
    else ⟨gamma a, hU left_mem_uIcc⟩
  have heq : _root_.Set.EqOn (Subtype.val ∘ eta) gamma (_root_.Set.uIcc a b) := by
    intro t ht
    simp only [eta, dif_pos ht, Function.comp_apply]
  refine ⟨eta, ?_, heq⟩
  apply absolutelyContinuousOnInterval_subtype_of_val U
  exact absolutelyContinuousOnInterval_congr h heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_absolutelyContinuousOnInterval_openSubtype then
    throwError "Refusing to shadow existing declaration Manifold.exists_absolutelyContinuousOnInterval_openSubtype"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_absolutelyContinuousOnInterval_openSubtype ``Submission.Manifold.exists_absolutelyContinuousOnInterval_openSubtype

end Manifold

namespace Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem absolutelyContinuousOnInterval_of_extChartAt
    {γ : ℝ → M} {a b : ℝ} (p : M)
    (hsrc : _root_.Set.MapsTo γ (_root_.Set.uIcc a b) (chartAt H p).source)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ γ) a b) :
    absolutelyContinuousOnInterval I γ a b := by
  have hsrc' : _root_.Set.MapsTo γ (_root_.Set.uIcc a b) (extChartAt I p).source := by
    simpa only [extChartAt_source] using hsrc
  have hcont : ContinuousOn γ (_root_.Set.uIcc a b) := by
    have hmaps : _root_.Set.MapsTo ((extChartAt I p) ∘ γ) (_root_.Set.uIcc a b) (extChartAt I p).target :=
      fun r hr => (extChartAt I p).map_source (hsrc' hr)
    have hc := (continuousOn_extChartAt_symm p).comp hAC.continuousOn hmaps
    apply hc.congr
    intro r hr
    exact ((extChartAt I p).left_inv (hsrc' hr)).symm
  refine ⟨hcont, ?_⟩
  intro q c d hsub hqsrc
  let F : E → E := extChartAt I q ∘ (extChartAt I p).symm
  let K : Set E := ((extChartAt I p) ∘ γ) '' _root_.Set.uIcc c d
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn (hAC.continuousOn.mono hsub)
  have hKcoord : K ⊆ ((extChartAt I p).symm ≫ extChartAt I q).source := by
    rintro x ⟨r, hr, rfl⟩
    refine ⟨(extChartAt I p).map_source (hsrc' (hsub hr)), ?_⟩
    change (extChartAt I p).symm ((extChartAt I p) (γ r)) ∈ (extChartAt I q).source
    rw [(extChartAt I p).left_inv (hsrc' (hsub hr))]
    simpa only [extChartAt_source] using hqsrc hr
  have hlocal : LocallyLipschitzOn K F := by
    intro x hx
    have hcoord := contDiffWithinAt_ext_coord_change (I := I) (n := (1 : WithTop ℕ∞)) q p (hKcoord hx)
    have hcd : ContDiffAt ℝ 1 F x := by
      apply hcoord.contDiffAt
      simp only [ModelWithCorners.range_eq_univ, _root_.Filter.univ_mem]
    obtain ⟨C, V, hV, hCV⟩ := hcd.exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hCV⟩
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact hK
  have hh := hC.comp_absolutelyContinuousOnInterval (hAC.mono hsub)
    (fun r hr => _root_.Set.mem_image_of_mem _ hr)
  apply hh.congr
  intro r hr
  change (extChartAt I q) ((extChartAt I p).symm ((extChartAt I p) (γ r))) =
    (extChartAt I q) (γ r)
  rw [(extChartAt I p).left_inv (hsrc' (hsub hr))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_of_extChartAt then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_of_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_of_extChartAt ``Submission.Manifold.absolutelyContinuousOnInterval_of_extChartAt


omit [I.Boundaryless] [IsManifold I 1 M] in
theorem absolutelyContinuousOnInterval_of_finite_partition
    {γ : ℝ → M} {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hpiece : ∀ i : Fin m, absolutelyContinuousOnInterval I γ (t i.castSucc) (t i.succ)) :
    absolutelyContinuousOnInterval I γ (t 0) (t (Fin.last m)) := by
  have hprefix (k : Fin (m + 1)) : absolutelyContinuousOnInterval I γ (t 0) (t k) := by
    induction k using Fin.induction with
    | zero =>
      have hconst : absolutelyContinuousOnInterval I (fun _ : ℝ => γ (t 0)) (t 0) (t 0) := by
        refine ⟨continuousOn_const, ?_⟩
        intro p c d _ _
        exact (contDiff_const.contDiffOn.absolutelyContinuousOnInterval :
          AbsolutelyContinuousOnInterval (fun _ : ℝ => extChartAt I p (γ (t 0))) c d)
      apply absolutelyContinuousOnInterval_congr hconst
      intro r hr
      have heq : r = t 0 := by simpa only [_root_.Set.uIcc_self, _root_.Set.mem_singleton_iff] using hr
      subst r
      rfl
    | succ k ih =>
      have hh := absolutelyContinuousOnInterval_piecewise_Iic ih (hpiece k)
        (ht (Fin.zero_le _)) (ht k.castSucc_le_succ) rfl
      simpa only [Set.piecewise_same] using hh
  exact hprefix (Fin.last m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_of_finite_partition then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_of_finite_partition"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_of_finite_partition ``Submission.Manifold.absolutelyContinuousOnInterval_of_finite_partition

end Manifold

open scoped _root_.ContDiff

namespace Manifold

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

theorem absolutelyContinuousOnInterval_comp_contMDiff
    {gamma : ℝ → M} {a b : ℝ} (hgamma : absolutelyContinuousOnInterval I gamma a b)
    {f : M → N} (hf : ContMDiff I J 1 f) :
    absolutelyContinuousOnInterval J (f ∘ gamma) a b := by
  have hpart (q : N) (c d : ℝ) (hcd : c ≤ d)
      (hsub : _root_.Set.uIcc c d ⊆ _root_.Set.uIcc a b)
      (hmaps : _root_.Set.MapsTo (f ∘ gamma) (_root_.Set.uIcc c d) (chartAt H' q).source) :
      AbsolutelyContinuousOnInterval ((extChartAt J q) ∘ f ∘ gamma) c d := by
    obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hcharts⟩ :=
      DifferentialGeometry.Geometry.exists_chart_subdivision (H := H) hcd
        (hgamma.1.mono (Icc_subset_uIcc.trans hsub))
    have hsegment (n : ℕ) : AbsolutelyContinuousOnInterval
        ((extChartAt J q) ∘ f ∘ gamma) (t n).val (t (n + 1)).val := by
      have hle : (t n).val ≤ (t (n + 1)).val := htmono (Nat.le_succ n)
      have hseg : _root_.Set.uIcc (t n).val (t (n + 1)).val ⊆ _root_.Set.uIcc c d := by
        rw [_root_.Set.uIcc_of_le hle, _root_.Set.uIcc_of_le hcd]
        exact _root_.Set.Icc_subset_Icc (t n).property.1 (t (n + 1)).property.2
      obtain ⟨p, hp⟩ := hcharts n
      have hsrc : _root_.Set.MapsTo gamma (_root_.Set.uIcc (t n).val (t (n + 1)).val) (chartAt H p).source := by
        simpa only [_root_.Set.uIcc_of_le hle] using hp
      have hAC := hgamma.2 p (t n).val (t (n + 1)).val (hseg.trans hsub) hsrc
      let K := ((extChartAt I p) ∘ gamma) '' _root_.Set.uIcc (t n).val (t (n + 1)).val
      have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hAC.continuousOn
      have hKr : K ⊆ _root_.Set.range I := by
        rintro x ⟨r, hr, rfl⟩
        exact extChartAt_target_subset_range p ((extChartAt I p).map_source
          (by simpa only [extChartAt_source] using hsrc hr))
      have hloc : LocallyLipschitzOn K ((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) := by
        rintro x ⟨r, hr, rfl⟩
        have hC := ((contMDiffAt_iff_of_mem_source (hsrc hr) (hmaps (hseg hr))).mp
          (hf.contMDiffAt (x := gamma r))).2
        obtain ⟨L, V, hV, hLip⟩ := hC.exists_lipschitzOnWith I.convex_range
        exact ⟨L, V, nhdsWithin_mono _ hKr hV, hLip⟩
      obtain ⟨L, hLip⟩ := hloc.exists_lipschitzOnWith_of_compact hK
      have h := hLip.comp_absolutelyContinuousOnInterval hAC
        (fun r hr => _root_.Set.mem_image_of_mem ((extChartAt I p) ∘ gamma) hr)
      apply h.congr
      intro r hr
      dsimp only [Function.comp_apply]
      rw [(extChartAt I p).left_inv (by simpa only [extChartAt_source] using hsrc hr)]
    have hjoin (n : ℕ) : AbsolutelyContinuousOnInterval
        ((extChartAt J q) ∘ f ∘ gamma) c (t n).val := by
      induction n with
      | zero =>
        rw [ht0]
        have h := hsegment 0
        rw [ht0] at h
        exact h.mono (by simp)
      | succ n ih =>
        simpa only [Set.piecewise_same] using
          AbsolutelyContinuousOnInterval.piecewise_Iic (t n).property.1
            (htmono (Nat.le_succ n)) ih (hsegment n) rfl
    simpa only [hm m le_rfl] using hjoin m
  refine ⟨hf.continuous.comp_continuousOn hgamma.1, ?_⟩
  intro q c d hsub hmaps
  rcases le_total c d with hcd | hdc
  · exact hpart q c d hcd hsub hmaps
  · exact (hpart q d c hdc (by simpa only [_root_.Set.uIcc_comm] using hsub)
      (by simpa only [_root_.Set.uIcc_comm] using hmaps)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_comp_contMDiff then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_comp_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_comp_contMDiff ``Submission.Manifold.absolutelyContinuousOnInterval_comp_contMDiff

end Manifold
