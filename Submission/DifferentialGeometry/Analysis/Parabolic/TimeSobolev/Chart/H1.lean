import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

omit [CompleteSpace E] in
theorem chartCoord_contDiff
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) {T : ℝ} (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) T))
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source) :
    ContDiffOn ℝ 1 ((extChartAt I p) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T) := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact (contMDiffOn_extChartAt (I := I) (n := 1) (x := p)).comp hgamma hsrc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartCoord_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartCoord_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartCoord_contDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartCoord_contDiff

noncomputable def chartTimeH1
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) T))
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source) : timeH1 E T :=
  timeH1.ofContDiffOn hT ((extChartAt I p) ∘ gamma)
    (chartCoord_contDiff I p gamma hgamma hsrc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1

theorem chartTimeH1_toFun
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) T))
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source) :
    _root_.Set.EqOn (chartTimeH1 I hT p gamma hgamma hsrc).toFun
      ((extChartAt I p) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T) := by
  exact timeH1.toFun_ofContDiffOn hT ((extChartAt I p) ∘ gamma)
    (chartCoord_contDiff I p gamma hgamma hsrc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_toFun

omit [CompleteSpace E] in
theorem chartTimeH1_deriv
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) T))
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source) :
    (chartTimeH1 I hT p gamma hgamma hsrc).deriv
      =ᵐ[timeMeasure T] _root_.deriv ((extChartAt I p) ∘ gamma) := by
  exact timeH1.deriv_ofContDiffOn hT ((extChartAt I p) ∘ gamma)
    (chartCoord_contDiff I p gamma hgamma hsrc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartTimeH1_deriv

omit [CompleteSpace E] in
theorem curve_cont_of_h1
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) {R a b : ℝ} (alpha : ℝ → M) (u : timeH1 E R)
    (ha : 0 ≤ a) (hbR : b ≤ R)
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ alpha) (_root_.Set.Icc a b)) :
    ContinuousOn alpha (_root_.Set.Icc a b) := by
  have hu : ContinuousOn u.toFun (_root_.Set.Icc a b) :=
    u.continuousOn_toFun.mono fun s hs ↦
      ⟨ha.trans hs.1, hs.2.trans hbR⟩
  have hmaps : _root_.Set.MapsTo u.toFun (_root_.Set.Icc a b) (extChartAt I p).target := by
    intro s hs
    rw [hrep hs]
    apply (extChartAt I p).map_source
    rw [extChartAt_source]
    exact hsrc hs
  have hcont : ContinuousOn ((extChartAt I p).symm ∘ u.toFun) (_root_.Set.Icc a b) :=
    (continuousOn_extChartAt_symm p).comp hu hmaps
  refine hcont.congr ?_
  intro s hs
  rw [Function.comp_apply, hrep hs]
  simpa only [Function.comp_apply] using ((extChartAt I p).left_inv (by
    rw [extChartAt_source]
    exact hsrc hs)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_of_h1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_of_h1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_of_h1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_of_h1

omit [CompleteSpace E] in
theorem curve_cont_local
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) {a b : ℝ} (alpha : ℝ → M) (u : timeH1 E (b - a))
    (hab : a ≤ b)
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun (fun r ↦ extChartAt I p (alpha (a + r)))
      (_root_.Set.Icc (0 : ℝ) (b - a))) :
    ContinuousOn alpha (_root_.Set.Icc a b) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmaps : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : ℝ) (b - a))
      (extChartAt I p).target := by
    intro r hr
    rw [hrep hr]
    apply (extChartAt I p).map_source
    rw [extChartAt_source]
    exact hsrc ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hshift : ContinuousOn (fun r ↦ alpha (a + r))
      (_root_.Set.Icc (0 : ℝ) (b - a)) := by
    have hcont : ContinuousOn ((extChartAt I p).symm ∘ u.toFun)
        (_root_.Set.Icc (0 : ℝ) (b - a)) :=
      (continuousOn_extChartAt_symm p).comp u.continuousOn_toFun hmaps
    refine hcont.congr ?_
    intro r hr
    rw [Function.comp_apply, hrep hr]
    simpa only using ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩)).symm
  have hsub : _root_.Set.MapsTo (fun s : ℝ ↦ s - a) (_root_.Set.Icc a b)
      (_root_.Set.Icc (0 : ℝ) (b - a)) := by
    intro s hs
    exact ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩
  have hcomp := hshift.comp
    (continuous_id.sub continuous_const).continuousOn hsub
  refine hcomp.congr ?_
  intro s _hs
  simp only [Function.comp_apply, Pi.sub_apply, id_eq]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_local ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_cont_local

theorem curve_mdiff_local
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) {a b : ℝ} (alpha : ℝ → M) (u : timeH1 E (b - a))
    (hab : a ≤ b)
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun (fun r ↦ extChartAt I p (alpha (a + r)))
      (_root_.Set.Icc (0 : ℝ) (b - a))) :
    ∀ᵐ r ∂(timeMeasure (b - a)), MDifferentiableAt 𝓘(ℝ, ℝ) I alpha (a + r) := by
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmem : ∀ᵐ r ∂(timeMeasure (b - a)), r ∈ _root_.Set.Ioo (0 : ℝ) (b - a) := by
    unfold timeMeasure
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun, hmem] with r hur hr
  have hrIcc : r ∈ _root_.Set.Icc (0 : ℝ) (b - a) := ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hIcc : _root_.Set.Icc (0 : ℝ) (b - a) ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
  have hur' : HasDerivAt u.toFun (u.deriv r) r := hur.hasDerivAt hIcc
  have hsrc_r : alpha (a + r) ∈ (chartAt H p).source := by
    apply hsrc
    constructor
    · linarith [hr.1]
    · linarith [hr.2]
  have htar : u.toFun r ∈ (extChartAt I p).target := by
    rw [hrep hrIcc]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc_r)
  have hu : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u.toFun r := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hur'.differentiableAt
  have hshift : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ alpha (a + s)) r := by
    have hpre : u.toFun ⁻¹' _root_.Set.range I ∈ 𝓝 r :=
      Filter.mem_of_superset
        (Filter.mem_of_superset hIcc fun s hs ↦ by
          change u.toFun s ∈ (extChartAt I p).target
          rw [hrep hs]
          exact (extChartAt I p).map_source (by
            rw [extChartAt_source]
            apply hsrc
            constructor
            · linarith [hs.1]
            · linarith [hs.2]))
        fun _ hy ↦ extChartAt_target_subset_range p hy
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) I ((extChartAt I p).symm ∘ u.toFun) r :=
      mdifferentiableWithinAt_univ.mp
        (MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin (x := r)
          (f := u.toFun) (s := Set.univ) (mdifferentiableWithinAt_extChartAt_symm htar)
          hu.mdifferentiableWithinAt (by simpa using hpre))
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hIcc] with s hs
    rw [Function.comp_apply, hrep hs]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      apply hsrc
      constructor
      · linarith [hs.1]
      · linarith [hs.2])).symm
  have hsub : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ s - a) (a + r) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (hasDerivAt_id (a + r)).sub_const a |>.differentiableAt
  have hback : MDifferentiableAt 𝓘(ℝ, ℝ) I
      ((fun s ↦ alpha (a + s)) ∘ fun s : ℝ ↦ s - a) (a + r) :=
    MDifferentiableAt.comp_of_eq (x := a + r) (f := fun s : ℝ ↦ s - a) hshift hsub (by ring)
  apply hback.congr_of_eventuallyEq
  filter_upwards with s
  simp only [Function.comp_apply]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_mdiff_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_mdiff_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_mdiff_local ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_mdiff_local

theorem chartH1_overlap
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (p q : M) (gamma : ℝ → M) (u v : timeH1 E T)
    (hp : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source)
    (hq : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H q).source)
    (hup : _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T))
    (huq : _root_.Set.EqOn v.toFun ((extChartAt I q) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T)) :
    v.deriv =ᵐ[timeMeasure T]
      fun t ↦ tangentCoordChange I p q (gamma t) (u.deriv t) := by
  apply timeH1.chain_ae (f := (extChartAt I q) ∘ (extChartAt I p).symm)
    (s := _root_.Set.range I) u v (fun t ↦ tangentCoordChange I p q (gamma t))
  · intro t ht
    have hpsrc : gamma t ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hp ht
    have hqsrc : gamma t ∈ (extChartAt I q).source := by
      rw [extChartAt_source]
      exact hq ht
    have hderiv := hasFDerivWithinAt_tangentCoordChange (I := I)
      (show gamma t ∈ (extChartAt I p).source ∩ (extChartAt I q).source from
        ⟨hpsrc, hqsrc⟩)
    simpa only [hup ht, Function.comp_apply] using hderiv
  · intro t ht
    rw [hup ht]
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp ht))
  · intro t ht
    have hpsrc : gamma t ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hp ht
    rw [huq ht]
    simp only [Function.comp_apply]
    rw [hup ht]
    simp only [Function.comp_apply]
    rw [(extChartAt I p).left_inv hpsrc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap

theorem chartH1_overlap_c1
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p q : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma
      (_root_.Set.Icc (0 : ℝ) T))
    (hp : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source)
    (hq : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H q).source) :
    (chartTimeH1 I hT q gamma hgamma hq).deriv =ᵐ[timeMeasure T]
      fun t ↦ tangentCoordChange I p q (gamma t)
        ((chartTimeH1 I hT p gamma hgamma hp).deriv t) :=
  chartH1_overlap I p q gamma
    (chartTimeH1 I hT p gamma hgamma hp)
    (chartTimeH1 I hT q gamma hgamma hq) hp hq
    (chartTimeH1_toFun I hT p gamma hgamma hp)
    (chartTimeH1_toFun I hT q gamma hgamma hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap_c1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap_c1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap_c1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartH1_overlap_c1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
