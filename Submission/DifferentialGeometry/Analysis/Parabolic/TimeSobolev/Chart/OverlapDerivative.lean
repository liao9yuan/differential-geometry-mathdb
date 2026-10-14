import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.C1Regularity
import Mathlib.Analysis.Calculus.Deriv.Shift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

omit [CompleteSpace E] in
theorem chartDeriv_shift {a b r : ℝ} (phi : ℝ → E)
    (u : timeH1 E (b - a))
    (hrep : _root_.Set.EqOn u.toFun (fun s ↦ phi (a + s))
      (_root_.Set.Icc (0 : ℝ) (b - a)))
    (hr : r ∈ _root_.Set.Icc (0 : ℝ) (b - a)) :
    derivWithin phi (_root_.Set.Icc a b) (a + r) =
      derivWithin u.toFun (_root_.Set.Icc (0 : ℝ) (b - a)) r := by
  let s : Set ℝ := _root_.Set.Icc (0 : ℝ) (b - a)
  have hset : a +ᵥ s = _root_.Set.Icc a b := by
    ext x
    simp only [_root_.Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
      _root_.Set.mem_Icc, s]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have heq : Filter.EventuallyEq (nhdsWithin r s) u.toFun
      (fun x ↦ phi (a + x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hrep hx
  calc
    derivWithin phi (_root_.Set.Icc a b) (a + r) =
        derivWithin (fun x ↦ phi (a + x)) s r := by
      rw [derivWithin_comp_const_add, hset]
    _ = derivWithin u.toFun s r :=
      (heq.derivWithin_eq_of_mem (by simpa only [s] using hr)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_shift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_shift ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_shift

omit [CompleteSpace E] in
theorem chartDeriv_change
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {s : Set ℝ} {x : ℝ} (p q : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma s)
    (hx : x ∈ s)
    (huniq : UniqueDiffWithinAt ℝ s x)
    (hp : _root_.Set.MapsTo gamma s (chartAt H p).source)
    (hq : gamma x ∈ (chartAt H q).source) :
    derivWithin ((extChartAt I q) ∘ gamma) s x =
      tangentCoordChange I p q (gamma x)
        (derivWithin ((extChartAt I p) ∘ gamma) s x) := by
  let f : E → E := (extChartAt I q) ∘ (extChartAt I p).symm
  have hphi : ContDiffOn ℝ 1 ((extChartAt I p) ∘ gamma) s := by
    have hchart := ((contMDiffOn_iff_target.mp hgamma).2 p).mono
      (fun y hy ↦ ⟨hy, by
        rw [extChartAt_source]
        exact hp hy⟩)
    exact hchart.contDiffOn
  have hder : HasDerivWithinAt ((extChartAt I p) ∘ gamma)
      (derivWithin ((extChartAt I p) ∘ gamma) s x) s x :=
    (hphi.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hpsrc : gamma x ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp hx
  have hqsrc : gamma x ∈ (extChartAt I q).source := by
    rw [extChartAt_source]
    exact hq
  have hmap : _root_.Set.MapsTo ((extChartAt I p) ∘ gamma) s (_root_.Set.range I) := by
    intro y hy
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp hy))
  have hfun : _root_.Set.EqOn ((extChartAt I q) ∘ gamma)
      (f ∘ ((extChartAt I p) ∘ gamma)) s := by
    intro y hy
    simp only [f, Function.comp_apply]
    exact congrArg (extChartAt I q) ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hp hy)).symm
  have htrans := hasFDerivWithinAt_tangentCoordChange (I := I)
    (show gamma x ∈ (extChartAt I p).source ∩
        (extChartAt I q).source from ⟨hpsrc, hqsrc⟩)
  have hchain : HasDerivWithinAt
      (f ∘ ((extChartAt I p) ∘ gamma))
      (tangentCoordChange I p q (gamma x)
        (derivWithin ((extChartAt I p) ∘ gamma) s x)) s x := by
    exact htrans.comp_hasDerivWithinAt_of_eq x hder hmap rfl
  exact (hchain.congr_of_mem hfun hx).derivWithin huniq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_change then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_change"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_change ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_change

omit [CompleteSpace E] in
theorem chartDeriv_overlap
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 < T) (p q : M) (gamma : ℝ → M) (u v : timeH1 E T)
    (hp : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source)
    (hq : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H q).source)
    (hup : _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T))
    (huq : _root_.Set.EqOn v.toFun ((extChartAt I q) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T))
    (hu : ContDiffOn ℝ 1 u.toFun (_root_.Set.Icc (0 : ℝ) T))
    (hv : ContDiffOn ℝ 1 v.toFun (_root_.Set.Icc (0 : ℝ) T)) :
    _root_.Set.EqOn (fun t ↦ derivWithin v.toFun (_root_.Set.Icc (0 : ℝ) T) t)
      (fun t ↦ tangentCoordChange I p q (gamma t)
        (derivWithin u.toFun (_root_.Set.Icc (0 : ℝ) T) t))
      (_root_.Set.Icc (0 : ℝ) T) := by
  let s : Set ℝ := _root_.Set.Icc (0 : ℝ) T
  let f : E → E := (extChartAt I q) ∘ (extChartAt I p).symm
  have humap : _root_.Set.MapsTo u.toFun s (_root_.Set.range I) := by
    intro r hr
    rw [hup hr]
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp hr))
  have hfun : _root_.Set.EqOn v.toFun (f ∘ u.toFun) s := by
    intro r hr
    have hpsrc : gamma r ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hp hr
    rw [huq hr]
    simp only [f, Function.comp_apply]
    rw [hup hr]
    exact congrArg (extChartAt I q) ((extChartAt I p).left_inv hpsrc).symm
  intro t ht
  have hpsrc : gamma t ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp ht
  have hqsrc : gamma t ∈ (extChartAt I q).source := by
    rw [extChartAt_source]
    exact hq ht
  have hdu : HasDerivWithinAt u.toFun (derivWithin u.toFun s t) s t :=
    (hu.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdv : HasDerivWithinAt v.toFun (derivWithin v.toFun s t) s t :=
    (hv.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have htrans := hasFDerivWithinAt_tangentCoordChange (I := I)
    (show gamma t ∈ (extChartAt I p).source ∩ (extChartAt I q).source from
      ⟨hpsrc, hqsrc⟩)
  have hchain : HasDerivWithinAt (f ∘ u.toFun)
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t := by
    exact htrans.comp_hasDerivWithinAt_of_eq t hdu humap (hup ht).symm
  have hvchain : HasDerivWithinAt v.toFun
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t :=
    hchain.congr_of_mem hfun ht
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv s hdv hvchain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_overlap ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_overlap

omit [CompleteSpace E] in
theorem chartDeriv_head
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T L : ℝ} (hT : 0 < T) (hTL : T ≤ L) (p q : M)
    (gamma : ℝ → M) (u : timeH1 E T) (v : timeH1 E L)
    (hp : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H p).source)
    (hq : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : ℝ) T) (chartAt H q).source)
    (hup : _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T))
    (huq : _root_.Set.EqOn v.toFun ((extChartAt I q) ∘ gamma) (_root_.Set.Icc (0 : ℝ) T))
    (hu : ContDiffOn ℝ 1 u.toFun (_root_.Set.Icc (0 : ℝ) T))
    (hv : ContDiffOn ℝ 1 v.toFun (_root_.Set.Icc (0 : ℝ) L)) :
    _root_.Set.EqOn (fun t ↦ derivWithin v.toFun (_root_.Set.Icc (0 : ℝ) L) t)
      (fun t ↦ tangentCoordChange I p q (gamma t)
        (derivWithin u.toFun (_root_.Set.Icc (0 : ℝ) T) t))
      (_root_.Set.Icc (0 : ℝ) T) := by
  let s : Set ℝ := _root_.Set.Icc (0 : ℝ) T
  let s' : Set ℝ := _root_.Set.Icc (0 : ℝ) L
  let f : E → E := (extChartAt I q) ∘ (extChartAt I p).symm
  have hsub : s ⊆ s' := by
    exact _root_.Set.Icc_subset_Icc_right hTL
  have humap : _root_.Set.MapsTo u.toFun s (_root_.Set.range I) := by
    intro r hr
    rw [hup hr]
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hp hr))
  have hfun : _root_.Set.EqOn v.toFun (f ∘ u.toFun) s := by
    intro r hr
    have hpsrc : gamma r ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hp hr
    rw [huq hr]
    simp only [f, Function.comp_apply]
    rw [hup hr]
    exact congrArg (extChartAt I q) ((extChartAt I p).left_inv hpsrc).symm
  intro t ht
  have hpsrc : gamma t ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp ht
  have hqsrc : gamma t ∈ (extChartAt I q).source := by
    rw [extChartAt_source]
    exact hq ht
  have hdu : HasDerivWithinAt u.toFun (derivWithin u.toFun s t) s t :=
    (hu.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdv' : HasDerivWithinAt v.toFun (derivWithin v.toFun s' t) s' t :=
    (hv.differentiableOn (by norm_num) t (hsub ht)).hasDerivWithinAt
  have hdv : HasDerivWithinAt v.toFun (derivWithin v.toFun s' t) s t :=
    hdv'.mono hsub
  have htrans := hasFDerivWithinAt_tangentCoordChange (I := I)
    (show gamma t ∈ (extChartAt I p).source ∩ (extChartAt I q).source from
      ⟨hpsrc, hqsrc⟩)
  have hchain : HasDerivWithinAt (f ∘ u.toFun)
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t := by
    exact htrans.comp_hasDerivWithinAt_of_eq t hdu humap (hup ht).symm
  have hvchain : HasDerivWithinAt v.toFun
      (tangentCoordChange I p q (gamma t) (derivWithin u.toFun s t)) s t :=
    hchain.congr_of_mem hfun ht
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv s hdv hvchain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_head then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_head"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_head ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.chartDeriv_head

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
