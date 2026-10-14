import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u
variable {W : Type u} [MetricSpace W]

namespace EndRay


def restrict {E : UniformSpace.Completion W} (a : EndRay E)
    (d : ℝ) (hd : 0 < d) (hda : d ≤ a.length) : EndRay E where
  length := d
  length_pos := hd
  point := a.point
  radial s hs := a.radial s ⟨hs.1, hs.2.trans hda⟩
  minimizing s hs t ht := a.minimizing s ⟨hs.1, hs.2.trans hda⟩
    t ⟨ht.1, ht.2.trans hda⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict


theorem restrict_eventuallyEqual {E : UniformSpace.Completion W} (a : EndRay E)
    (d : ℝ) (hd : 0 < d) (hda : d ≤ a.length) :
    (a.restrict d hd hda).EventuallyEqual a :=
  ⟨d, hd, le_min le_rfl hda, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict_eventuallyEqual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict_eventuallyEqual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict_eventuallyEqual ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.restrict_eventuallyEqual


theorem eventuallyEqual_refl {E : UniformSpace.Completion W} (a : EndRay E) :
    a.EventuallyEqual a :=
  ⟨a.length, a.length_pos, le_min le_rfl le_rfl, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.eventuallyEqual_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.eventuallyEqual_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.eventuallyEqual_refl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.eventuallyEqual_refl


theorem EventuallyEqual.symm {E : UniformSpace.Completion W} {a b : EndRay E}
    (h : a.EventuallyEqual b) : b.EventuallyEqual a := by
  obtain ⟨d, hd, hlen, heq⟩ := h
  exact ⟨d, hd, by simpa [min_comm] using hlen, fun s hs => (heq s hs).symm⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.symm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.symm


theorem EventuallyEqual.trans {E : UniformSpace.Completion W} {a b c : EndRay E}
    (hab : a.EventuallyEqual b) (hbc : b.EventuallyEqual c) : a.EventuallyEqual c := by
  obtain ⟨d, hd, hlen, heq⟩ := hab
  obtain ⟨e, he, helen, heeq⟩ := hbc
  refine ⟨min d e, lt_min hd he,
    le_min ((min_le_left _ _).trans (hlen.trans (min_le_left _ _)))
      ((min_le_right _ _).trans (helen.trans (min_le_right _ _))), ?_⟩
  intro s hs
  exact (heq s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩).trans
    (heeq s ⟨hs.1, hs.2.trans (min_le_right _ _)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.trans ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual.trans

end EndRay

theorem endComparisonAngle_self_radius_eq_zero_iff
    {E : UniformSpace.Completion W} (a b : EndRay E) {s : ℝ} (hs : 0 < s) :
    endComparisonAngle a b s s = 0 ↔ a.point s = b.point s := by
  rw [endComparisonAngle, Real.arccos_eq_zero]
  have hden : 0 < 2 * s * s := by positivity
  rw [le_div_iff₀ hden]
  constructor
  · intro h
    have hd : _root_.Dist.dist (a.point s) (b.point s) = 0 := by
      nlinarith [sq_nonneg (_root_.Dist.dist (a.point s) (b.point s)),
        dist_nonneg (x := a.point s) (y := b.point s)]
    exact dist_eq_zero.mp hd
  · intro h
    rw [h, dist_self]
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_self_radius_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_self_radius_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_self_radius_eq_zero_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_self_radius_eq_zero_iff

variable [ChartedSpace Surgery.Topology.ThreeSpace W] [IsManifold I3 ∞ W]

theorem EndAngles.comparison_le_angle_near_endpoint
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} (A : EndAngles H)
    (a b : EndRay H.endpoint) :
    ∃ d : ℝ, 0 < d ∧ d ≤ _root_.Min.min a.length b.length ∧
      ∀ s ∈ Set.Ioc 0 d, ∀ t ∈ Set.Ioc 0 d,
        endComparisonAngle a b s t ≤ A.angle a b := by
  obtain ⟨d, hd, hlen, hmono⟩ := A.monotone a b
  refine ⟨d, hd, hlen, ?_⟩
  intro s hs t ht
  by_contra hnot
  have hgap : 0 < (endComparisonAngle a b s t - A.angle a b) / 2 := by
    linarith [lt_of_not_ge hnot]
  obtain ⟨e, he, _helen, hlim⟩ := A.limit a b _ hgap
  let q := _root_.Min.min e (_root_.Min.min s t)
  have hq : 0 < q := lt_min he (lt_min hs.1 ht.1)
  have hqe : q ≤ e := min_le_left _ _
  have hqs : q ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hqt : q ≤ t := (min_le_right _ _).trans (min_le_right _ _)
  have hcmp := hmono q s q t hq hqs hs.2 hq hqt ht.2
  have hclose := (abs_lt.mp (hlim q ⟨hq, hqe⟩ q ⟨hq, hqe⟩)).2
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.comparison_le_angle_near_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.comparison_le_angle_near_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.comparison_le_angle_near_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.comparison_le_angle_near_endpoint

theorem EndAngles.angle_eq_zero_iff_eventuallyEqual
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} (A : EndAngles H)
    (a b : EndRay H.endpoint) : A.angle a b = 0 ↔ a.EventuallyEqual b := by
  let := A.metric
  constructor
  · intro hzero
    obtain ⟨d, hd, hlen, hcmp⟩ := A.comparison_le_angle_near_endpoint a b
    refine ⟨d, hd, hlen, ?_⟩
    intro s hs
    apply (endComparisonAngle_self_radius_eq_zero_iff a b hs.1).mp
    apply le_antisymm
    · simpa only [hzero] using hcmp s hs s hs
    · exact Real.arccos_nonneg _
  · intro heq
    rw [← A.distance, A.eventual_eq a b heq, dist_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.angle_eq_zero_iff_eventuallyEqual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.angle_eq_zero_iff_eventuallyEqual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.angle_eq_zero_iff_eventuallyEqual ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.angle_eq_zero_iff_eventuallyEqual


theorem EndAngles.classOf_eq_iff_eventuallyEqual
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} (A : EndAngles H)
    (a b : EndRay H.endpoint) : A.classOf a = A.classOf b ↔ a.EventuallyEqual b := by
  let := A.metric
  rw [← dist_eq_zero, A.distance, A.angle_eq_zero_iff_eventuallyEqual]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.classOf_eq_iff_eventuallyEqual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.classOf_eq_iff_eventuallyEqual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.classOf_eq_iff_eventuallyEqual ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles.classOf_eq_iff_eventuallyEqual

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
