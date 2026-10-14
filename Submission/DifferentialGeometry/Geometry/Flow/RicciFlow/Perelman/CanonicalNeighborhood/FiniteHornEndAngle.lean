import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngleKernel
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {W : Type u} [MetricSpace W]

def endRayFamily (E : UniformSpace.Completion W) :
    EndRay E → ℝ → UniformSpace.Completion W :=
  fun a s => (a.point s : UniformSpace.Completion W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily

def endRayLength (E : UniformSpace.Completion W) (d : ℝ) (a : EndRay E) : ℝ :=
  _root_.Min.min a.length d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayLength

theorem endRayFamily_isRadialFamily (E : UniformSpace.Completion W) (d : ℝ) :
    IsRadialFamily E (endRayLength E d) (endRayFamily E) :=
  fun a s hs => by
    rw [endRayFamily, dist_comm]
    exact a.radial s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily_isRadialFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily_isRadialFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily_isRadialFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayFamily_isRadialFamily

theorem radialComparisonAngle_endRay {E : UniformSpace.Completion W}
    (a b : EndRay E) (s t : ℝ) :
    radialComparisonAngle (endRayFamily E) a b s t = endComparisonAngle a b s t := by
  simp only [radialComparisonAngle, endRayFamily, endComparisonAngle, comparisonAngle,
    comparisonCosine, UniformSpace.Completion.dist_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_endRay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_endRay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_endRay ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_endRay

theorem endComparisonAngle_eq_zero_of_dist_eq_abs {E : UniformSpace.Completion W}
    (a b : EndRay E) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : _root_.Dist.dist (a.point s) (b.point t) = |s - t|) : endComparisonAngle a b s t = 0 := by
  have hcos : (s ^ 2 + t ^ 2 - _root_.Dist.dist (a.point s) (b.point t) ^ 2) / (2 * s * t) = 1 := by
    rw [h, sq_abs]
    field_simp
    ring
  simp only [endComparisonAngle, hcos, Real.arccos_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_zero_of_dist_eq_abs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_zero_of_dist_eq_abs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_zero_of_dist_eq_abs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_zero_of_dist_eq_abs

theorem radialComparisonAngle_eq_zero_of_dist_eq_abs {E : UniformSpace.Completion W}
    (a b : EndRay E) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : _root_.Dist.dist (a.point s) (b.point t) = |s - t|) :
    radialComparisonAngle (endRayFamily E) a b s t = 0 := by
  rw [radialComparisonAngle_endRay]
  exact endComparisonAngle_eq_zero_of_dist_eq_abs a b hs ht h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_eq_zero_of_dist_eq_abs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_eq_zero_of_dist_eq_abs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_eq_zero_of_dist_eq_abs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialComparisonAngle_eq_zero_of_dist_eq_abs

def endRayAngle (E : UniformSpace.Completion W) (d : ℝ) (a b : EndRay E) : ℝ :=
  limitingRadialAngle (endRayLength E d) (endRayFamily E) a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle

variable [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
variable {g : SmoothRiemannianMetric I3 W}

theorem endRayAngle_mem_Icc (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (a b : EndRay H.endpoint) : endRayAngle H.endpoint d a b ∈ _root_.Set.Icc 0 Real.pi :=
  limitingRadialAngle_mem_Icc (endRayFamily H.endpoint)
    (by simpa only [endRayLength] using lt_min a.length_pos hd)
    (by simpa only [endRayLength] using lt_min b.length_pos hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_mem_Icc ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_mem_Icc

theorem tendsto_endRayAngle (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a b : EndRay H.endpoint) :
    _root_.Filter.Tendsto (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (endRayAngle H.endpoint d a b)) := by
  have h := tendsto_limitingRadialAngle (endRayFamily H.endpoint)
    (by simpa only [endRayLength] using lt_min a.length_pos hd)
    (by simpa only [endRayLength] using lt_min b.length_pos hd) (hmono a b)
  simpa only [radialComparisonAngle_endRay, endRayAngle] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_endRayAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_endRayAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_endRayAngle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_endRayAngle

theorem endRayAngle_self (H : FiniteHorn g) {d : ℝ} (hd : 0 < d) (a : EndRay H.endpoint) :
    endRayAngle H.endpoint d a a = 0 := by
  apply limitingRadialAngle_self (by simpa only [endRayLength] using lt_min a.length_pos hd)
  intro s hs t ht
  simp only [endRayFamily, UniformSpace.Completion.dist_eq]
  exact a.minimizing s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩ t
    ⟨ht.1, ht.2.trans (min_le_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_self ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_self

theorem endRayAngle_comm (H : FiniteHorn g) (d : ℝ) (a b : EndRay H.endpoint) :
    endRayAngle H.endpoint d a b = endRayAngle H.endpoint d b a :=
  limitingRadialAngle_comm (endRayLength H.endpoint d) (endRayFamily H.endpoint) a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_comm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_comm

theorem endRayAngle_triangle (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a b c : EndRay H.endpoint) :
    endRayAngle H.endpoint d a c ≤ endRayAngle H.endpoint d a b +
      endRayAngle H.endpoint d b c := by
  apply limitingRadialAngle_triangle_of_minimizing H.endpoint
    (fun a => by simpa only [endRayLength] using lt_min a.length_pos hd)
    (endRayFamily_isRadialFamily H.endpoint d) ?_ (fun i j _ => hmono i j)
  intro a s hs t ht
  simp only [endRayFamily, UniformSpace.Completion.dist_eq]
  exact a.minimizing s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩ t
    ⟨ht.1, ht.2.trans (min_le_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_triangle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_triangle

theorem endRayAngle_limit (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a b : EndRay H.endpoint) {eta : ℝ} (heta : 0 < eta) :
    ∃ d' : ℝ, 0 < d' ∧ d' ≤ _root_.Min.min a.length b.length ∧
      ∀ s ∈ _root_.Set.Ioc (0 : ℝ) d', ∀ t ∈ _root_.Set.Ioc (0 : ℝ) d',
        |endComparisonAngle a b s t - endRayAngle H.endpoint d a b| < eta := by
  have h := tendsto_endRayAngle H hd hmono a b
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
      |endComparisonAngle a b p.1 p.2 - endRayAngle H.endpoint d a b| < eta := by
    refine (h.eventually (Metric.ball_mem_nhds (endRayAngle H.endpoint d a b) heta)).mono ?_
    intro y hy
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
  obtain ⟨pa, hpa, pb, hpb, hmain⟩ := Filter.eventually_prod_iff.mp hev
  obtain ⟨u, hu, hU'⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hpa
  obtain ⟨v, hv, hV'⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hpb
  refine ⟨min (_root_.Min.min u v) (_root_.Min.min a.length b.length), ?_,
    min_le_right _ _, ?_⟩
  · exact lt_min (lt_min hu hv) (lt_min a.length_pos b.length_pos)
  · intro s hs t ht
    exact hmain (hU' ⟨hs.1, hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩)
      (hV' ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_limit

theorem endRayAngle_eq_zero_of_eventuallyEqual (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    {a b : EndRay H.endpoint} (heq : a.EventuallyEqual b) :
    endRayAngle H.endpoint d a b = 0 := by
  have h := tendsto_endRayAngle H hd hmono a b
  have hzero : (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2) =ᶠ[
      𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    obtain ⟨e, he, hemin, hee⟩ := heq
    have hU : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ∈ _root_.Set.Ioc (0 : ℝ) e := Ioc_mem_nhdsGT he
    filter_upwards [hU.prod_mk hU] with p hp
    refine endComparisonAngle_eq_zero_of_dist_eq_abs a b hp.1.1 hp.2.1 ?_
    rw [hee p.1 ⟨hp.1.1, hp.1.2⟩,
      b.minimizing p.1 ⟨hp.1.1, (hp.1.2.trans hemin).trans (min_le_right _ _)⟩ p.2
        ⟨hp.2.1, (hp.2.2.trans hemin).trans (min_le_right _ _)⟩]
  have h0 : _root_.Filter.Tendsto (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Filter.Tendsto.congr' hzero.symm tendsto_const_nhds
  exact tendsto_nhds_unique h h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_eq_zero_of_eventuallyEqual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_eq_zero_of_eventuallyEqual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_eq_zero_of_eventuallyEqual ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRayAngle_eq_zero_of_eventuallyEqual

theorem finite_horn_end_angle_of_monotone (H : FiniteHorn g) (d : ℝ) (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b)) :
    Nonempty (EndAngles H) := by
  have hself : ∀ a : EndRay H.endpoint, endRayAngle H.endpoint d a a = 0 :=
    endRayAngle_self H hd
  have hsymm : ∀ a b : EndRay H.endpoint, endRayAngle H.endpoint d a b =
      endRayAngle H.endpoint d b a := endRayAngle_comm H d
  have htri : ∀ a b c : EndRay H.endpoint, endRayAngle H.endpoint d a c ≤
      endRayAngle H.endpoint d a b + endRayAngle H.endpoint d b c :=
    endRayAngle_triangle H hd hmono
  let K : AngleKernel (EndRay H.endpoint) :=
    { angle := endRayAngle H.endpoint d
      nonneg := fun a b => (endRayAngle_mem_Icc H hd a b).1
      self := hself
      symm := hsymm
      triangle := htri }
  have hmonoField : ∀ a b : EndRay H.endpoint, ∃ d' : ℝ, 0 < d' ∧
      d' ≤ _root_.Min.min a.length b.length ∧ ∀ s s' t t', 0 < s → s ≤ s' → s' ≤ d' →
        0 < t → t ≤ t' → t' ≤ d' → endComparisonAngle a b s' t' ≤ endComparisonAngle a b s t := by
    intro a b
    refine ⟨min (endRayLength H.endpoint d a) (endRayLength H.endpoint d b),
      lt_min (by simpa only [endRayLength] using lt_min a.length_pos hd)
        (by simpa only [endRayLength] using lt_min b.length_pos hd),
      le_min ((min_le_left _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
    intro s s' t t' hs hss' hs'd ht htt' ht'd
    have hsI : s ∈ _root_.Set.Ioc (0 : ℝ) (endRayLength H.endpoint d a) :=
      ⟨hs, hss'.trans (hs'd.trans (min_le_left _ _))⟩
    have hs'I : s' ∈ _root_.Set.Ioc (0 : ℝ) (endRayLength H.endpoint d a) :=
      ⟨lt_of_lt_of_le hs hss', hs'd.trans (min_le_left _ _)⟩
    have htI : t ∈ _root_.Set.Ioc (0 : ℝ) (endRayLength H.endpoint d b) :=
      ⟨ht, htt'.trans (ht'd.trans (min_le_right _ _))⟩
    have ht'I : t' ∈ _root_.Set.Ioc (0 : ℝ) (endRayLength H.endpoint d b) :=
      ⟨lt_of_lt_of_le ht htt', ht'd.trans (min_le_right _ _)⟩
    have h₁ := (hmono a b).1 hsI hs'I htI hss'
    have h₂ := (hmono a b).2 hs'I htI ht'I htt'
    simpa only [radialComparisonAngle_endRay] using h₂.trans h₁
  have hevField : ∀ a b : EndRay H.endpoint, a.EventuallyEqual b →
      K.classOf a = K.classOf b := by
    intro a b hab
    exact Quotient.sound (endRayAngle_eq_zero_of_eventuallyEqual H hd hmono hab)
  let F : EndAngles H :=
    { angle := K.angle
      range := fun a b => endRayAngle_mem_Icc H hd a b
      limit := fun a b eta heta => endRayAngle_limit H hd hmono a b heta
      monotone := hmonoField
      self := hself
      symm := hsymm
      triangle := htri
      quotient := Quotient K.setoid
      metric := K.metricSpace
      classOf := K.classOf
      onto := K.classOf_surjective
      distance := fun a b => K.dist_mk a b
      eventual_eq := hevField }
  exact ⟨F⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_monotone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_monotone

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
