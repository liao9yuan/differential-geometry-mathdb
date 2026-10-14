import Submission.DifferentialGeometry.Topology.MetricSpace.TotallyBounded
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleOrder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Completion

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

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Toponogov

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

variable {g : SmoothRiemannianMetric I3 W}

attribute [local instance] EndAngles.metric

structure ScaleDirectionNet (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) : Prop where
  net : ∀ eta > 0, ∃ A : Finset (EndRay H.endpoint), ∃ d > 0, ∀ b : EndRay H.endpoint,
    ∃ a ∈ A, ∀ s ∈ _root_.Set.Ioc (0 : ℝ) (_root_.Min.min d (_root_.Min.min b.length a.length)),
      _root_.Dist.dist (a.point s) (b.point s) < eta * s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleDirectionNet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleDirectionNet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleDirectionNet ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleDirectionNet

structure ScaleSeparatedEndRays (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) : Prop where
  separated : ∃ a b : EndRay H.endpoint, ∃ c > 0, ∃ d > 0,
    ∀ s ∈ _root_.Set.Ioc (0 : ℝ) (_root_.Min.min d (_root_.Min.min a.length b.length)),
      c * s ≤ _root_.Dist.dist (a.point s) (b.point s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleSeparatedEndRays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleSeparatedEndRays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleSeparatedEndRays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleSeparatedEndRays

structure SeparatedEndRays (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (angles : EndAngles H) : Prop where
  separated : ∃ a b : EndRay H.endpoint, ∃ beta > 0, ∃ d > 0,
    ∀ s ∈ _root_.Set.Ioc (0 : ℝ) (_root_.Min.min d (_root_.Min.min a.length b.length)), beta ≤ endComparisonAngle a b s s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SeparatedEndRays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SeparatedEndRays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SeparatedEndRays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SeparatedEndRays

theorem comparisonAngle_self_le_of_dist_le {s gamma D : ℝ} (hs : 0 < s) (hgamma : 0 < gamma)
    (hgamma1 : gamma ≤ 1) (hD0 : 0 ≤ D) (hD : D ≤ gamma / Real.pi * s) :
    comparisonAngle s s D ≤ gamma := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hquarter : 0 ≤ gamma / 4 := by positivity
  have hquarterpi : gamma / 4 ≤ Real.pi / 2 := by
    have := Real.pi_gt_three
    linarith
  have hsin := Real.mul_le_sin hquarter hquarterpi
  have hkey : gamma / Real.pi * s ≤ 2 * s * Real.sin (gamma / 4) := by
    have h2 : 2 * s * (2 / Real.pi * (gamma / 4)) ≤ 2 * s * Real.sin (gamma / 4) :=
      mul_le_mul_of_nonneg_left hsin (by positivity)
    have h3 : 2 * s * (2 / Real.pi * (gamma / 4)) = gamma / Real.pi * s := by
      field_simp
      ring
    rwa [h3] at h2
  have hD' : D ≤ 2 * s * Real.sin (gamma / 4) := hD.trans hkey
  have hsq : D ^ 2 ≤ 4 * s ^ 2 * Real.sin (gamma / 4) ^ 2 := by
    nlinarith [hD', hD0]
  have hcosid : Real.cos (gamma / 2) = 1 - 2 * Real.sin (gamma / 4) ^ 2 := by
    rw [show gamma / 2 = 2 * (gamma / 4) by ring, Real.cos_two_mul_eq_one_sub]
  have htheta0 : 0 ≤ gamma / 2 := by positivity
  have hthetapi : gamma / 2 ≤ Real.pi := by linarith
  have hhalf : comparisonAngle s s D ≤ gamma / 2 :=
    comparisonAngle_le_of_sq_le_cos (θ := gamma / 2) hs hs htheta0 hthetapi (by
      rw [hcosid]
      nlinarith)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_self_le_of_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_self_le_of_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_self_le_of_dist_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_self_le_of_dist_le

theorem quotient_totallyBounded_iff_finset_angle_net (H : FiniteHorn g) (angles : EndAngles H) :
    TotallyBounded (_root_.Set.univ : Set angles.quotient) ↔
      ∀ ε > 0, ∃ A : Finset (EndRay H.endpoint), ∀ b : EndRay H.endpoint,
        ∃ a ∈ A, angles.angle a b < ε := by
  classical
  rw [Metric.totallyBounded_univ_iff_finset_net]
  have honto : ∀ q : angles.quotient, ∃ a : EndRay H.endpoint, angles.classOf a = q :=
    fun q => angles.onto q
  choose rep hrep using honto
  constructor
  · intro h ε hε
    obtain ⟨t, ht⟩ := h ε hε
    refine ⟨t.image rep, fun b => ?_⟩
    obtain ⟨q, hqt, hqb⟩ := ht (angles.classOf b)
    refine ⟨rep q, Finset.mem_image_of_mem _ hqt, ?_⟩
    calc angles.angle (rep q) b
        = _root_.Dist.dist (angles.classOf (rep q)) (angles.classOf b) :=
          (angles.distance (rep q) b).symm
      _ = _root_.Dist.dist q (angles.classOf b) := by rw [hrep q]
      _ = _root_.Dist.dist (angles.classOf b) q := dist_comm _ _
      _ < ε := hqb
  · intro h ε hε
    obtain ⟨A, hA⟩ := h ε hε
    refine ⟨A.image angles.classOf, fun q => ?_⟩
    obtain ⟨b, rfl⟩ := angles.onto q
    obtain ⟨a, haA, hab⟩ := hA b
    exact ⟨angles.classOf a, Finset.mem_image_of_mem _ haA,
      calc _root_.Dist.dist (angles.classOf b) (angles.classOf a) = angles.angle a b := by
            rw [dist_comm, angles.distance a b]
        _ < ε := hab⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quotient_totallyBounded_iff_finset_angle_net then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quotient_totallyBounded_iff_finset_angle_net"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quotient_totallyBounded_iff_finset_angle_net ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quotient_totallyBounded_iff_finset_angle_net

theorem totallyBounded_quotient_of_scaleDirectionNet (H : FiniteHorn g) (angles : EndAngles H)
    (hnet : ScaleDirectionNet g H) :
    TotallyBounded (_root_.Set.univ : Set angles.quotient) := by
  classical
  rw [quotient_totallyBounded_iff_finset_angle_net H angles]
  intro eps heps
  have heta : 0 < _root_.Min.min (eps / 2) 1 := lt_min (by linarith) one_pos
  have heta1 : _root_.Min.min (eps / 2) 1 ≤ 1 := min_le_right _ _
  have hetaeps : _root_.Min.min (eps / 2) 1 ≤ eps / 2 := min_le_left _ _
  have hdel : 0 < _root_.Min.min (eps / 2) 1 / Real.pi := div_pos heta Real.pi_pos
  obtain ⟨A, d, hd, hA⟩ := hnet.net (_root_.Min.min (eps / 2) 1 / Real.pi) hdel
  refine ⟨A, fun b => ?_⟩
  obtain ⟨a, haA, ha⟩ := hA b
  obtain ⟨dl, hdlpos, hdlle, hdl⟩ := angles.limit a b (_root_.Min.min (eps / 2) 1) heta
  have hminpos : 0 < _root_.Min.min d dl := lt_min hd hdlpos
  have hspos : 0 < _root_.Min.min d dl / 2 := by linarith
  have hsd : _root_.Min.min d dl / 2 ≤ d := by have := min_le_left d dl; linarith
  have hsdl : _root_.Min.min d dl / 2 ≤ dl := by have := min_le_right d dl; linarith
  have hmem : _root_.Min.min d dl / 2 ∈ _root_.Set.Ioc (0 : ℝ) (_root_.Min.min d (_root_.Min.min b.length a.length)) :=
    ⟨hspos, le_min hsd (le_min (hsdl.trans (hdlle.trans (min_le_right _ _)))
      (hsdl.trans (hdlle.trans (min_le_left _ _))))⟩
  have hmemdl : _root_.Min.min d dl / 2 ∈ _root_.Set.Ioc (0 : ℝ) dl := ⟨hspos, hsdl⟩
  have hclose : _root_.Dist.dist (a.point (_root_.Min.min d dl / 2)) (b.point (_root_.Min.min d dl / 2)) <
      (_root_.Min.min (eps / 2) 1 / Real.pi) * (_root_.Min.min d dl / 2) := ha (_root_.Min.min d dl / 2) hmem
  have hcmp : endComparisonAngle a b (_root_.Min.min d dl / 2) (_root_.Min.min d dl / 2) ≤ _root_.Min.min (eps / 2) 1 :=
    comparisonAngle_self_le_of_dist_le hspos heta heta1 (dist_nonneg) hclose.le
  have hangle : angles.angle a b < _root_.Min.min (eps / 2) 1 + _root_.Min.min (eps / 2) 1 := by
    have h := (abs_lt.mp (hdl (_root_.Min.min d dl / 2) hmemdl (_root_.Min.min d dl / 2) hmemdl)).1
    linarith
  have h2m : _root_.Min.min (eps / 2) 1 + _root_.Min.min (eps / 2) 1 ≤ eps :=
    (add_le_add hetaeps hetaeps).trans_eq (by ring)
  exact ⟨a, haA, lt_of_lt_of_le hangle h2m⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_quotient_of_scaleDirectionNet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_quotient_of_scaleDirectionNet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_quotient_of_scaleDirectionNet ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_quotient_of_scaleDirectionNet

theorem separatedEndRays_of_scaleSeparated (H : FiniteHorn g) (angles : EndAngles H)
    (h : ScaleSeparatedEndRays g H) : SeparatedEndRays g H angles := by
  obtain ⟨a, b, c, hc, d, hd, hsep⟩ := h.separated
  have hgamma : 0 < _root_.Min.min c 2 := lt_min hc (by norm_num)
  have hgamma2 : _root_.Min.min c 2 ≤ 2 := min_le_right _ _
  have hbeta : 0 < Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2) := by
    rw [Real.arccos_pos]
    nlinarith [hgamma]
  have hbetapi : Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2) ≤ Real.pi := Real.arccos_le_pi _
  refine ⟨a, b, Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2), hbeta, d, hd, ?_⟩
  intro s hs
  have hslen : s ≤ _root_.Min.min a.length b.length := hs.2.trans (min_le_right _ _)
  have hsa : s ≤ a.length := hslen.trans (min_le_left _ _)
  have hsb : s ≤ b.length := hslen.trans (min_le_right _ _)
  have hms : _root_.Min.min c 2 * s ≤ _root_.Dist.dist (a.point s) (b.point s) :=
    (mul_le_mul_of_nonneg_right (min_le_left c 2) hs.1.le).trans (hsep s hs)
  have hD0 : 0 ≤ _root_.Dist.dist (a.point s) (b.point s) := dist_nonneg
  have hD2s : _root_.Dist.dist (a.point s) (b.point s) ≤ s + s := by
    have h := dist_triangle (a.point s : UniformSpace.Completion W) H.endpoint
      (b.point s : UniformSpace.Completion W)
    rw [UniformSpace.Completion.dist_eq, a.radial s ⟨hs.1, hsa⟩] at h
    rw [dist_comm H.endpoint (b.point s : UniformSpace.Completion W),
      b.radial s ⟨hs.1, hsb⟩] at h
    linarith
  have hcos : Real.cos (endComparisonAngle a b s s) ≤
      Real.cos (Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2)) := by
    change Real.cos (comparisonAngle s s (_root_.Dist.dist (a.point s) (b.point s))) ≤
      Real.cos (Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2))
    rw [Real.cos_arccos (by nlinarith [hgamma2])
      (by nlinarith [hgamma]), cos_comparisonAngle hs.1 hs.1 (by rw [sub_self, abs_zero]; exact hD0) hD2s]
    have hsq : ((_root_.Min.min c 2) * s) ^ 2 ≤ _root_.Dist.dist (a.point s) (b.point s) ^ 2 :=
      sq_le_sq' (by nlinarith [hD0, hms]) hms
    have hden : 0 < 2 * (s * s) := by nlinarith [hs.1]
    rw [comparisonCosine]
    rw [show 2 * s * s = 2 * (s * s) by ring]
    rw [div_le_iff₀ hden]
    nlinarith [hsq, hs.1, hgamma]
  by_contra hcon
  have hlt : endComparisonAngle a b s s < Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2) :=
    lt_of_not_ge hcon
  have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi
    (x := endComparisonAngle a b s s) (y := Real.arccos (1 - (_root_.Min.min c 2) ^ 2 / 2))
    (comparisonAngle_mem_Icc s s (_root_.Dist.dist (a.point s) (b.point s))).1 hbetapi hlt
  linarith [hcos, hmono]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_scaleSeparated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_scaleSeparated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_scaleSeparated ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_scaleSeparated

theorem exists_pos_angle_of_separatedEndRays (H : FiniteHorn g) (angles : EndAngles H)
    (hsep : SeparatedEndRays g H angles) :
    ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  obtain ⟨a, b, beta, hbeta, d, hd, hsep'⟩ := hsep.separated
  obtain ⟨d', hd'pos, hd'le, hd'⟩ := angles.limit a b (beta / 2) (half_pos hbeta)
  have hminpos : 0 < _root_.Min.min d d' := lt_min hd hd'pos
  have hspos : 0 < _root_.Min.min d d' / 2 := by linarith
  have hsd : _root_.Min.min d d' / 2 ≤ d := by have := min_le_left d d'; linarith
  have hsdd' : _root_.Min.min d d' / 2 ≤ d' := by have := min_le_right d d'; linarith
  have hmem : _root_.Min.min d d' / 2 ∈ _root_.Set.Ioc (0 : ℝ) (_root_.Min.min d (_root_.Min.min a.length b.length)) :=
    ⟨hspos, le_min hsd (le_min (hsdd'.trans (hd'le.trans (min_le_left _ _)))
      (hsdd'.trans (hd'le.trans (min_le_right _ _))))⟩
  have hmemd' : _root_.Min.min d d' / 2 ∈ _root_.Set.Ioc (0 : ℝ) d' := ⟨hspos, hsdd'⟩
  have hlow := hsep' (_root_.Min.min d d' / 2) hmem
  have hdist := (abs_lt.mp (hd' (_root_.Min.min d d' / 2) hmemd' (_root_.Min.min d d' / 2) hmemd')).2
  exact ⟨a, b, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_pos_angle_of_separatedEndRays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_pos_angle_of_separatedEndRays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_pos_angle_of_separatedEndRays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_pos_angle_of_separatedEndRays

theorem separatedEndRays_of_exists_pos_angle (H : FiniteHorn g) (angles : EndAngles H)
    (h : ∃ a b : EndRay H.endpoint, 0 < angles.angle a b) :
    SeparatedEndRays g H angles := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨dm, hdm, hdmle, hmono⟩ := angles.monotone a b
  obtain ⟨dl, hdl, hdlle, hlim⟩ := angles.limit a b (angles.angle a b / 2) (half_pos hab)
  have hdlmem : _root_.Min.min dm dl ∈ _root_.Set.Ioc (0 : ℝ) dl := ⟨lt_min hdm hdl, min_le_right _ _⟩
  have hlow : angles.angle a b / 2 < endComparisonAngle a b (_root_.Min.min dm dl) (_root_.Min.min dm dl) := by
    have h := (abs_lt.mp (hlim (_root_.Min.min dm dl) hdlmem (_root_.Min.min dm dl) hdlmem)).1
    linarith
  refine ⟨a, b, angles.angle a b / 2, half_pos hab, _root_.Min.min dm dl, lt_min hdm hdl, ?_⟩
  intro s hs
  have hsd : s ≤ _root_.Min.min dm dl := hs.2.trans (min_le_left _ _)
  have hslen : s ≤ _root_.Min.min a.length b.length := hs.2.trans (min_le_right _ _)
  have hsdm : s ≤ dm := hsd.trans (min_le_left _ _)
  have hdle : _root_.Min.min dm dl ≤ dm := min_le_left _ _
  have hmono' := hmono s (_root_.Min.min dm dl) s (_root_.Min.min dm dl) hs.1 hsd hdle hs.1 hsd hdle
  exact hlow.le.trans hmono'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_exists_pos_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_exists_pos_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_exists_pos_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_of_exists_pos_angle

theorem finite_horn_direction_compactness_of_inputs
    (hnet : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ScaleDirectionNet g H)
    (hsep : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H, SeparatedEndRays g H angles) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H, letI := angles.metric;
        TotallyBounded (Set.univ : Set angles.quotient) ∧
          CompactSpace (UniformSpace.Completion angles.quotient) ∧
          ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  obtain ⟨H₁, hH₁, hnet'⟩ := hnet
  obtain ⟨H₂, hH₂, hsep'⟩ := hsep
  refine ⟨max H₁ H₂, lt_max_of_lt_left hH₁, ?_⟩
  intro g H hdepth angles
  have hnet'' := hnet' g H ((le_max_left H₁ H₂).trans hdepth)
  have hsep'' := hsep' g H ((le_max_right H₁ H₂).trans hdepth) angles
  have htb := totallyBounded_quotient_of_scaleDirectionNet H angles hnet''
  exact ⟨htb, Metric.compactSpace_completion_of_totallyBounded htb,
    exists_pos_angle_of_separatedEndRays H angles hsep''⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_inputs

theorem separatedEndRays_iff_exists_pos_angle (H : FiniteHorn g) (angles : EndAngles H) :
    SeparatedEndRays g H angles ↔ ∃ a b : EndRay H.endpoint, 0 < angles.angle a b :=
  ⟨exists_pos_angle_of_separatedEndRays H angles, separatedEndRays_of_exists_pos_angle H angles⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_iff_exists_pos_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_iff_exists_pos_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_iff_exists_pos_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.separatedEndRays_iff_exists_pos_angle

theorem finite_horn_direction_compactness_of_geometric_inputs
    (hnet : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ScaleDirectionNet g H)
    (hsep : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ScaleSeparatedEndRays g H) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H, letI := angles.metric;
        TotallyBounded (Set.univ : Set angles.quotient) ∧
          CompactSpace (UniformSpace.Completion angles.quotient) ∧
          ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  obtain ⟨H₂, hH₂, hsep'⟩ := hsep
  exact finite_horn_direction_compactness_of_inputs hnet
    ⟨H₂, hH₂, fun g H hdepth angles => separatedEndRays_of_scaleSeparated H angles
      (hsep' g H hdepth)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_geometric_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_geometric_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_geometric_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness_of_geometric_inputs


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
