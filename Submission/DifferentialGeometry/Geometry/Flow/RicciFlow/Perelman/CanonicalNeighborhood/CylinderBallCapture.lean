import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1

theorem CylinderReference.closedBall_subset_slab (C : CylinderReference)
    (p : Cylinder) {R : ℝ} (hR : 0 ≤ R) :
    riemannianClosedBallOf (C.metric 0) p R ⊆ _root_.Set.univ ×ˢ _root_.Set.Icc (p.2 - R) (p.2 + R) := by
  intro y hy
  have hheight : |p.2 - y.2| ≤ R :=
    (ENNReal.ofReal_le_ofReal_iff hR).mp ((C.height_edist_le p y).trans hy)
  have habs := abs_le.mp hheight
  exact ⟨mem_univ _, by constructor <;> linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.closedBall_subset_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.closedBall_subset_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.closedBall_subset_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.closedBall_subset_slab

theorem CylinderReference.isCompact_closedBall (C : CylinderReference)
    (p : Cylinder) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (riemannianClosedBallOf (C.metric 0) p R) := by
  have hslab : IsCompact (_root_.Set.univ ×ˢ _root_.Set.Icc (p.2 - R) (p.2 + R) : Set Cylinder) :=
    (isCompact_univ : IsCompact (_root_.Set.univ : Set (Sphere 2))).prod _root_.CompactIccSpace.isCompact_Icc
  exact hslab.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist (C.metric 0) p) continuous_const)
    (C.closedBall_subset_slab p hR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.isCompact_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.isCompact_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.isCompact_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.isCompact_closedBall

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem collar_ball_subset_image (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ U)
    (p : Sphere 2) :
    riemannianBallOf (g 0) (F (p, 0)) (R / 2) ⊆ F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) := by
  have hball : riemannianClosedBallOf (C.metric 0) (p, 0) R ⊆
      univ ×ˢ _root_.Set.Icc (-R) R := by
    simpa only [zero_sub, zero_add] using C.closedBall_subset_slab (p, 0) hR.le
  apply (ball_subset_image_of_metric_lower_crossModel (C.metric 0) (g 0) F (p, 0)
    (L := 2) hR (by norm_num) (C.isCompact_closedBall (p, 0) hR.le)
    (hball.trans (hslab.trans hsource)) ?_).trans (_root_.Set.image_mono hball)
  intro y hy v
  have hlower := (cmp.equivalence 0 hzero y (hslab (hball hy)) v).1
  rw [hmetric, cmp.pullback_eq 0 y (hslab (hball hy))] at hlower
  have hh := inner_self_nonneg (I := IC) (C.metric 0) y v
  have hg := inner_self_nonneg (I := I3) (g 0) (F y) (mfderiv IC I3 (F : Cylinder → M) y v)
  nlinarith [mul_nonneg (sub_nonneg.mpr heps) hh]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_ball_subset_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_ball_subset_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_ball_subset_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_ball_subset_image

theorem collar_isCompact_closedBall (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R r : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R) (hr : r < R / 2)
    (hsource : U ⊆ F.source) (hslab : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ U)
    (p : Sphere 2) :
    IsCompact (riemannianClosedBallOf (g 0) (F (p, 0)) r) := by
  have hcpt : IsCompact (F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R)) :=
    ((isCompact_univ : IsCompact (_root_.Set.univ : Set (Sphere 2))).prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hslab.trans hsource))
  apply hcpt.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist (g 0) (F (p, 0))) continuous_const)
  intro y hy
  apply collar_ball_subset_image C g F cmp hmetric heps hzero hR hsource hslab p
  exact lt_of_le_of_lt hy
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < R / 2)).mpr hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_isCompact_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_isCompact_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_isCompact_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_isCompact_closedBall

theorem collar_short_curve_stays (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ U)
    (p : Sphere 2) {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (_root_.Set.Icc a b))
    (hstart : gamma a = F (p, 0))
    (hlen : metricPathELength (g 0) gamma a b < ENNReal.ofReal (R / 2)) :
    ∀ s ∈ _root_.Set.Icc a b, gamma s ∈ F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) := by
  intro s hs
  apply collar_ball_subset_image C g F cmp hmetric heps hzero hR hsource hslab p
  have hdist := edistOf_le_metricPathELength (g 0) hs.1
    (hgamma.mono (_root_.Set.Icc_subset_Icc le_rfl hs.2))
  rw [hstart] at hdist
  exact (hdist.trans (metricPathELength_mono (g 0) gamma le_rfl hs.2)).trans_lt hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_short_curve_stays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_short_curve_stays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_short_curve_stays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_short_curve_stays

theorem collar_length_lower_of_leaves (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ U)
    (p : Sphere 2) {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (_root_.Set.Icc a b))
    (hstart : gamma a = F (p, 0))
    (hleave : ∃ s ∈ _root_.Set.Icc a b, gamma s ∉ F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R)) :
    ENNReal.ofReal (R / 2) ≤ metricPathELength (g 0) gamma a b := by
  apply le_of_not_gt
  intro hshort
  obtain ⟨s, hs, hnot⟩ := hleave
  exact hnot (collar_short_curve_stays C g F cmp hmetric heps hzero hR hsource hslab
    p hgamma hstart hshort s hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_length_lower_of_leaves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_length_lower_of_leaves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_length_lower_of_leaves ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_length_lower_of_leaves

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
