import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Submission.DifferentialGeometry.Geometry.Neck.SpatialRecentering
import Submission.DifferentialGeometry.Geometry.Neck.SpatialChart
import Submission.DifferentialGeometry.Geometry.Neck.SpatialTolerance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Metric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {p : M} {eps alpha a : ℝ}

theorem SpatialNeck.exists_at_coordinate_of_tolerance
    (nk : SpatialNeck g eps p) (hsmall : alpha < 1 / 11)
    (hreserve : 13000 * eps ≤ alpha) (u : Sphere 2)
    (hshift : |a| * eps ≤ 1 / 2) :
    ∃ out : SpatialNeck g alpha (nk.map (u, a)), out.center = u ∧
      out.map = partialDiffeomorphTransMixed
        (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
        nk.map := by
  have heps : eps < 1 := by linarith [nk.eps_small]
  have htwice : 2 * eps ≤ alpha := by linarith [nk.eps_pos]
  have halpha : 0 < alpha := lt_of_lt_of_le (mul_pos (by norm_num) nk.eps_pos) htwice
  have hratio : eps / alpha ≤ 1 / 2 :=
    (div_le_iff₀ halpha).mpr (by linarith)
  have hfit : |a| + alpha⁻¹ ≤ eps⁻¹ := by
    rw [inv_eq_one_div eps]
    apply (le_div_iff₀ nk.eps_pos).mpr
    calc
      (|a| + alpha⁻¹) * eps = |a| * eps + eps / alpha := by ring
      _ ≤ 1 := by linarith
  have habs : |a| < eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ nk.eps_pos).mpr
    linarith
  have hwindow : (u, a) ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _, abs_lt.mp habs⟩
  have hroot : Real.sqrt 3 ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hrootmul : (4323 * eps) * Real.sqrt 3 ≤ (4323 * eps) * 2 :=
    mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num) nk.eps_pos.le)
  have hsq : eps ^ 2 ≤ eps := by nlinarith [nk.eps_pos]
  have hbudget : (1 + 4323 * eps) * eps + (4323 * eps) * Real.sqrt 3 ≤ alpha := by
    nlinarith
  exact nk.exists_at_coordinate_of_scalar_close hsmall hbudget u hfit
    (nk.abs_scalar_ratio_sub_one_le hwindow)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_of_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_of_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_of_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_of_tolerance

theorem SpatialNeck.exists_at_coordinate
    (nk : SpatialNeck g eps p) (hsmall : alpha < 1 / 11)
    (hreserve : 13000 * eps ≤ alpha) (u : Sphere 2) (ha : |a| ≤ 4) :
    ∃ out : SpatialNeck g alpha (nk.map (u, a)), out.center = u ∧
      out.map = partialDiffeomorphTransMixed
        (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
        nk.map := by
  apply nk.exists_at_coordinate_of_tolerance hsmall hreserve u
  have hmul := mul_le_mul_of_nonneg_right ha nk.eps_pos.le
  linarith [nk.eps_small]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate

theorem SpatialNeck.exists_at_coordinate_mul
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 156000)
    (u : Sphere 2) (ha : |a| ≤ 4) :
    13000 * eps < 1 / 11 ∧
      ∃ out : SpatialNeck g (13000 * eps) (nk.map (u, a)), out.center = u ∧
        out.map = partialDiffeomorphTransMixed
          (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2)
            a 1 (by norm_num)).toPartialDiffeomorph
          nk.map := by
  have hsmall : 13000 * eps < 1 / 11 := by linarith
  exact ⟨hsmall, nk.exists_at_coordinate hsmall le_rfl u ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_at_coordinate_mul

omit [T2Space M] in
theorem SpatialNeck.translated_map_apply
    (nk : SpatialNeck g eps p) (u : Sphere 2)
    (out : SpatialNeck g alpha (nk.map (u, a)))
    (hmap : out.map = partialDiffeomorphTransMixed
      (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
      nk.map) (v : Sphere 2) (t : ℝ) :
    out.map (v, t) = nk.map (v, a + t) := by
  rw [hmap]
  change nk.map (v, a + 1 * t) = nk.map (v, a + t)
  rw [one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.translated_map_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.translated_map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.translated_map_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.translated_map_apply

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Filter
open scoped _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_spatial_neck_at_limit_of_tendsto_centers
    (g : SmoothRiemannianMetric I3 M) {ι : Type*} {l : Filter ι} [l.NeBot]
    {x : ι → M} {p : M} (hx : _root_.Filter.Tendsto x l (𝓝 p))
    {eps alpha : ℝ} (hsmall : alpha < 1 / 11) (hreserve : 13000 * eps ≤ alpha)
    (hnecks : ∀ᶠ n in l, Nonempty (SpatialNeck g eps (x n))) :
    Nonempty (SpatialNeck g alpha p) := by
  obtain ⟨n, hn⟩ := hnecks.exists
  obtain ⟨nk⟩ := hn
  have heps := nk.eps_pos
  have heps1 : eps < 1 := nk.eps_small.trans (by norm_num)
  let B := _root_.Max.max (metricScalarAt g p) 0 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [le_max_right (metricScalarAt g p) 0]
  have hRpB : metricScalarAt g p < B := by
    dsimp only [B]
    linarith [le_max_left (metricScalarAt g p) 0]
  have hscalar : ∀ᶠ n in l, metricScalarAt g (x n) < B :=
    ((metricScalar_smooth g).continuous.tendsto p |>.comp hx).eventually (Iio_mem_nhds hRpB)
  let r := Real.sqrt (1 - eps) / Real.sqrt B
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hB)
  have hdist : _root_.Filter.Tendsto (fun n => riemannianEDistOf g (x n) p) l (𝓝 0) := by
    have hc := (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g p).tendsto p
    have h := hc.comp hx
    change _root_.Filter.Tendsto (fun n => riemannianEDistOf g p (x n)) l (𝓝 (riemannianEDistOf g p p)) at h
    rw [riemannianEDistOf_self] at h
    exact h.congr' (Eventually.of_forall fun n => riemannianEDistOf_comm g p (x n))
  obtain ⟨n, ⟨nk⟩, hR, hd⟩ :=
    (hnecks.and (hscalar.and (hdist.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hr))))).exists
  have hroot := Real.sqrt_pos.mpr nk.Q_pos
  have hrad : r ≤ Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g (x n)) := by
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hroot
    exact Real.sqrt_le_sqrt hR.le
  have hnear : p ∈ riemannianBallOf g (x n)
      (1 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g (x n))) := by
    change riemannianEDistOf g (x n) p < ENNReal.ofReal
      (1 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g (x n)))
    simpa only [one_mul] using hd.trans_le (ENNReal.ofReal_le_ofReal hrad)
  obtain ⟨⟨q, a⟩, ha, hmap⟩ := nk.ball_subset_image_slab zero_lt_one
    ((one_lt_inv₀ heps).mpr heps1) hnear
  have hshift : |a| * eps ≤ 1 / 2 := by
    have hb : |a| ≤ 1 := abs_le.mpr ha.2
    have hm := mul_le_mul_of_nonneg_right hb heps.le
    linarith [nk.eps_small]
  obtain ⟨out, _, _⟩ := nk.exists_at_coordinate_of_tolerance hsmall hreserve q hshift
  exact hmap ▸ ⟨out⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_at_limit_of_tendsto_centers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_at_limit_of_tendsto_centers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_at_limit_of_tendsto_centers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_at_limit_of_tendsto_centers

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
