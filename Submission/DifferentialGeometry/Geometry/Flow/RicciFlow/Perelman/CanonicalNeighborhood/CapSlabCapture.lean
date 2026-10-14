import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import Submission.DifferentialGeometry.Geometry.Neck.SpatialChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Boundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc t : ℝ} {p y : M} {U : Set M}

theorem SpatialNeck.image_slab_subset_cap_core_of_center_in_slab
    (nk : SpatialNeck (S.base.metric t) eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hy : nk.map (q, level) = y)
    (cap : LocalCap S epsc y t U)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z) :
    nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-4 : ℝ) 4) ⊆ interior cap.core.carrier := by
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
  have hscalar := nk.abs_scalar_ratio_sub_one_le
    (show (q, level) ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ from
      ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp hlevel).1, (abs_le.mp hlevel).2]⟩)
  rw [hy] at hscalar
  have hypos : 0 < S.scalar t y := by
    have hratio : 0 < metricScalarAt (S.base.metric t) y / metricScalarAt (S.base.metric t) p := by
      linarith [(abs_le.mp hscalar).1]
    exact (div_pos_iff.mp hratio).elim (fun h => h.1) (fun h => (nk.Q_pos.not_gt h.2).elim)
  have hQ : S.scalar t y ≤ 2 * metricScalarAt (S.base.metric t) p := by
    have hratio : metricScalarAt (S.base.metric t) y / metricScalarAt (S.base.metric t) p ≤ 2 := by
      linarith [(abs_le.mp hscalar).2]
    exact (div_le_iff₀ nk.Q_pos).mp hratio
  have hroot : Real.sqrt (S.scalar t y) ≤ 2 * Real.sqrt (metricScalarAt (S.base.metric t) p) := by
    nlinarith [Real.sq_sqrt hypos.le, Real.sq_sqrt nk.Q_pos.le,
      Real.sqrt_nonneg (S.scalar t y), Real.sqrt_nonneg (metricScalarAt (S.base.metric t) p)]
  have hepsroot : Real.sqrt (1 + eps) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + eps by linarith [nk.eps_pos]),
      Real.sqrt_nonneg (1 + eps)]
  let R := 20 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)
  have hRlt : R < 10000 / Real.sqrt (S.scalar t y) := by
    apply (div_lt_div_iff₀ (Real.sqrt_pos.mpr nk.Q_pos) (Real.sqrt_pos.mpr hypos)).mpr
    have hp := Real.sqrt_pos.mpr nk.Q_pos
    have hq := Real.sqrt_pos.mpr hypos
    have hprod := mul_le_mul hepsroot hroot (by positivity : 0 ≤ Real.sqrt (S.scalar t y))
      (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hybound := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 4) hlen
    ⟨(q, level), ⟨mem_univ _, abs_le.mp hlevel⟩, hy⟩
  have hcapture := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (S.base.metric t) cap.center_inside
    (r := ENNReal.ofReal (10000 / Real.sqrt (S.scalar t y)))
    (by
      intro z hz
      have hztube : z ∈ cap.tube := (cap.overlap_eq.symm ▸ hz).2
      exact (ENNReal.ofReal_le_ofReal (hdepth z hztube)).trans ENNReal.ofReal_toReal_le)
  rintro z ⟨w, hw, rfl⟩
  apply hcapture
  have hwbound := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 4) hlen
    ⟨w, hw, rfl⟩
  change riemannianEDistOf (S.base.metric t) p y ≤ _ at hybound
  change riemannianEDistOf (S.base.metric t) p (nk.map w) ≤ _ at hwbound
  have hyp : riemannianEDistOf (S.base.metric t) y p ≤
      ENNReal.ofReal ((4 + 6) * Real.sqrt (1 + eps) /
        Real.sqrt (metricScalarAt (S.base.metric t) p)) := by
    rw [riemannianEDistOf_comm]
    exact hybound
  have hdist := (riemannianEDistOf_triangle (S.base.metric t) y p (nk.map w)).trans
    (add_le_add hyp hwbound)
  have hsum : ENNReal.ofReal ((4 + 6) * Real.sqrt (1 + eps) /
      Real.sqrt (metricScalarAt (S.base.metric t) p)) +
      ENNReal.ofReal ((4 + 6) * Real.sqrt (1 + eps) /
      Real.sqrt (metricScalarAt (S.base.metric t) p)) = ENNReal.ofReal R := by
    have hn : 0 ≤ (4 + 6) * Real.sqrt (1 + eps) /
        Real.sqrt (metricScalarAt (S.base.metric t) p) :=
      div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    rw [← ENNReal.ofReal_add hn hn]
    congr 1
    dsimp only [R]
    ring
  exact (hdist.trans_eq hsum).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (div_pos (by norm_num) (Real.sqrt_pos.mpr hypos))).mpr hRlt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.image_slab_subset_cap_core_of_center_in_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.image_slab_subset_cap_core_of_center_in_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.image_slab_subset_cap_core_of_center_in_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.image_slab_subset_cap_core_of_center_in_slab

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
