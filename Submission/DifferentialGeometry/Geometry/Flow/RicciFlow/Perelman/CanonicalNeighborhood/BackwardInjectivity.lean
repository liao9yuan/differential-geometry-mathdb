import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_uniform_injectivity_of_metricNoncollapsed
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (P : PointedRiemannianManifold.{u, 0, 0} I3) (scales : Set ℝ),
        MetricComplete P → MetricNoncollapsed P kappa scales →
        ∀ (p : P.M) (r : ℝ), r ∈ scales → 0 < r →
          (∀ y ∈ riemannianBallOf P.metric p r,
            r ^ 4 * Tensor0SBundle.normSq0S P.metric y 4 (metricRm04At P.metric y) ≤ 1) →
          HasInjRadiusAt P p (iota * r) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hkappa
  refine ⟨iota, hiota, ?_⟩
  intro P scales hcomplete hnc p r hrs hr hcurv
  have hvol := hnc p r hrs hr hcurv
  have hvol' : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 P.M P.metric (riemannianBallOf P.metric p r) := by
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using hvol
  exact hasInjRadiusAt_of_expMap_injOn P p (mul_pos hiota hr)
    (hinj P.M P.metric ⟨hcomplete.complete⟩ p r hr hcurv hvol')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed

theorem exists_uniform_injectivity_of_metricNoncollapsed_curvature_bound
    {kappa K : ℝ} (hkappa : 0 < kappa) (hK : 0 ≤ K) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ P : PointedRiemannianManifold.{u, 0, 0} I3,
        MetricComplete P → MetricNoncollapsed P kappa (_root_.Set.Ioc 0 1) →
        (∀ x : P.M, Tensor0SBundle.normSq0S P.metric x 4 (metricRm04At P.metric x) ≤ K) →
        ∀ p : P.M, HasInjRadiusAt P p eta := by
  obtain ⟨iota, hiota, hinj⟩ := exists_uniform_injectivity_of_metricNoncollapsed.{u} hkappa
  let r : ℝ := _root_.Min.min 1 (1 / (K + 1))
  have hr : 0 < r := lt_min one_pos (one_div_pos.mpr (by linarith))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrK : r * (K + 1) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < K + 1)).mp (min_le_right _ _)
  have hrpow : r ^ 4 ≤ r := by
    have hr2 : r ^ 2 ≤ r := by nlinarith
    have hr4 : (r ^ 2) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg r]
  have hscale : r ^ 4 * K ≤ 1 := by
    calc
      r ^ 4 * K ≤ r * K := mul_le_mul_of_nonneg_right hrpow hK
      _ ≤ r * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.le
      _ ≤ 1 := hrK
  refine ⟨iota * r, mul_pos hiota hr, ?_⟩
  intro P hcomplete hnc hbound p
  exact hinj P (_root_.Set.Ioc 0 1) hcomplete hnc p r ⟨hr, hr1⟩ hr (fun y _ =>
    (mul_le_mul_of_nonneg_left (hbound y) (pow_nonneg hr.le 4)).trans hscale)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_injectivity_of_metricNoncollapsed_curvature_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
