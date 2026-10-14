import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornAnnulusCompactness
import Submission.DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_isCompact_subradial_closedBall (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∀ R : ℝ, R < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint →
        IsCompact (Metric.closedBall x R) := by
  obtain ⟨delta, hdelta, htail⟩ := finiteHorn_ball_subset_subend g H 0
  refine ⟨delta / 4, by positivity, ?_⟩
  intro x hx R hR
  have ha : 0 < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint - R := sub_pos.mpr hR
  apply (finiteHorn_isCompact_radial_annulus g H 0 ha).of_isClosed_subset
    Metric.isClosed_closedBall
  intro y hy
  have hyx : _root_.Dist.dist y x ≤ R := hy
  have hxy : _root_.Dist.dist x y ≤ R := by simpa only [dist_comm] using hyx
  have hupper : _root_.Dist.dist (y : UniformSpace.Completion W) H.endpoint < delta := by
    have htri := dist_triangle (y : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq] at htri
    linarith
  refine ⟨subset_closure ⟨y, htail y hupper, rfl⟩, ?_⟩
  have htri := dist_triangle (x : UniformSpace.Completion W)
    (y : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq] at htri
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_isCompact_subradial_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_isCompact_subradial_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_isCompact_subradial_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_isCompact_subradial_closedBall

variable [SigmaCompactSpace W]

theorem finiteHorn_exists_subradial_minimizer (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∀ y : W, _root_.Dist.dist x y < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint →
      ∃ R : ℝ, _root_.Dist.dist x y < R ∧ R < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint ∧
        IsCompact (Metric.closedBall x R) ∧
        ∃ gamma : ℝ → W, gamma 0 = x ∧ gamma 1 = y ∧
          ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
          (∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, gamma s ∈ Metric.closedBall x R) ∧
          metricPathELength g gamma 0 1 = ENNReal.ofReal (_root_.Dist.dist x y) ∧
          ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ b ∈ _root_.Set.Icc (0 : ℝ) 1,
            metricPathELength g gamma a b =
              ENNReal.ofReal (b - a) * ENNReal.ofReal (_root_.Dist.dist x y) := by
  obtain ⟨d, hd, hcpt⟩ := finiteHorn_isCompact_subradial_closedBall g H
  refine ⟨d, hd, ?_⟩
  intro x hx y hxy
  let R : ℝ := (_root_.Dist.dist x y + _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint) / 2
  have hxyR : _root_.Dist.dist x y < R := by dsimp [R]; linarith
  have hR : R < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint := by dsimp [R]; linarith
  have hK := hcpt x hx R hR
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub, _, _⟩ :=
    Geometry.exists_smooth_geodesic_minimizer_of_isCompact_closedBall g
      (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm) hK hxyR
  exact ⟨R, hxyR, hR, hK, gamma, hstart, hend, hsmooth, hmem, hlength, hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_subradial_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_subradial_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_subradial_minimizer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_subradial_minimizer

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
