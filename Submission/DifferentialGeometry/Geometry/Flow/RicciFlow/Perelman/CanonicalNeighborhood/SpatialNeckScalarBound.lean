import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckHighCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_spatialNeck_scalar_upper_bound :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧
      ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g →
        DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g →
        ∃ C : ℝ, ∀ (p : M) (eta : ℝ), eta ≤ eta₀ →
          SpatialNeck g eta p → metricScalarAt g p ≤ C := by
  obtain ⟨eta₀, heta₀, hconvert⟩ := exists_spatialNeckWitness_of_spatialNeck
    spatialNeckControlEpsilon_pos
  refine ⟨eta₀, heta₀, ?_⟩
  intro M _ _ _ _ _ _ g hg hsec
  classical
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let _ : T3Space M := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : MetricSpace M := riemMetricSpace (I := I3) (M := M)
  have hEnorm : IsMetricNorm (I := I3) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I3) g x v
  by_contra hbound
  have hlarge (n : ℕ) : ∃ (p : M) (eta : ℝ) (heta : eta ≤ eta₀)
      (nk : SpatialNeck g eta p), (n : ℝ) < metricScalarAt g p := by
    push Not at hbound
    obtain ⟨p, eta, heta, nk, hn⟩ := hbound n
    exact ⟨p, eta, heta, nk, hn⟩
  choose p eta heta nk hn using hlarge
  choose W _hW using fun n : ℕ => hconvert M g hg (p n) (eta n) (heta n) (nk n)
  have hdiverges : _root_.Filter.Tendsto (fun n => metricScalarAt g (p n)) _root_.Filter.atTop atTop :=
    tendsto_atTop_mono (fun n => (hn n).le) (tendsto_natCast_atTop_atTop (R := ℝ))
  exact not_tendsto_scalar_spatialNeck_centers_of_nonnegative W hEnorm le_rfl hsec hdiverges

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_scalar_upper_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_scalar_upper_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_scalar_upper_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_scalar_upper_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
