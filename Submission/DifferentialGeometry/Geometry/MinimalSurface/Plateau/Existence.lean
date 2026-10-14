import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.NoncompactMinimizer
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.AreaMinimality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission













noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]






theorem exists_morrey_disk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u := by
  obtain ⟨u, σ, hσ, _, _, _, htrace, hsmooth, hharm, hconf, henergy, heq⟩ :=
    exists_disk_energy_minimizer_of_homogeneously_regular g hcomplete hregular γ hγ hfinite
  exact ⟨u, isMorreyDisk_of_energy_attainment g hγ.smooth hγ.immersed
    hsmooth hconf hharm henergy ⟨σ, hσ, htrace⟩ heq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_morrey_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_morrey_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_morrey_disk ``Submission.DifferentialGeometry.Geometry.exists_morrey_disk




def selectedMorreyDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) : C(closedDisk, M) :=
  Classical.choose (exists_morrey_disk g hcomplete hregular γ hγ hfinite)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.selectedMorreyDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.selectedMorreyDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.selectedMorreyDisk ``Submission.DifferentialGeometry.Geometry.selectedMorreyDisk



theorem selectedMorreyDisk_isMorrey (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    IsMorreyDisk g γ (selectedMorreyDisk g hcomplete hregular γ hγ hfinite) :=
  Classical.choose_spec (exists_morrey_disk g hcomplete hregular γ hγ hfinite)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.selectedMorreyDisk_isMorrey then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.selectedMorreyDisk_isMorrey"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.selectedMorreyDisk_isMorrey ``Submission.DifferentialGeometry.Geometry.selectedMorreyDisk_isMorrey

end DifferentialGeometry.Geometry
