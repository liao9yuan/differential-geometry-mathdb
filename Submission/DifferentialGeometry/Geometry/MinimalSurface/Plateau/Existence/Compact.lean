import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.CompactMinimizer
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.AreaMinimality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_morrey_disk_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (weaklyMonotoneDiskCompetitors g γ).Nonempty) :
    ∃ q : C(closedDisk, M), IsMorreyDisk g γ q := by
  obtain ⟨q, τ, hτ, _, _, _, htrace, hsmooth, hharm, hconf, henergy, heq⟩ :=
    exists_disk_energy_minimizer_of_compact g γ hγ hfinite
  exact ⟨q, isMorreyDisk_of_energy_attainment g hγ.smooth hγ.immersed
    hsmooth hconf hharm henergy ⟨τ, hτ, htrace⟩ heq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_morrey_disk_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_morrey_disk_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_morrey_disk_of_compact ``Submission.DifferentialGeometry.Geometry.exists_morrey_disk_of_compact

end DifferentialGeometry.Geometry
