import Submission.DifferentialGeometry.Topology.LoopSpace.ManifoldComponent
import Submission.DifferentialGeometry.Geometry.Metric.Restriction
import Submission.DifferentialGeometry.Geometry.Measure.Area.OpenTarget
import Submission.DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

omit [CompactSpace M] in
theorem spanningDiskCompetitor_open_inclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : TopologicalSpace.Opens M)
    {γ : freeLoop U} {u : C(closedDisk, U)}
    (hu : u ∈ spanningDiskCompetitors (g.restrictOpen U) γ) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp u ∈ spanningDiskCompetitors g
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) := by
  obtain ⟨ht, L, hL⟩ := hu
  refine ⟨?_, L, fun z w => (riemannianEDistOf_le_restrictOpen g U (u z) (u w)).trans (hL z w)⟩
  ext θ
  exact congrArg Subtype.val (congrArg (fun f : freeLoop U => f θ) ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskCompetitor_open_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskCompetitor_open_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskCompetitor_open_inclusion ``Submission.DifferentialGeometry.Geometry.spanningDiskCompetitor_open_inclusion



theorem spanningDiskCompetitors_nonempty_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {L : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * _root_.EDist.edist s t)
    (hnull : γ.Nullhomotopic) : (spanningDiskCompetitors g γ).Nonempty := by
  let U := loopComponentOpen E γ
  let γU : freeLoop U := loopInComponent γ
  have hγU (s t : loopCircle) :
      riemannianEDistOf (g.restrictOpen U) (γU s) (γU t) ≤ (L : ℝ≥0∞) * _root_.EDist.edist s t := by
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U (isClosed_loopComponentOpen E γ)]
    exact hγ s t
  obtain ⟨u, hu⟩ := spanningDiskCompetitors_nonempty (g.restrictOpen U) hγU
    (loopInComponent_nullhomotopic γ hnull)
  exact ⟨_, spanningDiskCompetitor_open_inclusion g U hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskCompetitors_nonempty_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskCompetitors_nonempty_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskCompetitors_nonempty_of_compact ``Submission.DifferentialGeometry.Geometry.spanningDiskCompetitors_nonempty_of_compact

end DifferentialGeometry.Geometry
