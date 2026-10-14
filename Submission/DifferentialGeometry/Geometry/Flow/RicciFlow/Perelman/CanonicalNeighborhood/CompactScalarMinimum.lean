import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarMinimum
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem BackwardExtension.exists_scalar_le_one_of_compact
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    [CompactSpace L.space.M] {a : ℝ} {ha : a ≤ 0}
    (B : BackwardExtension L (RealTimeInterval.closed a 0 ha))
    {t : ℝ} (ht : t ∈ _root_.Set.Icc a 0) :
    ∃ x : L.space.M, B.solution.scalar t x ≤ 1 := by
  obtain ⟨x, hx⟩ := exists_scalar_le_at_earlier_time_of_compact B.solution B.isSolution ht.2
    (show _root_.Set.Icc t 0 ⊆ _root_.Set.Icc a 0 from fun _ hu => ⟨ht.1.trans hu.1, hu.2⟩)
    (show _root_.Set.Ioo t 0 ⊆ _root_.Set.Ioo a 0 from fun _ hu => ⟨ht.1.trans_lt hu.1, hu.2⟩)
    L.space.basepoint
  refine ⟨x, ?_⟩
  have hterminal : B.solution.scalar 0 L.space.basepoint = 1 := by
    change metricScalarAt (B.solution.base.metric 0) L.space.basepoint = 1
    rw [B.terminal]
    exact L.scalar_one
  simpa only [hterminal] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension.exists_scalar_le_one_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension.exists_scalar_le_one_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension.exists_scalar_le_one_of_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension.exists_scalar_le_one_of_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
