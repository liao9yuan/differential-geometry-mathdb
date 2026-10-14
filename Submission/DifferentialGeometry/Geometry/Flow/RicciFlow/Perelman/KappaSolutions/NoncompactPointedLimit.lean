import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Compact
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem pointedLimit_noncompact_of_connected_noncompact_sources
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L phi)
    (hconnected : ∀ k : ℕ,
      @ConnectedSpace (X.obj (phi k)).M (X.obj (phi k)).topology)
    (hnoncompact : ∀ k : ℕ,
      @NoncompactSpace (X.obj (phi k)).M (X.obj (phi k)).topology) :
    @NoncompactSpace L.M L.topology := by
  let _ : TopologicalSpace L.M := L.topology
  constructor
  intro hcompact
  have hcompactSpace : CompactSpace L.M := ⟨hcompact⟩
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_globalizes Phi hcompactSpace hconnected
  obtain ⟨_, _, _, _, _, _, hsourceCompact⟩ := hk0 k0 le_rfl
  exact (hnoncompact k0).noncompact_univ hsourceCompact.isCompact_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_noncompact_of_connected_noncompact_sources then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_noncompact_of_connected_noncompact_sources"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_noncompact_of_connected_noncompact_sources ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_noncompact_of_connected_noncompact_sources

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

theorem backwardSliceLimit_noncompact
    (hconnected : @ConnectedSpace F.M F.topology)
    (hnoncompact : @NoncompactSpace F.M F.topology)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi) :
    @NoncompactSpace L.M L.topology :=
  pointedLimit_noncompact_of_connected_noncompact_sources Phi
    (fun _ => hconnected) (fun _ => hnoncompact)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_noncompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_noncompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_noncompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_noncompact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
