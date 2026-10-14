import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Connected.PathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem PointedRiemannianConvergenceMaps.path_connected_space_of_frequently_path_connected_targets
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (htarget : ∃ᶠ n in _root_.Filter.atTop, IsPathConnected (Φ.target n)) : PathConnectedSpace L.M := by
  apply pathConnectedSpace_iff_univ.mpr
  refine ⟨L.basepoint, _root_.Set.mem_univ _, ?_⟩
  intro x _
  obtain ⟨N, hN⟩ := Φ.source_subset (isCompact_singleton (x := x))
  obtain ⟨n, htn, hn⟩ := (htarget.and_eventually (_root_.Filter.eventually_ge_atTop N)).exists
  have hsource : IsPathConnected (Φ.source n) := by
    have hh := htn.image' (Φ.partialDiffeomorph n).symm.contMDiffOn_toFun.continuousOn
    have heq : (Φ.partialDiffeomorph n).symm '' Φ.target n = Φ.source n := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Φ.partialDiffeomorph n).map_target' hz
      · intro hy
        refine ⟨Φ.partialDiffeomorph n y, (Φ.partialDiffeomorph n).map_source' hy, ?_⟩
        exact (Φ.partialDiffeomorph n).left_inv hy
    rwa [heq] at hh
  exact (hsource.joinedIn L.basepoint (Φ.base_mem n) x
    (hN n hn (_root_.Set.mem_singleton x))).mono (_root_.Set.subset_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.path_connected_space_of_frequently_path_connected_targets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.path_connected_space_of_frequently_path_connected_targets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.path_connected_space_of_frequently_path_connected_targets ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.path_connected_space_of_frequently_path_connected_targets

end DifferentialGeometry.CheegerGromovCompactness
