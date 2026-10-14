import Submission.DifferentialGeometry.Geometry.Neck.SpatialUnitBandReturn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M}
  (hK : IsCompact K) (heps : eps ≤ 1 / 156000) (p : ℕ → M)
  (neck : ∀ n, SpatialNeck g eps (p n))
  (hp : ∀ n, (neck n).map ((neck n).center, 3 / 2) ∈ K)
  (W : ℕ → Set M) (hW : Monotone W)

include hK heps hp hW in
theorem exists_spatial_neck_midpoint_mem_of_monotone
    (hband : ∀ n, (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆ W (n + 1)) :
    ∃ n, (neck n).map ((neck n).center, 3 / 2) ∈ W n := by
  obtain ⟨i, j, hij, hreturn⟩ :=
    exists_spatial_neck_unit_band_return_in_compact g hK heps p neck hp
  exact ⟨j, hW (Nat.succ_le_of_lt hij) (hband i hreturn)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_midpoint_mem_of_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_midpoint_mem_of_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_midpoint_mem_of_monotone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_midpoint_mem_of_monotone

include hK heps hp hW in
theorem not_forall_spatial_neck_unit_band_subset_sdiff :
    ¬ ∀ n, (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆ W (n + 1) \ W n := by
  intro hband
  obtain ⟨n, hn⟩ := exists_spatial_neck_midpoint_mem_of_monotone g hK heps p neck hp W hW
    (fun n x hx => (hband n hx).1)
  exact (hband n ⟨((neck n).center, 3 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩).2 hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_forall_spatial_neck_unit_band_subset_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_forall_spatial_neck_unit_band_subset_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_forall_spatial_neck_unit_band_subset_sdiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_forall_spatial_neck_unit_band_subset_sdiff

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
