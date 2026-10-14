import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 t : ℝ} {p : M}

theorem CanonicalWitness.scalar_le_on_union_region
    (witness : CanonicalWitness S eps C1 C2 p t)
    {W V : Set M} (hV : V ⊆ W ∪ witness.domain.carrier) (hp : p ∈ W)
    {B : ℝ} (hB : ∀ x ∈ W, S.scalar t x ≤ B) :
    ∀ x ∈ V, S.scalar t x ≤ C2 * B := by
  have hC2 := witness.one_le_comparison_constant
  have hBpos : 0 < B := witness.Q_pos.trans_le (hB p hp)
  have hBmul : B ≤ C2 * B := le_mul_of_one_le_left hBpos.le hC2
  intro x hx
  rcases hV hx with hxW | hxV
  · exact (hB x hxW).trans hBmul
  · exact (witness.scalar_bounds x hxV).2.trans
      (mul_le_mul_of_nonneg_left (hB p hp) (zero_le_one.trans hC2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_on_union_region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_on_union_region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_on_union_region ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_on_union_region

theorem CanonicalWitness.scalar_le_sq_mul_at_mem_domain
    (witness : CanonicalWitness S eps C1 C2 p t) {anchor : M}
    (hanchor : anchor ∈ witness.domain.carrier) :
    ∀ x ∈ witness.domain.carrier, S.scalar t x ≤ C2 ^ 2 * S.scalar t anchor := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le witness.one_le_comparison_constant
  have hcenter : S.scalar t p ≤ C2 * S.scalar t anchor := by
    have h := mul_le_mul_of_nonneg_left (witness.scalar_bounds anchor hanchor).1 hC2.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] using h
  intro x hx
  have h := (witness.scalar_bounds x hx).2.trans (mul_le_mul_of_nonneg_left hcenter hC2.le)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_sq_mul_at_mem_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_sq_mul_at_mem_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_sq_mul_at_mem_domain ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_sq_mul_at_mem_domain

theorem CanonicalWitness.scalar_le_max_on_union_region_of_anchor
    (witness : CanonicalWitness S eps C1 C2 p t)
    {W V : Set M} (hV : V ⊆ W ∪ witness.domain.carrier)
    {anchor : M} (hanchor : anchor ∈ witness.domain.carrier)
    {B : ℝ} (hB : ∀ x ∈ W, S.scalar t x ≤ B) :
    ∀ x ∈ V, S.scalar t x ≤ _root_.Max.max B (C2 ^ 2 * S.scalar t anchor) := by
  intro x hx
  rcases hV hx with hxW | hxV
  · exact (hB x hxW).trans (le_max_left _ _)
  · exact (witness.scalar_le_sq_mul_at_mem_domain hanchor x hxV).trans (le_max_right _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_max_on_union_region_of_anchor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_max_on_union_region_of_anchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_max_on_union_region_of_anchor ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.scalar_le_max_on_union_region_of_anchor

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
