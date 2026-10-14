import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Linear cones on actual affine singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cone an original simplex when it is affine. The ordered vertex list
is determined by that actual simplex; other basis elements are sent to zero. -/
def affineSingularConeBasis (n : ℕ) (a : E) (σ : integralSingularSimplex n E) :
    (integralSingularChains E).X (n + 1) := by
  classical
  exact if h : ∃ v, affineSingularSimplex n v = σ then
    affineSingularChain (n + 1) (Fin.cons a h.choose) else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularConeBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularConeBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularConeBasis ``Submission.DifferentialGeometry.Topology.affineSingularConeBasis

/-- On an affine simplex the cone uses its SAME original ordered vertices. -/
theorem affineSingularConeBasis_affine (n : ℕ) (a : E) (v : Fin (n + 1) → E) :
    affineSingularConeBasis n a (affineSingularSimplex n v) =
      affineSingularChain (n + 1) (Fin.cons a v) := by
  classical
  unfold affineSingularConeBasis
  let h : ∃ w, affineSingularSimplex n w = affineSingularSimplex n v := ⟨v, rfl⟩
  rw [dif_pos h, affineSingularSimplex_injective n h.choose_spec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularConeBasis_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularConeBasis_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularConeBasis_affine ``Submission.DifferentialGeometry.Topology.affineSingularConeBasis_affine

/-- Extend the actual affine cones linearly on the original singular basis. -/
def affineSingularCone (n : ℕ) (a : E) :
    (integralSingularChains E).X n →ₗ[ℤ] (integralSingularChains E).X (n + 1) :=
  (integralSingularChainBasis n E).constr (M' := (integralSingularChains E).X (n + 1)) ℕ
    (affineSingularConeBasis n a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone ``Submission.DifferentialGeometry.Topology.affineSingularCone

/-- The linear extension agrees exactly on every original affine generator. -/
theorem affineSingularCone_affine (n : ℕ) (a : E) (v : Fin (n + 1) → E) :
    affineSingularCone n a (affineSingularChain n v) =
      affineSingularChain (n + 1) (Fin.cons a v) := by
  change affineSingularCone n a (integralSimplexChain n (affineSingularSimplex n v)) = _
  rw [← integralSingularChainBasis_apply]
  exact ((integralSingularChainBasis n E).constr_basis ℕ _ (affineSingularSimplex n v)).trans
    (affineSingularConeBasis_affine n a v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_affine ``Submission.DifferentialGeometry.Topology.affineSingularCone_affine

/-- The cone identity on each original positive-dimensional affine generator. -/
theorem affineSingularCone_boundary_affine (n : ℕ) (a : E) (v : Fin (n + 2) → E) :
    (integralSingularChains E).d (n + 2) (n + 1)
      (affineSingularCone (n + 1) a (affineSingularChain (n + 1) v)) =
        affineSingularChain (n + 1) v - affineSingularCone n a
          ((integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v)) := by
  rw [affineSingularCone_affine, affineSingularChain_cone_boundary,
    affineSingularChain_boundary, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, affineSingularCone_affine]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_boundary_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_boundary_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_boundary_affine ``Submission.DifferentialGeometry.Topology.affineSingularCone_boundary_affine

end DifferentialGeometry.Topology
