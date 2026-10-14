import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineZeroCone

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Barycentric subdivision of the original affine singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual barycenter of the specified original ordered vertices. -/
def affineSimplexBarycenter (n : ℕ) (v : Fin (n + 1) → E) : E :=
  affineSimplexMap v stdSimplex.barycenter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexBarycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexBarycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexBarycenter ``Submission.DifferentialGeometry.Topology.affineSimplexBarycenter

/-- This barycenter lies in every convex carrier of the original vertices. -/
theorem affineSimplexBarycenter_mem (n : ℕ) (v : Fin (n + 1) → E)
    {A : Set E} (hA : Convex ℝ A) (hv : ∀ i, v i ∈ A) : affineSimplexBarycenter n v ∈ A :=
  convexHull_min (range_subset_iff.mpr hv) hA (affineSimplexMap_mem_convexHull v _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexBarycenter_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexBarycenter_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexBarycenter_mem ``Submission.DifferentialGeometry.Topology.affineSimplexBarycenter_mem

/-- Recursive barycentric subdivision: cone the subdivided original
boundary to the same simplex's actual barycenter. It acts on the original
chain groups and sends nonaffine basis simplices to zero in positive degrees. -/
def affineSingularSubdivision (n : ℕ) :
    (integralSingularChains E).X n →ₗ[ℤ] (integralSingularChains E).X n :=
  match n with
  | 0 => LinearMap.id
  | n + 1 => by
    classical
    exact (integralSingularChainBasis (n + 1) E).constr
      (M' := (integralSingularChains E).X (n + 1)) ℕ (fun σ =>
        if h : ∃ v, affineSingularSimplex (n + 1) v = σ then
          affineSingularCone n (affineSimplexBarycenter (n + 1) h.choose)
            (affineSingularSubdivision n ((integralSingularChains E).d (n + 1) n
              (integralSimplexChain (n + 1) σ))) else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSubdivision ``Submission.DifferentialGeometry.Topology.affineSingularSubdivision

/-- Degree-zero subdivision is the original identity. -/
theorem affineSingularSubdivision_zero (c : (integralSingularChains E).X 0) :
    affineSingularSubdivision 0 c = c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSubdivision_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSubdivision_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSubdivision_zero ``Submission.DifferentialGeometry.Topology.affineSingularSubdivision_zero

/-- The recursion on an affine generator uses its exact original vertices
and boundary, independently of the proof that it is affine. -/
theorem affineSingularSubdivision_succ (n : ℕ) (v : Fin (n + 2) → E) :
    affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v) =
      affineSingularCone n (affineSimplexBarycenter (n + 1) v)
        (affineSingularSubdivision n ((integralSingularChains E).d (n + 1) n
          (affineSingularChain (n + 1) v))) := by
  classical
  rw [affineSingularSubdivision]
  change ((integralSingularChainBasis (n + 1) E).constr
    (M' := (integralSingularChains E).X (n + 1)) ℕ _)
      (integralSimplexChain (n + 1) (affineSingularSimplex (n + 1) v)) = _
  rw [← integralSingularChainBasis_apply, Basis.constr_basis]
  let h : ∃ w, affineSingularSimplex (n + 1) w = affineSingularSimplex (n + 1) v := ⟨v, rfl⟩
  rw [dif_pos h, affineSingularSimplex_injective (n + 1) h.choose_spec]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSubdivision_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSubdivision_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSubdivision_succ ``Submission.DifferentialGeometry.Topology.affineSingularSubdivision_succ

/-- Subdivision preserves the same actual convex carrier in every degree. -/
theorem affineSingularSubdivision_mem (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    affineSingularSubdivision n c ∈ affineSingularChainsIn n A := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    have h : affineSingularChainsIn (n + 1) A ≤
        Submodule.comap (affineSingularSubdivision (n + 1)) (affineSingularChainsIn (n + 1) A) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v) ∈
        affineSingularChainsIn (n + 1) A
      rw [affineSingularSubdivision_succ]
      exact affineSingularCone_mem n (affineSimplexBarycenter_mem (n + 1) v hA hv)
        (ih (affineSingularChainsIn_boundary n A (affineSingularChain_mem (n + 1) A v hv)))
    exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSubdivision_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSubdivision_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSubdivision_mem ``Submission.DifferentialGeometry.Topology.affineSingularSubdivision_mem

end DifferentialGeometry.Topology
