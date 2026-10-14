import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineCones
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Affine chain carriers inside the original singular complex -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Original affine chains with ordered vertices in A. -/
def affineSingularChainsIn (n : ℕ) (A : Set E) :
    Submodule ℤ ((integralSingularChains E).X n) :=
  Submodule.span ℤ {c | ∃ v : Fin (n + 1) → E,
    (∀ i, v i ∈ A) ∧ c = affineSingularChain n v}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChainsIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChainsIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChainsIn ``Submission.DifferentialGeometry.Topology.affineSingularChainsIn

/-- Every original affine generator with those vertices belongs to its carrier. -/
theorem affineSingularChain_mem (n : ℕ) (A : Set E) (v : Fin (n + 1) → E)
    (hv : ∀ i, v i ∈ A) : affineSingularChain n v ∈ affineSingularChainsIn n A :=
  Submodule.subset_span ⟨v, hv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChain_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChain_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChain_mem ``Submission.DifferentialGeometry.Topology.affineSingularChain_mem

/-- In a convex carrier, the original affine chain is an actual singular
chain carried by that same subspace. -/
theorem affineSingularChainsIn_le (n : ℕ) {A : Set E} (hA : Convex ℝ A) :
    affineSingularChainsIn n A ≤ integralSingularChainsIn n A := by
  apply Submodule.span_le.mpr
  rintro c ⟨v, hv, rfl⟩
  apply Submodule.subset_span
  refine ⟨affineSingularSimplex n v, ?_, rfl⟩
  rintro _ ⟨t, rfl⟩
  change integralSingularSimplexEquiv n E ((integralSingularSimplexEquiv n E).symm
    (affineSimplexMap v)) t ∈ A
  rw [Equiv.apply_symm_apply]
  exact (convexHull_min (range_subset_iff.mpr hv) hA) (affineSimplexMap_mem_convexHull v t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChainsIn_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChainsIn_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChainsIn_le ``Submission.DifferentialGeometry.Topology.affineSingularChainsIn_le

/-- The original boundary preserves the specified vertex carrier. -/
theorem affineSingularChainsIn_boundary (n : ℕ) (A : Set E)
    {c : (integralSingularChains E).X (n + 1)} (hc : c ∈ affineSingularChainsIn (n + 1) A) :
    (integralSingularChains E).d (n + 1) n c ∈ affineSingularChainsIn n A := by
  have h : affineSingularChainsIn (n + 1) A ≤
      Submodule.comap ((integralSingularChains E).d (n + 1) n).hom (affineSingularChainsIn n A) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change (integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v) ∈ affineSingularChainsIn n A
    rw [affineSingularChain_boundary]
    exact Submodule.sum_mem (affineSingularChainsIn n A) (fun i _ =>
      (affineSingularChainsIn n A).toAddSubgroup.zsmul_mem
        (affineSingularChain_mem n A (v ∘ i.succAbove) (fun j => hv _)) _)
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChainsIn_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChainsIn_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChainsIn_boundary ``Submission.DifferentialGeometry.Topology.affineSingularChainsIn_boundary

/-- Coning to a vertex in A preserves the SAME original affine carrier. -/
theorem affineSingularCone_mem (n : ℕ) {A : Set E} {a : E} (ha : a ∈ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    affineSingularCone n a c ∈ affineSingularChainsIn (n + 1) A := by
  have h : affineSingularChainsIn n A ≤
      Submodule.comap (affineSingularCone n a) (affineSingularChainsIn (n + 1) A) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change affineSingularCone n a (affineSingularChain n v) ∈ affineSingularChainsIn (n + 1) A
    rw [affineSingularCone_affine]
    exact affineSingularChain_mem (n + 1) A (Fin.cons a v) (Fin.cases ha hv)
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_mem ``Submission.DifferentialGeometry.Topology.affineSingularCone_mem

/-- The exact cone identity extends to every original affine chain in
positive degrees by linearity. -/
theorem affineSingularCone_boundary (n : ℕ) (a : E) (A : Set E)
    {c : (integralSingularChains E).X (n + 1)} (hc : c ∈ affineSingularChainsIn (n + 1) A) :
    (integralSingularChains E).d (n + 2) (n + 1) (affineSingularCone (n + 1) a c) =
      c - affineSingularCone n a ((integralSingularChains E).d (n + 1) n c) := by
  let F := ((integralSingularChains E).d (n + 2) (n + 1)).hom.comp (affineSingularCone (n + 1) a) -
    (LinearMap.id - (affineSingularCone n a).comp ((integralSingularChains E).d (n + 1) n).hom)
  have h : affineSingularChainsIn (n + 1) A ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, rfl⟩
    change F (affineSingularChain (n + 1) v) = 0
    exact sub_eq_zero.mpr (affineSingularCone_boundary_affine n a v)
  exact sub_eq_zero.mp (h hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_boundary ``Submission.DifferentialGeometry.Topology.affineSingularCone_boundary

end DifferentialGeometry.Topology
