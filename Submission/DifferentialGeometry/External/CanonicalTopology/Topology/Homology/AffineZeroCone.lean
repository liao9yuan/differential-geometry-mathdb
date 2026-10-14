import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineCarriers
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Augmentation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The augmented degree-zero identity for the original affine cone -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original augmentation times the original vertex at a. -/
def affineSingularAugmentationChain (a : E) :
    (integralSingularChains E).X 0 →ₗ[ℤ] (integralSingularChains E).X 0 where
  toFun c := integralSingularAugmentation c • affineSingularChain 0 (fun _ => a)
  map_add' c d := by rw [map_add, add_zsmul]
  map_smul' k c := by
    have hε := integralSingularAugmentation.map_smul k c
    change integralSingularAugmentation _ = k * integralSingularAugmentation c at hε
    rw [hε]
    exact (mul_zsmul _ _ _).trans
      (int_smul_eq_zsmul ((integralSingularChains E).X 0).isModule k _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularAugmentationChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularAugmentationChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularAugmentationChain ``Submission.DifferentialGeometry.Topology.affineSingularAugmentationChain


/-- On each original vertex this is the same unit vertex at a. -/
theorem affineSingularAugmentationChain_affine (a : E) (v : Fin 1 → E) :
    affineSingularAugmentationChain a (affineSingularChain 0 v) =
      affineSingularChain 0 (fun _ => a) := by
  change integralSingularAugmentation (integralSimplexChain 0 (affineSingularSimplex 0 v)) •
    affineSingularChain 0 (fun _ => a) = _
  rw [integralSingularAugmentation_simplex, one_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularAugmentationChain_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularAugmentationChain_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularAugmentationChain_affine ``Submission.DifferentialGeometry.Topology.affineSingularAugmentationChain_affine

/-- The actual edge from a to the original vertex has boundary vertex minus a. -/
theorem affineSingularCone_boundary_zero_affine (a : E) (v : Fin 1 → E) :
    (integralSingularChains E).d 1 0 (affineSingularCone 0 a (affineSingularChain 0 v)) =
      affineSingularChain 0 v - affineSingularAugmentationChain a (affineSingularChain 0 v) := by
  rw [affineSingularAugmentationChain_affine, affineSingularCone_affine,
    affineSingularChain_boundary, Fin.sum_univ_two]
  have h0 : Fin.cons a v ∘ (0 : Fin 2).succAbove = v := by funext i; simp
  have h1 : Fin.cons a v ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => a := by
    funext i
    fin_cases i
    rfl
  rw [h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_boundary_zero_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_boundary_zero_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_boundary_zero_affine ``Submission.DifferentialGeometry.Topology.affineSingularCone_boundary_zero_affine

/-- The actual augmented cone identity on every affine zero-chain. -/
theorem affineSingularCone_boundary_zero (a : E) (A : Set E)
    {c : (integralSingularChains E).X 0} (hc : c ∈ affineSingularChainsIn 0 A) :
    (integralSingularChains E).d 1 0 (affineSingularCone 0 a c) =
      c - affineSingularAugmentationChain a c := by
  let F := ((integralSingularChains E).d 1 0).hom.comp (affineSingularCone 0 a) -
    (LinearMap.id - affineSingularAugmentationChain a)
  have h : affineSingularChainsIn 0 A ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, rfl⟩
    change F (affineSingularChain 0 v) = 0
    exact sub_eq_zero.mpr (affineSingularCone_boundary_zero_affine a v)
  exact sub_eq_zero.mp (h hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_boundary_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_boundary_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_boundary_zero ``Submission.DifferentialGeometry.Topology.affineSingularCone_boundary_zero

/-- An affine zero-chain of total coefficient zero bounds its same cone. -/
theorem affineSingularCone_bounds_zero (a : E) (A : Set E)
    {c : (integralSingularChains E).X 0} (hc : c ∈ affineSingularChainsIn 0 A)
    (hε : integralSingularAugmentation c = 0) :
    (integralSingularChains E).d 1 0 (affineSingularCone 0 a c) = c := by
  rw [affineSingularCone_boundary_zero a A hc]
  have h : affineSingularAugmentationChain a c = 0 := by
    change integralSingularAugmentation c • affineSingularChain 0 (fun _ => a) = 0
    rw [hε, zero_zsmul]
  rw [h, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularCone_bounds_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularCone_bounds_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularCone_bounds_zero ``Submission.DifferentialGeometry.Topology.affineSingularCone_bounds_zero

end DifferentialGeometry.Topology
