import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineSimplex
import Mathlib.Data.Fin.Tuple.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Original affine chains and the ordered cone boundary -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered vertices determine their actual coefficient-one affine chain. -/
def affineSingularChain (n : ℕ) (v : Fin (n + 1) → E) : (integralSingularChains E).X n :=
  integralSimplexChain n (affineSingularSimplex n v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChain ``Submission.DifferentialGeometry.Topology.affineSingularChain

/-- The original alternating boundary deletes each ordered vertex. -/
theorem affineSingularChain_boundary (n : ℕ) (v : Fin (n + 2) → E) :
    (integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • affineSingularChain n (v ∘ i.succAbove) := by
  unfold affineSingularChain
  rw [integralSimplexChain_boundary]
  simp only [affineSingularSimplex_face]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChain_boundary ``Submission.DifferentialGeometry.Topology.affineSingularChain_boundary

/-- Distinct ordered vertex lists give distinct actual affine simplices. -/
theorem affineSingularSimplex_injective (n : ℕ) :
    Function.Injective (affineSingularSimplex (E := E) n) := by
  intro v w h
  have he := congrArg (integralSingularSimplexEquiv n E) h
  change integralSingularSimplexEquiv n E ((integralSingularSimplexEquiv n E).symm
    (affineSimplexMap v)) = integralSingularSimplexEquiv n E
      ((integralSingularSimplexEquiv n E).symm (affineSimplexMap w)) at he
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at he
  funext i
  simpa only [affineSimplexMap_vertex] using congrArg
    (fun F : C(stdSimplex ℝ (Fin (n + 1)), E) => F (stdSimplex.vertex i)) he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSimplex_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSimplex_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSimplex_injective ``Submission.DifferentialGeometry.Topology.affineSingularSimplex_injective

/-- The actual cone with a new first vertex has the original face as its
zeroth face and the negatively signed cones of the original remaining faces. -/
theorem affineSingularChain_cone_boundary (n : ℕ) (a : E) (v : Fin (n + 2) → E) :
    (integralSingularChains E).d (n + 2) (n + 1)
        (affineSingularChain (n + 2) (Fin.cons a v)) =
      affineSingularChain (n + 1) v -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          affineSingularChain (n + 1) (Fin.cons a (v ∘ i.succAbove)) := by
  rw [affineSingularChain_boundary, Fin.sum_univ_succ]
  have hzero : Fin.cons a v ∘ (0 : Fin (n + 3)).succAbove = v := by
    funext i
    simp
  rw [hzero]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    Fin.cons_comp_succ_succAbove, pow_succ, mul_neg_one]
  have hn (k : ℤ) (c : (integralSingularChains E).X (n + 1)) : (-k) • c = -(k • c) :=
    neg_zsmul c k
  simp only [hn]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularChain_cone_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularChain_cone_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularChain_cone_boundary ``Submission.DifferentialGeometry.Topology.affineSingularChain_cone_boundary

end DifferentialGeometry.Topology
