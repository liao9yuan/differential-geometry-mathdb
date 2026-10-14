import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexEvaluation
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LiftedFaces

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Exact ordered-face compatibility for original simplex chain evaluation -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Evaluation of an original face is evaluation of the same original
simplex after its actual ordered barycentric face inclusion. -/
theorem singularSimplexEvaluation_face (n : ℕ) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) :
    singularSimplexEvaluation n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (singularSimplexEvaluation (n + 1) σ).comp (liftedSimplexBodyMap n (n + 1) i.succAbove) := by
  apply ContinuousMap.ext
  intro z
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexEvaluation_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexEvaluation_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexEvaluation_face ``Submission.DifferentialGeometry.Topology.singularSimplexEvaluation_face

/-- Pushing through an original face equals pushing its original carrier
image through the same simplex, in every chain degree. -/
theorem singularSimplexChainPush_face (n k : ℕ) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) (c : integralSingularChainsIn k (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush (n + 1) k σ
      (singularCarrierMap k ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) c) =
      singularSimplexChainPush n k ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) c := by
  unfold singularSimplexChainPush
  rw [LinearMap.comp_apply, integralSingularChainRestriction_map, LinearMap.comp_apply]
  have hmap : integralSingularChainMap
      (singularSimplexEvaluation n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)) =
        integralSingularChainMap (liftedSimplexBodyMap n (n + 1) i.succAbove) ≫
          integralSingularChainMap (singularSimplexEvaluation (n + 1) σ) := by
    rw [singularSimplexEvaluation_face, integralSingularChainMap_comp]
  exact (congrArg (fun h : integralSingularChains (liftedSimplexBody.{u} n) ⟶ integralSingularChains X =>
    h.f k (integralSingularChainRestriction k (liftedSimplexBody n) c)) hmap).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexChainPush_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexChainPush_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexChainPush_face ``Submission.DifferentialGeometry.Topology.singularSimplexChainPush_face

end DifferentialGeometry.Topology
