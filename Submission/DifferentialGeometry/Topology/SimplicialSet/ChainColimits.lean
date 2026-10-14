import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.MonoCoprod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial
noncomputable section
universe u
namespace DifferentialGeometry.SSet
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


instance chainComplexFunctor_preservesColimits :
    PreservesColimitsOfSize.{u, u} ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R) where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change _root_.CategoryTheory.Limits.PreservesColimitsOfShape J
      ((_root_.CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj (_root_.Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R)
    infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.chainComplexFunctor_preservesColimits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.chainComplexFunctor_preservesColimits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.chainComplexFunctor_preservesColimits ``Submission.DifferentialGeometry.SSet.chainComplexFunctor_preservesColimits


instance chainComplexFunctor_preservesMonomorphisms :
    ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [_root_.SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [_root_.SSet, SimplicialObject.whiskering, _root_.CategoryTheory.SimplicialObject]
    infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.chainComplexFunctor_preservesMonomorphisms then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.chainComplexFunctor_preservesMonomorphisms"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.chainComplexFunctor_preservesMonomorphisms ``Submission.DifferentialGeometry.SSet.chainComplexFunctor_preservesMonomorphisms

end DifferentialGeometry.SSet
