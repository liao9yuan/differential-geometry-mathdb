import Submission.DifferentialGeometry.Topology.SimplicialSet.ChainColimits
import Submission.DifferentialGeometry.Topology.Homology.Algebra.PushoutExact
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
universe u
namespace DifferentialGeometry.SSet
variable {X : _root_.SSet.{u}} (A B : X.Subcomplex)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem unionChainSquare :
    _root_.CategoryTheory.IsPushout
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ B from inf_le_right)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) := by
  have sq : _root_.SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  exact ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_isPushout sq.isPushout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.unionChainSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.unionChainSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.unionChainSquare ``Submission.DifferentialGeometry.SSet.unionChainSquare


abbrev unionChainShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  DifferentialGeometry.ShortComplex.pushoutShortComplex (unionChainSquare A B R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.unionChainShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.unionChainShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.unionChainShortComplex ``Submission.DifferentialGeometry.SSet.unionChainShortComplex


theorem unionChainShortExact : (unionChainShortComplex A B R).ShortExact := by
  have : _root_.CategoryTheory.Mono (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) := by
    unfold _root_.SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.ShortComplex.pushoutShortExact (unionChainSquare A B R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.unionChainShortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.unionChainShortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.unionChainShortExact ``Submission.DifferentialGeometry.SSet.unionChainShortExact

def unionRelativeChainIso :
    _root_.CategoryTheory.Limits.cokernel (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) ≅
    _root_.CategoryTheory.Limits.cokernel (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) := by
  let sq := unionChainSquare A B R
  have := _root_.CategoryTheory.Limits.isIso_cokernel_map_of_isPushout sq
  exact _root_.CategoryTheory.asIso (cokernel.map _ _ _ _ sq.w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.unionRelativeChainIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.unionRelativeChainIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.unionRelativeChainIso ``Submission.DifferentialGeometry.SSet.unionRelativeChainIso


@[reassoc (attr := simp)]
theorem unionRelativeChainIso_projection :
    cokernel.π (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) ≫
        (unionRelativeChainIso A B R).hom =
      _root_.SSet.chainComplexMap
        (_root_.SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)) R ≫
      cokernel.π (_root_.SSet.chainComplexMap
        (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) :=
  cokernel.π_desc _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.unionRelativeChainIso_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.unionRelativeChainIso_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.unionRelativeChainIso_projection ``Submission.DifferentialGeometry.SSet.unionRelativeChainIso_projection

end DifferentialGeometry.SSet
