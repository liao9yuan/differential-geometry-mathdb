import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

theorem isIso_singularHomologyMap_of_homotopyEquiv
    {k : Type u} [Ring k] (R : ModuleCat.{u} k) {X Y : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map (TopCat.ofHom e.toFun)) := by
  let H := (_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj R
  refine ⟨⟨H.map (TopCat.ofHom e.invFun), ?_, ?_⟩⟩
  · rw [← Functor.map_comp]
    have h : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    exact (h.congr_homologyMap_singularChainComplexFunctor R n).trans (H.map_id X)
  · rw [← Functor.map_comp]
    have h : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    exact (h.congr_homologyMap_singularChainComplexFunctor R n).trans (H.map_id Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isIso_singularHomologyMap_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isIso_singularHomologyMap_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isIso_singularHomologyMap_of_homotopyEquiv ``Submission.DifferentialGeometry.Homology.isIso_singularHomologyMap_of_homotopyEquiv

end DifferentialGeometry.Homology
