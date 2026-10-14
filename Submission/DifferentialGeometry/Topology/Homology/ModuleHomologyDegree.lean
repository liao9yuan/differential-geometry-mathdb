import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory

universe u v w

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R] {ι : Type w} {shape : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) shape}

theorem exists_moduleCycle_map_of_eq (φ : K ⟶ L) {n t : ι} (h : n = t)
    (z : LinearMap.ker (K.sc n).g.hom) :
    ∃ z' : LinearMap.ker (L.sc t).g.hom,
      z'.val = (L.XIsoOfEq h).hom (φ.f n z.val) ∧
      moduleHomologyClass (L.sc t) z' =
        _root_.CategoryTheory.eqToHom (congrArg (fun i => L.homology i) h)
          (HomologicalComplex.homologyMap φ n (moduleHomologyClass (K.sc n) z)) := by
  subst t
  refine ⟨moduleCycleMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) z, ?_, ?_⟩
  · rfl
  · exact (moduleHomologyClass_map ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) z).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_moduleCycle_map_of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_moduleCycle_map_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_moduleCycle_map_of_eq ``Submission.DifferentialGeometry.Topology.exists_moduleCycle_map_of_eq

end DifferentialGeometry.Topology
