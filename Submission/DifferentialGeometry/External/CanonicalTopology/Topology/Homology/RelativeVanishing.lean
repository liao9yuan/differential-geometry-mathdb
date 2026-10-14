import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomology_univ_subsingleton
    {X : Type u} [TopologicalSpace X] (n : ℕ) :
    Subsingleton (integralRelativeHomology n (_root_.Set.univ : Set X)) := by
  let : _root_.CategoryTheory.IsIso (TopCat.ofHom (singularSubspaceInclusion (_root_.Set.univ : Set X))) :=
    inferInstanceAs (_root_.CategoryTheory.IsIso (TopCat.isoOfHomeo
      (X := TopCat.of (_root_.Set.univ : Set X)) (Y := TopCat.of X) (Homeomorph.Set.univ X)).hom)
  let : _root_.CategoryTheory.IsIso (integralSingularChainMap (singularSubspaceInclusion (_root_.Set.univ : Set X))) :=
    inferInstance
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).map_isZero
      (_root_.CategoryTheory.Limits.isZero_cokernel_of_epi (integralSingularChainMap (singularSubspaceInclusion (_root_.Set.univ : Set X)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomology_univ_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomology_univ_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomology_univ_subsingleton ``Submission.DifferentialGeometry.Topology.integralRelativeHomology_univ_subsingleton

end DifferentialGeometry.Topology

end
