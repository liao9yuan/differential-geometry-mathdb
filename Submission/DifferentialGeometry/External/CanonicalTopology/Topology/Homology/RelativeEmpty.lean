import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBasis
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set

universe u

namespace DifferentialGeometry.Topology

private theorem integralSingularChainMap_empty_eq_zero
    (X : Type u) [TopologicalSpace X] :
    integralSingularChainMap (singularSubspaceInclusion (∅ : Set X)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hc : c = 0 := by
    apply (integralSingularChainRepr n (∅ : Set X)).injective
    ext σ
    exact ((integralSingularSimplexEquiv n (∅ : Set X) σ)
      ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex ℝ 0⟩).2.elim
  subst c
  exact map_zero _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_empty_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularChainMap_empty_eq_zero target :: scope.openDecls } }

private theorem integralAbsoluteToRelative_empty_bijective
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (integralAbsoluteToRelative n (∅ : Set X)) := by
  let π := (integralRelativeChainSequence (∅ : Set X)).g
  have hπ : _root_.CategoryTheory.IsIso π := by
    change _root_.CategoryTheory.IsIso (cokernel.π (integralSingularChainMap (singularSubspaceInclusion (∅ : Set X))))
    rw [integralSingularChainMap_empty_eq_zero]
    infer_instance
  have hi : _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap π n) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_empty_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralAbsoluteToRelative_empty_bijective target :: scope.openDecls } }

def integralAbsoluteToRelativeEmptyEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularHomology n X ≃ₗ[ℤ] integralRelativeHomology n (∅ : Set X) :=
  LinearEquiv.ofBijective (integralAbsoluteToRelative n (∅ : Set X))
    (integralAbsoluteToRelative_empty_bijective X n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv

theorem integralAbsoluteToRelativeEmptyEquiv_toLinearMap
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralAbsoluteToRelativeEmptyEquiv n X).toLinearMap =
      integralAbsoluteToRelative n (∅ : Set X) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv_toLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv_toLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv_toLinearMap ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelativeEmptyEquiv_toLinearMap

private theorem integralSingularCochainMap_empty_eq_zero
    (X : Type u) [TopologicalSpace X] :
    integralSingularCochainMap (singularSubspaceInclusion (∅ : Set X)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change integralSingularCochainPullback n (singularSubspaceInclusion (∅ : Set X)) = 0
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((integralSingularChainMap (singularSubspaceInclusion (∅ : Set X))).f n c) = 0
  rw [integralSingularChainMap_empty_eq_zero]
  exact map_zero φ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCochainMap_empty_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCochainMap_empty_eq_zero target :: scope.openDecls } }

private theorem integralRelativeToAbsoluteCohomology_empty_bijective
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (integralRelativeToAbsoluteCohomology n (∅ : Set X)) := by
  let ι := integralRelativeCochainInclusion (∅ : Set X)
  have hι : _root_.CategoryTheory.IsIso ι := by
    change _root_.CategoryTheory.IsIso (kernel.ι (integralSingularCochainMap (singularSubspaceInclusion (∅ : Set X))))
    rw [integralSingularCochainMap_empty_eq_zero]
    infer_instance
  have hi : _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap ι n) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology_empty_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology_empty_bijective target :: scope.openDecls } }

def integralRelativeToAbsoluteCohomologyEmptyEquiv
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralRelativeCohomology n (∅ : Set X) ≃ₗ[ℤ] integralSingularCohomology n X :=
  LinearEquiv.ofBijective (integralRelativeToAbsoluteCohomology n (∅ : Set X))
    (integralRelativeToAbsoluteCohomology_empty_bijective X n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv ``Submission.DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv

theorem integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralRelativeToAbsoluteCohomologyEmptyEquiv n X).toLinearMap =
      integralRelativeToAbsoluteCohomology n (∅ : Set X) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap ``Submission.DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap

end DifferentialGeometry.Topology

end
