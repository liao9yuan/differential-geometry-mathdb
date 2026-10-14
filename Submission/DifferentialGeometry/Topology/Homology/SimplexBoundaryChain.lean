import Submission.DifferentialGeometry.Topology.Simplex.BoundaryGluing
import Submission.DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps
import Submission.DifferentialGeometry.Topology.Homology.LiftedSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def simplexBoundaryFace (n : ℕ) (i : Fin (n + 3)) :
    C(stdSimplex ℝ (Fin (n + 2)), ULift.{u} (Simplex.boundary (Fin (n + 3)))) :=
  ⟨fun p => ULift.up ⟨stdSimplex.map i.succAbove p,
    ⟨i, Simplex.map_succAbove_apply_pivot i p⟩⟩,
    continuous_uliftUp.comp ((stdSimplex.continuous_map i.succAbove).subtype_mk _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundaryFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundaryFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundaryFace ``Submission.DifferentialGeometry.Topology.simplexBoundaryFace

def simplexBoundaryChain (n : ℕ) :
    (integralSingularChains (ULift.{u} (Simplex.boundary (Fin (n + 3))))).X (n + 1) :=
  ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • integralSimplexChain (n + 1)
    ((integralSingularSimplexEquiv (n + 1) _).symm (simplexBoundaryFace n i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundaryChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundaryChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundaryChain ``Submission.DifferentialGeometry.Topology.simplexBoundaryChain

theorem integralSingularChainMap_boundaryDesc_simplexBoundaryChain (n : ℕ)
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p)) :
    (integralSingularChainMap
      ((Simplex.boundaryDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
      (simplexBoundaryChain.{u} n) =
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • integralSimplexChain (n + 1)
          ((integralSingularSimplexEquiv (n + 1) X).symm (f i)) := by
  rw [simplexBoundaryChain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralSimplexChain_map]
  congr 2
  apply (integralSingularSimplexEquiv (n + 1) X).injective
  rw [integralSingularSimplexMap_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext p
  exact Simplex.boundaryDesc_face f h i p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap_boundaryDesc_simplexBoundaryChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap_boundaryDesc_simplexBoundaryChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap_boundaryDesc_simplexBoundaryChain ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_boundaryDesc_simplexBoundaryChain

def simplexBoundarySphereMap (n : ℕ) :
    C(ULift.{u} (Simplex.boundary (Fin (n + 3))), liftedHomotopySphere.{u} n) :=
  ⟨fun p => ULift.up (Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm p.down),
    continuous_uliftUp.comp ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).continuous.comp continuous_uliftDown)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundarySphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundarySphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundarySphereMap ``Submission.DifferentialGeometry.Topology.simplexBoundarySphereMap

def simplexBoundarySphereChain (n : ℕ) :
    (integralSingularChains (liftedHomotopySphere.{u} n)).X (n + 1) :=
  (integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
    (simplexBoundaryChain n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundarySphereChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundarySphereChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundarySphereChain ``Submission.DifferentialGeometry.Topology.simplexBoundarySphereChain

theorem integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain (n : ℕ)
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p)) :
    (integralSingularChainMap
      ((Simplex.boundarySphereDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
      (simplexBoundarySphereChain.{u} n) =
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • integralSimplexChain (n + 1)
          ((integralSingularSimplexEquiv (n + 1) X).symm (f i)) := by
  let g : C(liftedHomotopySphere.{u} n, X) :=
    (Simplex.boundarySphereDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩
  have he : g.comp (simplexBoundarySphereMap n) =
      (Simplex.boundaryDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩ := by
    ext p
    change Simplex.boundaryDesc f h
      ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).symm
        (Simplex.stdSimplexNormedBoundarySphereHomeomorph
          (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm p.down)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have hc := congrArg (fun k => k.f (n + 1))
    (integralSingularChainMap_comp (simplexBoundarySphereMap n) g)
  change (integralSingularChainMap (g.comp (simplexBoundarySphereMap n))).f (n + 1) =
    (integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1) ≫
      (integralSingularChainMap g).f (n + 1) at hc
  change (integralSingularChainMap g).f (n + 1)
    ((integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
      (simplexBoundaryChain n)) = _
  rw [← ModuleCat.comp_apply, ← hc, he]
  exact integralSingularChainMap_boundaryDesc_simplexBoundaryChain n f h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

private def simplexBoundaryAmbientInclusion (n : ℕ) :
    C(ULift.{u} (Simplex.boundary (Fin (n + 3))),
      ULift.{u} (stdSimplex ℝ (Fin (n + 3)))) :=
  ⟨fun p => ULift.up p.down.val,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.simplexBoundaryAmbientInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.simplexBoundaryAmbientInclusion target :: scope.openDecls } }

private theorem simplexBoundaryAmbientInclusion_injective (n : ℕ) :
    Function.Injective (simplexBoundaryAmbientInclusion.{u} n) := by
  intro p q h
  exact ULift.ext _ _ (Subtype.ext (ULift.up_inj.mp h))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.simplexBoundaryAmbientInclusion_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.simplexBoundaryAmbientInclusion_injective target :: scope.openDecls } }

private theorem simplexBoundaryChain_inclusion (n : ℕ) :
    (integralSingularChainMap (simplexBoundaryAmbientInclusion n)).f (n + 1)
      (simplexBoundaryChain.{u} n) =
        (integralSingularChains (ULift.{u} (stdSimplex ℝ (Fin (n + 3))))).d (n + 2) (n + 1)
          (integralSimplexChain (n + 2)
            ((integralSingularSimplexEquiv (n + 2) _).symm
              ⟨ULift.up, continuous_uliftUp⟩)) := by
  rw [simplexBoundaryChain, map_sum, integralSimplexChain_boundary]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralSimplexChain_map]
  congr 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.simplexBoundaryChain_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.simplexBoundaryChain_inclusion target :: scope.openDecls } }

theorem simplexBoundaryChain_boundary (n : ℕ) :
    (integralSingularChains (ULift.{u} (Simplex.boundary (Fin (n + 3))))).d (n + 1) n
      (simplexBoundaryChain n) = 0 := by
  let j := simplexBoundaryAmbientInclusion.{u} n
  have : _root_.CategoryTheory.Mono (TopCat.ofHom j) :=
    (TopCat.mono_iff_injective _).mpr (simplexBoundaryAmbientInclusion_injective n)
  have : _root_.CategoryTheory.Mono (integralSingularChainMap j) := inferInstanceAs (_root_.CategoryTheory.Mono
    (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map
      (TopCat.ofHom j)))
  apply ((ModuleCat.mono_iff_injective ((integralSingularChainMap j).f n)).mp inferInstance)
  have hc := congrArg (fun k => k (simplexBoundaryChain.{u} n))
    ((integralSingularChainMap j).comm (n + 1) n)
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap j).f (n + 1) (simplexBoundaryChain.{u} n)) =
      (integralSingularChainMap j).f n ((integralSingularChains _).d (n + 1) n
        (simplexBoundaryChain.{u} n)) at hc
  rw [← hc, map_zero]
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap (simplexBoundaryAmbientInclusion n)).f (n + 1)
      (simplexBoundaryChain.{u} n)) = 0
  rw [simplexBoundaryChain_inclusion]
  exact congrArg (fun k => k (integralSimplexChain (n + 2)
    ((integralSingularSimplexEquiv (n + 2) _).symm ⟨ULift.up, continuous_uliftUp⟩)))
      ((integralSingularChains (ULift.{u} (stdSimplex ℝ (Fin (n + 3))))).d_comp_d
        (n + 2) (n + 1) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundaryChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundaryChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundaryChain_boundary ``Submission.DifferentialGeometry.Topology.simplexBoundaryChain_boundary

theorem simplexBoundarySphereChain_boundary (n : ℕ) :
    (integralSingularChains (liftedHomotopySphere.{u} n)).d (n + 1) n
      (simplexBoundarySphereChain n) = 0 := by
  have hc := congrArg (fun k => k (simplexBoundaryChain.{u} n))
    ((integralSingularChainMap (simplexBoundarySphereMap n)).comm (n + 1) n)
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
      (simplexBoundaryChain.{u} n)) =
      (integralSingularChainMap (simplexBoundarySphereMap n)).f n
        ((integralSingularChains _).d (n + 1) n (simplexBoundaryChain.{u} n)) at hc
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
      (simplexBoundaryChain.{u} n)) = 0
  rw [hc, simplexBoundaryChain_boundary, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundarySphereChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundarySphereChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundarySphereChain_boundary ``Submission.DifferentialGeometry.Topology.simplexBoundarySphereChain_boundary

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

def simplexBoundarySphereClass (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) :=
  integralSingularCycleClass n (liftedHomotopySphere.{u} n)
    ⟨simplexBoundarySphereChain n, simplexBoundarySphereChain_boundary n⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundarySphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundarySphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundarySphereClass ``Submission.DifferentialGeometry.Topology.simplexBoundarySphereClass

end DifferentialGeometry.Topology
