import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Integral singular homology on the pinned actual chain complex

The coefficient lift only places the integers in the space's universe.
The chains, differentials, homology and induced maps are Mathlib's singular
ones. No homology computation or Hurewicz/duality law is assumed.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- The integers, lifted only to match the universe of the singular simplices. -/
abbrev integralSingularCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCoefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCoefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCoefficients ``Submission.DifferentialGeometry.Topology.integralSingularCoefficients

/-- The actual integral singular chain complex, with its original alternating
face differential. -/
abbrev integralSingularChains (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).obj (TopCat.of X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChains ``Submission.DifferentialGeometry.Topology.integralSingularChains

/-- Actual integral singular homology, as a module over the integers. -/
abbrev integralSingularHomology (n : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℤ :=
  (integralSingularChains X).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology ``Submission.DifferentialGeometry.Topology.integralSingularHomology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The homology map induced by the original continuous target map. -/
def integralSingularHomologyMap (n : ℕ) (f : C(X, Y)) :
    integralSingularHomology n X →ₗ[ℤ] integralSingularHomology n Y :=
  (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map
    (TopCat.ofHom f)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap

/-- Identity on the actual space induces identity on its actual singular homology. -/
theorem integralSingularHomologyMap_id (n : ℕ) :
    integralSingularHomologyMap n (.id X) = LinearMap.id :=
  congrArg ModuleCat.Hom.hom
    (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map_id
      (TopCat.of X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_id ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_id

/-- The original composition law holds on the actual integral homology maps. -/
theorem integralSingularHomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap n (g.comp f) =
      (integralSingularHomologyMap n g).comp (integralSingularHomologyMap n f) :=
  congrArg ModuleCat.Hom.hom
    (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_comp ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_comp

/-- Homotopy invariance uses the original continuous homotopy and Mathlib's
proved singular chain homotopy, including the original parametrization. -/
theorem integralSingularHomologyMap_homotopic (n : ℕ) {f g : C(X, Y)} (h : f.Homotopic g) :
    integralSingularHomologyMap n f = integralSingularHomologyMap n g := by
  obtain ⟨H⟩ := h
  exact congrArg ModuleCat.Hom.hom
    (@TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (ModuleCat.{u} ℤ)
      _ _ _ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) (TopCat.ofHom g) _ H
        integralSingularCoefficients n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_homotopic ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_homotopic

/-- The original augmentation identifies H0 of every path-connected space
with the integers, without requiring a manifold hypothesis. -/
def integralSingularHomologyZeroEquiv [PathConnectedSpace X] :
    integralSingularHomology 0 X ≃ₗ[ℤ] ℤ :=
  (_root_.CategoryTheory.asIso ((TopCat.of X).singularHomology₀ε integralSingularCoefficients)).toLinearEquiv.trans
    ULift.moduleEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyZeroEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyZeroEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyZeroEquiv ``Submission.DifferentialGeometry.Topology.integralSingularHomologyZeroEquiv

end DifferentialGeometry.Topology
