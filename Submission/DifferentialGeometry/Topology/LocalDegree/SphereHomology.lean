import Submission.DifferentialGeometry.Topology.Homology.Reduced.MayerVietoris
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Topology
noncomputable section
universe u
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : Metric.sphere (0 : E) 1)

private theorem poleComplement_cover : ∀ x : Metric.sphere (0 : E) 1,
    x ∈ (poleComplement v : Set (Metric.sphere (0 : E) 1)) ∨ x ∈ (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.poleComplement_cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.poleComplement_cover target :: scope.openDecls } }

def sphereEquatorReducedHomologyIso (n : ℕ) :
    reducedSingularHomology R (TopCat.of (Metric.sphere (0 : E) 1)) (n + 1) ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  exact reducedMayerVietorisConnectingIso R (TopCat.of (Metric.sphere (0 : E) 1))
      (poleComplement v : Set (Metric.sphere (0 : E) 1)) (poleComplement (-v) : Set (Metric.sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleComplement_cover v) n ≪≫
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso ``Submission.DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso

def sphereCoverToEquator :
    TopCat.of ↥((poleComplement v : Set (Metric.sphere (0 : E) 1)) ∩ (poleComplement (-v) : Set (Metric.sphere (0 : E) 1))) ⟶
      TopCat.of (EquatorialSphere v) :=
  TopCat.ofHom (poleIntersectionHomotopyEquiv v).toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereCoverToEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereCoverToEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereCoverToEquator ``Submission.DifferentialGeometry.LocalDegree.sphereCoverToEquator


@[simp]
theorem sphereCoverToEquator_apply (x : poleIntersection v) :
    sphereCoverToEquator v x = poleIntersectionHomotopyEquiv v x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereCoverToEquator_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereCoverToEquator_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereCoverToEquator_apply ``Submission.DifferentialGeometry.LocalDegree.sphereCoverToEquator_apply

@[reassoc (attr := simp)]
theorem small_inclusion_sphereEquatorReducedHomologyIso (n : ℕ) :
    HomologicalComplex.homologyMap
      (augmentedSmallChainMap R (TopCat.of (Metric.sphere (0 : E) 1))
        (twoSetFamily (TopCat.of (Metric.sphere (0 : E) 1))
          (poleComplement v : Set (Metric.sphere (0 : E) 1)) (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)))) (n + 2) ≫
      (sphereEquatorReducedHomologyIso R v n).hom =
    augmentedSmallConnectingMap R (TopCat.of (Metric.sphere (0 : E) 1))
        (poleComplement v : Set (Metric.sphere (0 : E) 1)) (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)) n ≫
      reducedSingularHomologyMap R (sphereCoverToEquator v) n := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, small_inclusion_reducedMayerVietorisConnectingIso]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.small_inclusion_sphereEquatorReducedHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.small_inclusion_sphereEquatorReducedHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.small_inclusion_sphereEquatorReducedHomologyIso ``Submission.DifferentialGeometry.LocalDegree.small_inclusion_sphereEquatorReducedHomologyIso

def euclideanSphereReducedHomologySuccIso {k : Type} [Ring k] (R : ModuleCat k)
    (d n : ℕ) :
    reducedSingularHomology R
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)) (n + 1) ≅
      reducedSingularHomology R
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) n := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) := ⟨by simp⟩
  exact sphereEquatorReducedHomologyIso R (euclideanNorth d) n ≪≫
    reducedSingularHomologyIso R (equatorialSphereHomeomorph d (euclideanNorth d)).toHomotopyEquiv n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso

theorem isZero_euclideanZeroSphere_reducedHomology_succ {k : Type} [Ring k]
    (R : ModuleCat k) (n : ℕ) :
    _root_.CategoryTheory.Limits.IsZero (reducedSingularHomology R
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) (n + 1)) :=
  IsZero.of_iso
    (isZero_reducedSingularHomology_of_isEmpty R
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 0)) 1)) n)
    (euclideanSphereReducedHomologySuccIso R 0 n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isZero_euclideanZeroSphere_reducedHomology_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isZero_euclideanZeroSphere_reducedHomology_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isZero_euclideanZeroSphere_reducedHomology_succ ``Submission.DifferentialGeometry.LocalDegree.isZero_euclideanZeroSphere_reducedHomology_succ

end DifferentialGeometry.LocalDegree
