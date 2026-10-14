import Submission.DifferentialGeometry.Topology.Homology.Local.Generator
import Submission.DifferentialGeometry.Topology.LocalDegree.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology
universe u
section Maps
variable {E F : Type u} [PseudoMetricSpace E] [TopologicalSpace F] [Zero F]
  {f : E → F} {x : E} {R : ℝ} (hR : IsolatingRadius f x R)

private def isolatingBallMap : C(_root_.Metric.ball x R, F) :=
  ⟨fun y => f y, (hR.continuousOn.mono _root_.Metric.ball_subset_closedBall).domRestrict⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.isolatingBallMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.isolatingBallMap target :: scope.openDecls } }

private theorem isolatingBallMap_mapsTo :
    _root_.Set.MapsTo (isolatingBallMap hR) ({(⟨x,_root_.Metric.mem_ball_self hR.pos⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R))
      ({0}ᶜ : Set F) := by
  intro y hy
  exact hR.nonzero y (_root_.Metric.ball_subset_closedBall y.property) (fun he => hy (Subtype.ext he))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.isolatingBallMap_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.isolatingBallMap_mapsTo target :: scope.openDecls } }


def IsolatingRadius.relativeHomologyMap {k : Type u} [Ring k] (A : ModuleCat.{u} k) (n : ℕ) :
    relativeHomology (TopCat.of (_root_.Metric.ball x R))
      ({(⟨x,_root_.Metric.mem_ball_self hR.pos⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R)) A n ⟶
    relativeHomology (TopCat.of F) ({0}ᶜ : Set F) A n :=
  DifferentialGeometry.Homology.relativeHomologyMap A (X := TopCat.of (_root_.Metric.ball x R)) (Y := TopCat.of F)
    (TopCat.ofHom (isolatingBallMap hR)) (isolatingBallMap_mapsTo hR) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap


theorem IsolatingRadius.relativeHomologyMap_eq {k : Type u} [Ring k] (A : ModuleCat.{u} k) (n : ℕ) :
    hR.relativeHomologyMap A n =
      DifferentialGeometry.Homology.relativeHomologyMap A (X := TopCat.of (_root_.Metric.ball x R)) (Y := TopCat.of F)
        (s := ({(⟨x,_root_.Metric.mem_ball_self hR.pos⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R))) (t := ({0}ᶜ : Set F))
        (TopCat.ofHom (⟨fun y => f y,
          (hR.continuousOn.mono _root_.Metric.ball_subset_closedBall).domRestrict⟩ : C(_root_.Metric.ball x R,F)))
        (fun y hy => hR.nonzero y (_root_.Metric.ball_subset_closedBall y.property)
          (fun he => hy (Subtype.ext he))) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap_eq ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.relativeHomologyMap_eq
end Maps

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (hR : IsolatingRadius f x R)

private def isolatingBallSphereSection (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    C(EuclideanSphere d,
      ({(⟨x,_root_.Metric.mem_ball_self hR.pos⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R))) :=
  puncturedNeighborhoodSphereSection _ x (_root_.Metric.ball x R) (_root_.Metric.mem_ball_self hR.pos) hr
    (fun _ hy => (mem_sphere.mp hy).trans_lt hrR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.isolatingBallSphereSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.isolatingBallSphereSection target :: scope.openDecls } }

private theorem isolatingBallSphereMap_eq (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace ℝ (Fin (d + 1)))).toFun.comp
      ((relativeSubspaceMap (X := TopCat.of (_root_.Metric.ball x R))
        (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
        (TopCat.ofHom (isolatingBallMap hR)) (isolatingBallMap_mapsTo hR)).hom.comp
        (isolatingBallSphereSection hR r hr hrR)) =
      sphereMap f x R hR.continuousOn hR.nonzero ⟨r,hr,hrR.le⟩ := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rw [sphereMap_apply]
  exact puncturedSpaceSphereHomotopyEquiv_apply _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.isolatingBallSphereMap_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.isolatingBallSphereMap_eq target :: scope.openDecls } }

private theorem homologyMap_sphere_comparison (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (localBallSphereHomologyIso _ x R hR.pos (ModuleCat.of ℤ ℤ) d).inv ≫ hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) ≫
      (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom =
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (sphereMap f x R hR.continuousOn hR.nonzero ⟨r,hr,hrR.le⟩)) d := by
  let _ : ContractibleSpace (_root_.Metric.ball x R) := (convex_ball x R).contractibleSpace ⟨x,_root_.Metric.mem_ball_self hR.pos⟩
  dsimp only [localBallSphereHomologyIso, Iso.trans_inv,
    localEuclideanSphereHomologyIso, Iso.trans_hom]
  simp only [Category.assoc]
  have hS := puncturedNeighborhoodSphereHomologyIso_inv
    (EuclideanSpace ℝ (Fin (d + 1))) x (_root_.Metric.ball x R) (_root_.Metric.mem_ball_self hR.pos) _root_.Metric.isOpen_ball
    (ModuleCat.of ℤ ℤ) hr (fun y hy => (mem_sphere.mp hy).trans_lt hrR) d
  rw [hS]
  change reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
    (TopCat.ofHom (isolatingBallSphereSection hR r hr hrR)) d ≫ _ = _
  have hn := relativeReducedConnectingIso_naturality (ModuleCat.of ℤ ℤ)
    (X := TopCat.of (_root_.Metric.ball x R)) (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
    (TopCat.ofHom (isolatingBallMap hR)) (isolatingBallMap_mapsTo hR) d
  change _ = hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) ≫ _ at hn
  rw [← Category.assoc (hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)), ← hn, Category.assoc,
    Iso.inv_hom_id_assoc, reducedSingularHomologyIso_hom,
    ← reducedSingularHomologyMap_comp, ← reducedSingularHomologyMap_comp]
  exact congrArg (fun g => reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
    (TopCat.ofHom g) d) (isolatingBallSphereMap_eq hR r hr hrR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.homologyMap_sphere_comparison
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.homologyMap_sphere_comparison target :: scope.openDecls } }


theorem euclideanLocalDegree_relativeHomology :
    hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) (euclideanBallLocalGenerator x R hR.pos) =
      euclideanLocalDegree f x ⟨R,hR⟩ • euclideanLocalGenerator d := by
  apply (ModuleCat.mono_iff_injective
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom).mp inferInstance
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (homologyMap_sphere_comparison hR (R/2) (half_pos hR.pos) (by linarith [hR.pos]))
  change (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
    (hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) (euclideanBallLocalGenerator x R hR.pos)) = _ at he
  rw [he, euclideanLocalDegree_generator ⟨R,hR⟩ hR ⟨R/2,half_pos hR.pos,(by linarith [hR.pos])⟩]
  rw [map_zsmul]
  congr 1
  exact (congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_relativeHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_relativeHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_relativeHomology ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_relativeHomology
end DifferentialGeometry.LocalDegree
