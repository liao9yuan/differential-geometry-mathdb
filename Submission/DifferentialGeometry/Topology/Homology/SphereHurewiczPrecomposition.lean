import Submission.DifferentialGeometry.Topology.Homology.SphereHurewicz
import Submission.DifferentialGeometry.Topology.Homology.SphereGenerator
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Submission.DifferentialGeometry.Topology.Homotopy.SpherePrecomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.ContinuousMap _root_.Metric
namespace DifferentialGeometry.Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def liftedHomotopySphereMap (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    C(liftedHomotopySphere.{u} n, liftedHomotopySphere.{u} n) where
  toFun z := ULift.up (f z.down)
  continuous_toFun := continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedHomotopySphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedHomotopySphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedHomotopySphereMap ``Submission.DifferentialGeometry.Topology.liftedHomotopySphereMap

omit [SimplyConnectedSpace X] in
private theorem freeSphereHomologyImage_precompose (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n (integralSingularHomologyMap (n + 1)
      (liftedHomotopySphereMap n f) c) a =
      freeSphereHomologyImage n c (freeSpherePrecompose n f a) := by
  induction a using ZerothHomotopy.rec with
  | mk g =>
      rw [freeSphereHomologyImage_mk, freeSpherePrecompose_mk,
        freeSphereHomologyImage_mk]
      have hcomp : (g.comp f).comp (liftedHomotopySphereDown n) =
          (g.comp (liftedHomotopySphereDown n)).comp (liftedHomotopySphereMap n f) := rfl
      rw [hcomp, integralSingularHomologyMap_comp]
      rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_precompose
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.freeSphereHomologyImage_precompose target :: scope.openDecls } }

private theorem homotopyGroupToFreeSphere_precompose (n : ℕ) (x : X)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n x
      (homotopyGroupSpherePrecompose n x f a) =
      freeSpherePrecompose n f (homotopyGroupToFreeSphere n x a) := by
  unfold homotopyGroupSpherePrecompose
  exact (homotopyGroupFreeSphereEquiv n x).apply_symm_apply _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_precompose
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_precompose target :: scope.openDecls } }

theorem sphereHurewicz_precompose (n : ℕ) (x : X)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n x (integralSingularHomologyMap (n + 1)
      (liftedHomotopySphereMap n f) c)
      a = sphereHurewicz n x c (homotopyGroupSpherePrecompose n x f a) := by
  unfold sphereHurewicz
  rw [Function.comp_apply, Function.comp_apply, homotopyGroupToFreeSphere_precompose,
    freeSphereHomologyImage_precompose]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_precompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_precompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_precompose ``Submission.DifferentialGeometry.Topology.sphereHurewicz_precompose

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology
universe u

private theorem isSphereHomologyGenerator_map_of_linearEquiv (n : ℕ)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (hc : IsSphereHomologyGenerator n c)
    (L : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) ≃ₗ[ℤ]
      integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHomologyGenerator n (L c) := by
  obtain ⟨e, he⟩ := hc
  refine ⟨L.symm.trans e, ?_⟩
  rw [LinearEquiv.trans_apply, L.symm_apply_apply, he]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_map_of_linearEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isSphereHomologyGenerator_map_of_linearEquiv target :: scope.openDecls } }

theorem isSphereHomologyGenerator_liftedHomotopySphereMap
    (n : ℕ)
    (e : ContinuousMap.HomotopyEquiv
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (hc : IsSphereHomologyGenerator n c) :
    IsSphereHomologyGenerator n
      (integralSingularHomologyMap (n + 1) (liftedHomotopySphereMap n e.toFun) c) := by
  let el : ContinuousMap.HomotopyEquiv
      (liftedHomotopySphere.{u} n) (liftedHomotopySphere.{u} n) :=
    Homeomorph.ulift.toHomotopyEquiv.trans
      (e.trans Homeomorph.ulift.symm.toHomotopyEquiv)
  exact isSphereHomologyGenerator_map_of_linearEquiv n hc
    (integralSingularHomologyHomotopyEquiv (n + 1) el)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_liftedHomotopySphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_liftedHomotopySphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_liftedHomotopySphereMap ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_liftedHomotopySphereMap

end DifferentialGeometry.Topology
