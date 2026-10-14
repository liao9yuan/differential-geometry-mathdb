import Submission.DifferentialGeometry.Topology.Homology.LiftedSphere
import Submission.DifferentialGeometry.Topology.Homotopy.SphereNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.ContinuousMap _root_.Metric

universe u

namespace DifferentialGeometry.Topology


def liftedHomotopySphereDown (n : ℕ) :
    C(liftedHomotopySphere.{u} n, _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  ⟨ULift.down, Homeomorph.ulift.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedHomotopySphereDown then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedHomotopySphereDown"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedHomotopySphereDown ``Submission.DifferentialGeometry.Topology.liftedHomotopySphereDown

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]



def freeSphereHomologyImage (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    ZerothHomotopy C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) →
      integralSingularHomology (n + 1) X :=
  ZerothHomotopy.lift (fun f => integralSingularHomologyMap (n + 1)
    (f.comp (liftedHomotopySphereDown n)) c) (fun {_ _} h =>
      LinearMap.congr_fun (integralSingularHomologyMap_homotopic (n + 1)
        (((homotopic_iff_joined _ _).mpr ⟨h⟩).comp (Homotopic.refl (liftedHomotopySphereDown n)))) c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage


theorem freeSphereHomologyImage_mk (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (f : C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n c (ZerothHomotopy.mk f) =
      integralSingularHomologyMap (n + 1) (f.comp (liftedHomotopySphereDown n)) c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage_mk ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_mk


theorem freeSphereHomologyImage_natural (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) (f : C(X, Y))
    (a : ZerothHomotopy C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n c (freeSpherePostcompose n f a) =
      integralSingularHomologyMap (n + 1) f (freeSphereHomologyImage n c a) := by
  induction a using ZerothHomotopy.rec with
  | mk g =>
      change integralSingularHomologyMap (n + 1)
        (f.comp (g.comp (liftedHomotopySphereDown n))) c = _
      rw [integralSingularHomologyMap_comp]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage_natural ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_natural


theorem freeSphereHomologyImage_zsmul (n : ℕ) (k : ℤ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : ZerothHomotopy C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n (k • c) a = k • freeSphereHomologyImage n c a := by
  induction a using ZerothHomotopy.rec with
  | mk f => simp only [freeSphereHomologyImage_mk, map_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage_zsmul ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_zsmul



def sphereHurewicz (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    HomotopyGroup (Fin (n + 1)) X x → integralSingularHomology (n + 1) X :=
  (freeSphereHomologyImage n c) ∘ (homotopyGroupToFreeSphere n x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz ``Submission.DifferentialGeometry.Topology.sphereHurewicz


theorem sphereHurewicz_mk (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (Γ : GenLoop (Fin (n + 1)) X x) :
    sphereHurewicz n x c ⟦Γ⟧ = integralSingularHomologyMap (n + 1)
      ((genLoopSphereHomeomorph n x Γ).val.comp (liftedHomotopySphereDown n)) c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_mk ``Submission.DifferentialGeometry.Topology.sphereHurewicz_mk


theorem sphereHurewicz_zsmul (n : ℕ) (k : ℤ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n x (k • c) a = k • sphereHurewicz n x c a :=
  freeSphereHomologyImage_zsmul n k c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_zsmul ``Submission.DifferentialGeometry.Topology.sphereHurewicz_zsmul


theorem sphereHurewicz_zero (n : ℕ) (x : X)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n x (0 : integralSingularHomology (n + 1)
      (liftedHomotopySphere.{u} n)) a = 0 := by
  rw [← zero_zsmul (0 : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)),
    sphereHurewicz_zsmul, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_zero ``Submission.DifferentialGeometry.Topology.sphereHurewicz_zero


theorem sphereHurewicz_one (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    sphereHurewicz n x c 1 = 0 := by
  unfold sphereHurewicz
  rw [Function.comp_apply, homotopyGroupToFreeSphere_one, freeSphereHomologyImage_mk]
  change integralSingularHomologyMap (n + 1) (ContinuousMap.const _ x) c = 0
  rw [integralSingularHomologyMap_const (n + 1) (by omega)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_one ``Submission.DifferentialGeometry.Topology.sphereHurewicz_one


theorem sphereHurewicz_transport (n : ℕ) {x y : X} (p : Path x y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n y c (homotopyGroupTransport n p a) = sphereHurewicz n x c a := by
  unfold sphereHurewicz
  rw [Function.comp_apply, homotopyGroupToFreeSphere_transport]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_transport ``Submission.DifferentialGeometry.Topology.sphereHurewicz_transport


theorem sphereHurewicz_natural (n : ℕ) (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n y c (homotopyGroupBasedMap f x y hf a) =
      integralSingularHomologyMap (n + 1) f (sphereHurewicz n x c a) := by
  unfold sphereHurewicz
  rw [Function.comp_apply, homotopyGroupToFreeSphere_natural, freeSphereHomologyImage_natural]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_natural ``Submission.DifferentialGeometry.Topology.sphereHurewicz_natural

end DifferentialGeometry.Topology
