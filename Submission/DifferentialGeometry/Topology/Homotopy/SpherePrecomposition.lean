import Submission.DifferentialGeometry.Topology.Homotopy.SphereNaturality
import Submission.DifferentialGeometry.Topology.Homotopy.CubePrecomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def freeSpherePrecompose (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) →
      ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  ZerothHomotopy.lift (fun g => ZerothHomotopy.mk (g.comp f))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (_root_.ContinuousMap.continuous_precomp f)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSpherePrecompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSpherePrecompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSpherePrecompose ``Submission.DifferentialGeometry.Topology.freeSpherePrecompose

@[simp] theorem freeSpherePrecompose_mk (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSpherePrecompose n f (ZerothHomotopy.mk g) = ZerothHomotopy.mk (g.comp f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSpherePrecompose_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSpherePrecompose_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSpherePrecompose_mk ``Submission.DifferentialGeometry.Topology.freeSpherePrecompose_mk

theorem freeSpherePrecompose_eq_of_homotopic (n : ℕ)
    {f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)}
    (h : f.Homotopic g) : freeSpherePrecompose (X := X) n f = freeSpherePrecompose n g := by
  funext a
  induction a using ZerothHomotopy.rec with
  | mk a =>
    apply Quotient.sound
    apply (homotopic_iff_joined _ _).mp
    exact (ContinuousMap.Homotopic.refl a).comp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSpherePrecompose_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSpherePrecompose_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSpherePrecompose_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.freeSpherePrecompose_eq_of_homotopic

def homotopyGroupSpherePrecompose [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    HomotopyGroup (Fin (n + 1)) X x → HomotopyGroup (Fin (n + 1)) X x :=
  fun a => (homotopyGroupFreeSphereEquiv n x).symm
    (freeSpherePrecompose n f (homotopyGroupToFreeSphere n x a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose

theorem homotopyGroupSpherePrecompose_eq_of_homotopic [SimplyConnectedSpace X] (n : ℕ) (x : X)
    {f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)} (h : f.Homotopic g) :
    homotopyGroupSpherePrecompose n x f = homotopyGroupSpherePrecompose n x g := by
  unfold homotopyGroupSpherePrecompose
  rw [freeSpherePrecompose_eq_of_homotopic n h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_of_homotopic

theorem homotopyGroupSpherePrecompose_one [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    homotopyGroupSpherePrecompose n x f 1 = 1 := by
  apply (homotopyGroupFreeSphereEquiv n x).injective
  change homotopyGroupFreeSphereEquiv n x ((homotopyGroupFreeSphereEquiv n x).symm _) = _
  rw [Equiv.apply_symm_apply]
  change freeSpherePrecompose n f (homotopyGroupToFreeSphere n x 1) =
    homotopyGroupToFreeSphere n x 1
  rw [homotopyGroupToFreeSphere_one, freeSpherePrecompose_mk]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_one ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_one

theorem homotopyGroupSpherePrecompose_id [SimplyConnectedSpace X] (n : ℕ) (x : X) :
    homotopyGroupSpherePrecompose n x (ContinuousMap.id _) = id := by
  funext a
  change (homotopyGroupFreeSphereEquiv n x).symm
    (freeSpherePrecompose n (ContinuousMap.id _) (homotopyGroupFreeSphereEquiv n x a)) = a
  have h : freeSpherePrecompose (X := X) n (ContinuousMap.id _) = id := by
    funext c
    induction c using ZerothHomotopy.rec with
    | mk c => rfl
  rw [h]
  exact (homotopyGroupFreeSphereEquiv n x).symm_apply_apply a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_id ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_id

end DifferentialGeometry.Topology

open scoped _root_.Topology _root_.unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def cubeSphereMap (n : ℕ) (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1)))) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  (genLoopSphereHomeomorph n (cubeSphereBasepoint n)
    ⟨(cubeSphereProjection n).comp r,
      fun v hv => cubeSphereProjection_boundary n (r v) (hr hv)⟩).val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereMap ``Submission.DifferentialGeometry.Topology.cubeSphereMap

@[simp] theorem cubeSphereMap_projection (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (v : I^(Fin (n + 1))) :
    cubeSphereMap n r hr (cubeSphereProjection n v) = cubeSphereProjection n (r v) :=
  genLoopSphereHomeomorph_projection n (cubeSphereBasepoint n) _ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereMap_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereMap_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereMap_projection ``Submission.DifferentialGeometry.Topology.cubeSphereMap_projection

@[simp] theorem cubeSphereMap_basepoint (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1)))) :
    cubeSphereMap n r hr (cubeSphereBasepoint n) = cubeSphereBasepoint n :=
  (genLoopSphereHomeomorph n (cubeSphereBasepoint n) _).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereMap_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereMap_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereMap_basepoint ``Submission.DifferentialGeometry.Topology.cubeSphereMap_basepoint

theorem genLoopSphereHomeomorph_precompose (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (x : X) (p : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n x (genLoopPrecompose r hr p)).val =
      (genLoopSphereHomeomorph n x p).val.comp (cubeSphereMap n r hr) := by
  ext z
  obtain ⟨v, rfl⟩ := cubeSphereProjection_surjective n z
  rw [ContinuousMap.comp_apply, cubeSphereMap_projection,
    genLoopSphereHomeomorph_projection, genLoopSphereHomeomorph_projection]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph_precompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph_precompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph_precompose ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph_precompose

theorem homotopyGroupSpherePrecompose_eq_cube [SimplyConnectedSpace X] (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (x : X) :
    homotopyGroupSpherePrecompose n x (cubeSphereMap n r hr) =
      homotopyGroupPrecompose r hr x := by
  funext a
  induction a using Quotient.inductionOn with
  | h p =>
    apply (homotopyGroupFreeSphereEquiv n x).injective
    change (homotopyGroupFreeSphereEquiv n x) ((homotopyGroupFreeSphereEquiv n x).symm _) = _
    rw [Equiv.apply_symm_apply]
    change ZerothHomotopy.mk _ = ZerothHomotopy.mk _
    exact congrArg ZerothHomotopy.mk (genLoopSphereHomeomorph_precompose n r hr x p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_cube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_cube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_cube ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_eq_cube

def homotopyGroupCubeSpherePrecomposeHom [SimplyConnectedSpace X] (n : ℕ)
    (i : Fin (n + 1)) (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (hu : ∀ v t, r (Function.update v i t) = Function.update (r v) i t)
    (x : X) : HomotopyGroup (Fin (n + 1)) X x →* HomotopyGroup (Fin (n + 1)) X x where
  toFun := homotopyGroupSpherePrecompose n x (cubeSphereMap n r hr)
  map_one' := homotopyGroupSpherePrecompose_one n x _
  map_mul' a b := by
    rw [homotopyGroupSpherePrecompose_eq_cube]
    exact (homotopyGroupPrecomposeHom i r hr hu x).map_mul a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupCubeSpherePrecomposeHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupCubeSpherePrecomposeHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupCubeSpherePrecomposeHom ``Submission.DifferentialGeometry.Topology.homotopyGroupCubeSpherePrecomposeHom

theorem homotopyGroupSpherePrecompose_mul_of_homotopic_cube
    [SimplyConnectedSpace X] (n : ℕ) (i : Fin (n + 1))
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (hu : ∀ v t, r (Function.update v i t) = Function.update (r v) i t)
    (x : X)
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)}
    (hf : f.Homotopic (cubeSphereMap n r hr))
    (a b : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupSpherePrecompose n x f (a * b) =
      homotopyGroupSpherePrecompose n x f a * homotopyGroupSpherePrecompose n x f b := by
  rw [homotopyGroupSpherePrecompose_eq_of_homotopic n x hf]
  exact (homotopyGroupCubeSpherePrecomposeHom n i r hr hu x).map_mul a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_cube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_cube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_cube ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_cube


theorem homotopyGroupSpherePrecompose_mul_of_homotopic_suspension
    [SimplyConnectedSpace X] (n : ℕ) (i : Fin (n + 1))
    (r : C(I^({j : Fin (n + 1) // j ≠ i}), I^({j : Fin (n + 1) // j ≠ i})))
    (hr : Set.MapsTo r (Cube.boundary {j : Fin (n + 1) // j ≠ i})
      (Cube.boundary {j : Fin (n + 1) // j ≠ i}))
    (x : X)
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)}
    (hf : f.Homotopic (cubeSphereMap n (Cube.suspensionAt i r)
      (Cube.suspensionAt_mapsTo_boundary i r hr)))
    (a b : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupSpherePrecompose n x f (a * b) =
      homotopyGroupSpherePrecompose n x f a * homotopyGroupSpherePrecompose n x f b :=
  homotopyGroupSpherePrecompose_mul_of_homotopic_cube n i (Cube.suspensionAt i r)
    (Cube.suspensionAt_mapsTo_boundary i r hr) (Cube.suspensionAt_update i r) x hf a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_suspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_suspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_suspension ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_mul_of_homotopic_suspension

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem freeSpherePrecompose_comp (n : ℕ)
    (f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    freeSpherePrecompose (X := X) n (g.comp f) =
      freeSpherePrecompose n f ∘ freeSpherePrecompose n g := by
  funext a
  induction a using ZerothHomotopy.rec with
  | mk a => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSpherePrecompose_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSpherePrecompose_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSpherePrecompose_comp ``Submission.DifferentialGeometry.Topology.freeSpherePrecompose_comp

theorem homotopyGroupSpherePrecompose_comp [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    homotopyGroupSpherePrecompose n x (g.comp f) =
      homotopyGroupSpherePrecompose n x f ∘ homotopyGroupSpherePrecompose n x g := by
  funext a
  unfold homotopyGroupSpherePrecompose
  change (homotopyGroupFreeSphereEquiv n x).symm _ =
    (homotopyGroupFreeSphereEquiv n x).symm
      (freeSpherePrecompose n f ((homotopyGroupFreeSphereEquiv n x)
        ((homotopyGroupFreeSphereEquiv n x).symm _)))
  rw [Equiv.apply_symm_apply, freeSpherePrecompose_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_comp ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_comp

theorem homotopyGroupSpherePrecompose_homotopyEquiv [SimplyConnectedSpace X]
    (n : ℕ) (x : X)
    (e : ContinuousMap.HomotopyEquiv
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    Function.Bijective (homotopyGroupSpherePrecompose n x e.toFun) := by
  let T := homotopyGroupSpherePrecompose n x e.toFun
  let S := homotopyGroupSpherePrecompose n x e.invFun
  have hleft : T ∘ S = id := by
    dsimp [T, S]
    rw [← homotopyGroupSpherePrecompose_comp,
      homotopyGroupSpherePrecompose_eq_of_homotopic n x e.left_inv,
      homotopyGroupSpherePrecompose_id]
  have hright : S ∘ T = id := by
    dsimp [T, S]
    rw [← homotopyGroupSpherePrecompose_comp,
      homotopyGroupSpherePrecompose_eq_of_homotopic n x e.right_inv,
      homotopyGroupSpherePrecompose_id]
  exact ⟨(show Function.LeftInverse S T from congrFun hright).injective,
    (show Function.RightInverse S T from congrFun hleft).surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_homotopyEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_homotopyEquiv

end DifferentialGeometry.Topology
