import Submission.DifferentialGeometry.Topology.Homotopy.EquivUnder
import Mathlib.Topology.Homotopy.HomotopyGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Topology _root_.unitInterval

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X]

def genLoopPrecompose (r : C(I^N, I^N))
    (hr : Set.MapsTo r (Cube.boundary N) (Cube.boundary N))
    {x : X} (p : GenLoop N X x) : GenLoop N X x :=
  ⟨p.val.comp r, fun v hv => p.property (r v) (hr hv)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPrecompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPrecompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPrecompose ``Submission.DifferentialGeometry.Topology.genLoopPrecompose

theorem genLoopPrecompose_homotopic (r : C(I^N, I^N))
    (hr : Set.MapsTo r (Cube.boundary N) (Cube.boundary N))
    {x : X} {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopPrecompose r hr p) (genLoopPrecompose r hr q) := by
  obtain ⟨H⟩ := h
  exact ⟨Homotopy.HomotopyEquivUnder.precompHomotopyRel H r hr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPrecompose_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPrecompose_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPrecompose_homotopic ``Submission.DifferentialGeometry.Topology.genLoopPrecompose_homotopic

def homotopyGroupPrecompose (r : C(I^N, I^N))
    (hr : Set.MapsTo r (Cube.boundary N) (Cube.boundary N))
    (x : X) : HomotopyGroup N X x → HomotopyGroup N X x :=
  Quotient.map (genLoopPrecompose r hr) (fun _ _ h => genLoopPrecompose_homotopic r hr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupPrecompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupPrecompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupPrecompose ``Submission.DifferentialGeometry.Topology.homotopyGroupPrecompose

@[simp] theorem homotopyGroupPrecompose_mk (r : C(I^N, I^N))
    (hr : Set.MapsTo r (Cube.boundary N) (Cube.boundary N))
    (x : X) (p : GenLoop N X x) :
    homotopyGroupPrecompose r hr x ⟦p⟧ = ⟦genLoopPrecompose r hr p⟧ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupPrecompose_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupPrecompose_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupPrecompose_mk ``Submission.DifferentialGeometry.Topology.homotopyGroupPrecompose_mk

theorem genLoopPrecompose_transAt [DecidableEq N] (i : N)
    (r : C(I^N, I^N)) (hr : Set.MapsTo r (Cube.boundary N) (Cube.boundary N))
    (hu : ∀ v t, r (Function.update v i t) = Function.update (r v) i t)
    {x : X} (p q : GenLoop N X x) :
    genLoopPrecompose r hr (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopPrecompose r hr p) (genLoopPrecompose r hr q) := by
  have hi (v : I^N) : r v i = v i := by
    have h := congrArg (fun w => w i) (hu v (v i))
    simpa only [Function.update_eq_self, Function.update_self] using h
  ext v
  change GenLoop.transAt i p q (r v) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy, hi]
  split_ifs
  · change p _ = p (r _)
    rw [hu]
  · change q _ = q (r _)
    rw [hu]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPrecompose_transAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPrecompose_transAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPrecompose_transAt ``Submission.DifferentialGeometry.Topology.genLoopPrecompose_transAt

def homotopyGroupPrecomposeHom [DecidableEq N] [Nonempty N] (i : N)
    (r : C(I^N, I^N)) (hr : Set.MapsTo r (Cube.boundary N) (Cube.boundary N))
    (hu : ∀ v t, r (Function.update v i t) = Function.update (r v) i t)
    (x : X) : HomotopyGroup N X x →* HomotopyGroup N X x where
  toFun := homotopyGroupPrecompose r hr x
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        have hmul := congrArg (homotopyGroupPrecompose r hr x)
          (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        exact (congrArg (fun v : GenLoop N X x => (⟦v⟧ : HomotopyGroup N X x))
          (genLoopPrecompose_transAt i r hr hu q p)).trans
          (HomotopyGroup.mul_spec (i := i)
            (p := genLoopPrecompose r hr p) (q := genLoopPrecompose r hr q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupPrecomposeHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupPrecomposeHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupPrecomposeHom ``Submission.DifferentialGeometry.Topology.homotopyGroupPrecomposeHom

end DifferentialGeometry.Topology

namespace Cube
open _root_.Cube

variable {N : Type*} [DecidableEq N]

open _root_.Cube in
def suspensionAt (i : N)
    (r : C(I^({j : N // j ≠ i}), I^({j : N // j ≠ i}))) : C(I^N, I^N) :=
  (⟨Cube.insertAt i, (Cube.insertAt i).continuous⟩ : C(_, _)).comp
    (((ContinuousMap.id unitInterval).prodMap r).comp ⟨Cube.splitAt i, (Cube.splitAt i).continuous⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Cube.suspensionAt then
    throwError "Refusing to shadow existing declaration Cube.suspensionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Cube.suspensionAt ``Submission.Cube.suspensionAt

open _root_.Cube in
@[simp] theorem suspensionAt_apply_pivot (i : N)
    (r : C(I^({j : N // j ≠ i}), I^({j : N // j ≠ i}))) (v : I^N) :
    suspensionAt i r v i = v i := by
  simp [suspensionAt, Homeomorph.funSplitAt_apply, Homeomorph.funSplitAt_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Cube.suspensionAt_apply_pivot then
    throwError "Refusing to shadow existing declaration Cube.suspensionAt_apply_pivot"
  Lean.modifyEnv fun env => Lean.addAlias env `Cube.suspensionAt_apply_pivot ``Submission.Cube.suspensionAt_apply_pivot

open _root_.Cube in
theorem suspensionAt_update (i : N)
    (r : C(I^({j : N // j ≠ i}), I^({j : N // j ≠ i}))) (v : I^N) (t : unitInterval) :
    suspensionAt i r (Function.update v i t) = Function.update (suspensionAt i r v) i t := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp only [suspensionAt, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_mk, Homeomorph.funSplitAt_apply,
      Homeomorph.funSplitAt_symm_apply, dif_neg hj, Function.update_of_ne hj]
    have hrestrict : (fun k : {j : N // j ≠ i} => Function.update v i t k) =
        (fun k : {j : N // j ≠ i} => v k) :=
      funext (fun k => Function.update_of_ne k.property t v)
    rw [hrestrict]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Cube.suspensionAt_update then
    throwError "Refusing to shadow existing declaration Cube.suspensionAt_update"
  Lean.modifyEnv fun env => Lean.addAlias env `Cube.suspensionAt_update ``Submission.Cube.suspensionAt_update

open _root_.Cube in
theorem suspensionAt_mapsTo_boundary (i : N)
    (r : C(I^({j : N // j ≠ i}), I^({j : N // j ≠ i})))
    (hr : Set.MapsTo r (_root_.Cube.boundary {j : N // j ≠ i}) (_root_.Cube.boundary {j : N // j ≠ i})) :
    Set.MapsTo (suspensionAt i r) (_root_.Cube.boundary N) (_root_.Cube.boundary N) := by
  intro v hv
  rcases hv with ⟨j, hj⟩
  by_cases he : j = i
  · subst j
    exact ⟨i, by simpa only [suspensionAt_apply_pivot] using hj⟩
  · apply Cube.insertAt_boundary
    exact Or.inr (hr ⟨⟨j, he⟩, hj⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Cube.suspensionAt_mapsTo_boundary then
    throwError "Refusing to shadow existing declaration Cube.suspensionAt_mapsTo_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `Cube.suspensionAt_mapsTo_boundary ``Submission.Cube.suspensionAt_mapsTo_boundary

end Cube

namespace DifferentialGeometry.Topology

variable {N X : Type*} [DecidableEq N] [TopologicalSpace X]

def homotopyGroupSuspensionPrecomposeHom [Nonempty N] (i : N)
    (r : C(I^({j : N // j ≠ i}), I^({j : N // j ≠ i})))
    (hr : Set.MapsTo r (Cube.boundary {j : N // j ≠ i})
      (Cube.boundary {j : N // j ≠ i})) (x : X) :
    HomotopyGroup N X x →* HomotopyGroup N X x :=
  homotopyGroupPrecomposeHom i (Cube.suspensionAt i r)
    (Cube.suspensionAt_mapsTo_boundary i r hr)
    (Cube.suspensionAt_update i r) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSuspensionPrecomposeHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSuspensionPrecomposeHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSuspensionPrecomposeHom ``Submission.DifferentialGeometry.Topology.homotopyGroupSuspensionPrecomposeHom

end DifferentialGeometry.Topology
