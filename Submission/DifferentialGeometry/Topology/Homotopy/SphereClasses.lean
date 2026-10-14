import Submission.DifferentialGeometry.Topology.Homotopy.SphereTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


def homotopyGroupToFreeSphere (n : ℕ) (x : X) :
    HomotopyGroup (Fin (n + 1)) X x →
      ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  Quotient.lift (fun Γ => ZerothHomotopy.mk (genLoopSphereHomeomorph n x Γ).val) (by
    intro Γ Δ h
    obtain ⟨H⟩ := (genLoopSphereHomeomorph_homotopic_iff n x Γ Δ).mpr h
    exact Quotient.sound ((homotopic_iff_joined _ _).mp ⟨H.toHomotopy⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere

@[simp] theorem homotopyGroupToFreeSphere_mk (n : ℕ) (x : X)
    (Γ : GenLoop (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n x ⟦Γ⟧ =
      ZerothHomotopy.mk (genLoopSphereHomeomorph n x Γ).val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_mk ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_mk



theorem homotopyGroupToFreeSphere_surjective [PathConnectedSpace X] (n : ℕ) (x : X) :
    Surjective (homotopyGroupToFreeSphere n x) := by
  intro a
  induction a using ZerothHomotopy.rec with
  | mk f =>
    let y := f (cubeSphereBasepoint n)
    let Γ := (genLoopSphereHomeomorph n y).symm ⟨f, rfl⟩
    let p := PathConnectedSpace.somePath y x
    refine ⟨⟦genLoopTransport n p Γ⟧, ?_⟩
    have h : (genLoopSphereHomeomorph n y Γ).val.Homotopic
        (genLoopSphereHomeomorph n x (genLoopTransport n p Γ)).val :=
      ⟨genLoopSphereTransportHomotopy n p Γ⟩
    have hf : (genLoopSphereHomeomorph n y Γ).val = f :=
      congrArg Subtype.val ((genLoopSphereHomeomorph n y).apply_symm_apply ⟨f, rfl⟩)
    rw [hf] at h
    exact Quotient.sound ((homotopic_iff_joined _ _).mp h.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_surjective ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_surjective



theorem homotopyGroupToFreeSphere_injective [SimplyConnectedSpace X] (n : ℕ) (x : X) :
    Injective (homotopyGroupToFreeSphere n x) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h Γ =>
    induction b using Quotient.inductionOn with
    | h Δ =>
      intro h
      have hj : Joined (genLoopSphereHomeomorph n x Γ).val
          (genLoopSphereHomeomorph n x Δ).val := Quotient.exact h
      exact Quotient.sound (genLoop_homotopic_of_sphere_free_homotopic n Γ Δ
        ((homotopic_iff_joined _ _).mpr hj))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_injective ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_injective


def homotopyGroupFreeSphereEquiv [SimplyConnectedSpace X] (n : ℕ) (x : X) :
    HomotopyGroup (Fin (n + 1)) X x ≃
      ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  Equiv.ofBijective (homotopyGroupToFreeSphere n x)
    ⟨homotopyGroupToFreeSphere_injective n x, homotopyGroupToFreeSphere_surjective n x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupFreeSphereEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupFreeSphereEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupFreeSphereEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupFreeSphereEquiv


theorem homotopyGroupToFreeSphere_one (n : ℕ) (x : X) :
    homotopyGroupToFreeSphere n x 1 = ZerothHomotopy.mk (ContinuousMap.const _ x) := by
  change ZerothHomotopy.mk (genLoopSphereHomeomorph n x GenLoop.const).val = _
  rw [genLoopSphereHomeomorph_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_one ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_one


theorem homotopyGroupToFreeSphere_transport (n : ℕ) {x y : X} (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n y (homotopyGroupTransport n p a) =
      homotopyGroupToFreeSphere n x a := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact Quotient.sound ((homotopic_iff_joined _ _).mp
      (show (genLoopSphereHomeomorph n x Γ).val.Homotopic
        (genLoopSphereHomeomorph n y (genLoopTransport n p Γ)).val from
          ⟨genLoopSphereTransportHomotopy n p Γ⟩).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_transport ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_transport

end DifferentialGeometry.Topology
