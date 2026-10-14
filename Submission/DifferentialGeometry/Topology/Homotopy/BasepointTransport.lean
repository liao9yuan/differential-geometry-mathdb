import Submission.DifferentialGeometry.Topology.Homotopy.TransportContinuity
import Submission.DifferentialGeometry.Topology.Homotopy.TransportComposition
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X}


def homotopyGroupTransport (n : ℕ) (p : Path x y) :
    HomotopyGroup (Fin (n + 1)) X x → HomotopyGroup (Fin (n + 1)) X y :=
  Quotient.map (genLoopTransport n p) (fun _ _ h => genLoopTransport_homotopic n p h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport


theorem homotopyGroupTransport_refl (n : ℕ) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n (Path.refl x) a = a := by
  induction a using Quotient.inductionOn with
  | h Γ => exact Quotient.sound (genLoopTransport_refl_homotopic n Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport_refl ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport_refl


theorem homotopyGroupTransport_trans (n : ℕ) (p : Path x y) (q : Path y z)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n q (homotopyGroupTransport n p a) =
      homotopyGroupTransport n (p.trans q) a := by
  induction a using Quotient.inductionOn with
  | h Γ => exact Quotient.sound (genLoopTransport_trans_homotopic n p q Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport_trans ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport_trans


theorem homotopyGroupTransport_path_homotopic (n : ℕ) {p q : Path x y}
    (h : p.Homotopic q) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p a = homotopyGroupTransport n q a := by
  induction a using Quotient.inductionOn with
  | h Γ => exact Quotient.sound (genLoopTransport_path_homotopic n h Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport_path_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport_path_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport_path_homotopic ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport_path_homotopic


theorem homotopyGroupTransport_symm (n : ℕ) (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p.symm (homotopyGroupTransport n p a) = a := by
  rw [homotopyGroupTransport_trans,
    homotopyGroupTransport_path_homotopic n (Path.Homotopic.trans_symm p), homotopyGroupTransport_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport_symm ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport_symm



def homotopyGroupBasepointEquiv (n : ℕ) (p : Path x y) :
    HomotopyGroup (Fin (n + 1)) X x ≃ HomotopyGroup (Fin (n + 1)) X y where
  toFun := homotopyGroupTransport n p
  invFun := homotopyGroupTransport n p.symm
  left_inv := homotopyGroupTransport_symm n p
  right_inv a := by
    simpa only [Path.symm_symm] using homotopyGroupTransport_symm n p.symm a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupBasepointEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupBasepointEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupBasepointEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupBasepointEquiv


theorem homotopyGroupTransport_natural (n : ℕ) (f : C(X, Y)) (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n (p.map f.continuous) (homotopyGroupMap f x a) =
      homotopyGroupMap f y (homotopyGroupTransport n p a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact congrArg (fun r : GenLoop (Fin (n + 1)) Y (f y) =>
      (⟦r⟧ : HomotopyGroup (Fin (n + 1)) Y (f y))) (genLoopTransport_natural n f p Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport_natural ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport_natural



theorem homotopyGroupTransport_path_independent [SimplyConnectedSpace X]
    (n : ℕ) (p q : Path x y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p a = homotopyGroupTransport n q a :=
  homotopyGroupTransport_path_homotopic n (SimplyConnectedSpace.paths_homotopic p q) a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupTransport_path_independent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupTransport_path_independent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupTransport_path_independent ``Submission.DifferentialGeometry.Topology.homotopyGroupTransport_path_independent


theorem homotopyGroup_subsingleton_of_path (n : ℕ) (p : Path x y)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)] :
    Subsingleton (HomotopyGroup (Fin (n + 1)) X y) :=
  (homotopyGroupBasepointEquiv n p).surjective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroup_subsingleton_of_path then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroup_subsingleton_of_path"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroup_subsingleton_of_path ``Submission.DifferentialGeometry.Topology.homotopyGroup_subsingleton_of_path

end DifferentialGeometry.Topology
