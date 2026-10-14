import Submission.DifferentialGeometry.Topology.LoopSpace.BasedAdjunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {K P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]


def genLoopCircleUncurry (p : P)
    (Γ : GenLoop K (basedCircleLoop p) (basedCircleConstant p)) :
    GenLoop (K ⊕ Fin 1) P p :=
  GenLoop.genLoopGenLoopEquiv p
    (genLoopBasedMap ⟨(genLoopCircleHomeomorph p).symm,
      (genLoopCircleHomeomorph p).symm.continuous⟩
      (basedCircleConstant p) GenLoop.const (genLoopCircleHomeomorph_symm_constant p) Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCircleUncurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCircleUncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCircleUncurry ``Submission.DifferentialGeometry.Topology.genLoopCircleUncurry



theorem genLoopCircleUncurry_apply (p : P)
    (Γ : GenLoop K (basedCircleLoop p) (basedCircleConstant p))
    (t : K ⊕ Fin 1 → unitInterval) :
    genLoopCircleUncurry p Γ t =
      (Γ (t ∘ Sum.inl)).val ((t (Sum.inr 0)).val : loopCircle) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCircleUncurry_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCircleUncurry_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCircleUncurry_apply ``Submission.DifferentialGeometry.Topology.genLoopCircleUncurry_apply


theorem basedCirclePostcompose_constant (f : C(P, Q)) (p : P) :
    basedCirclePostcompose f p (basedCircleConstant p) = basedCircleConstant (f p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCirclePostcompose_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCirclePostcompose_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCirclePostcompose_constant ``Submission.DifferentialGeometry.Topology.basedCirclePostcompose_constant


theorem genLoopCircleUncurry_natural (f : C(P, Q)) (p : P)
    (Γ : GenLoop K (basedCircleLoop p) (basedCircleConstant p)) :
    genLoopCircleUncurry (f p)
      (genLoopBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) Γ) =
      genLoopPostcompose f p (genLoopCircleUncurry p Γ) := by
  ext t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCircleUncurry_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCircleUncurry_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCircleUncurry_natural ``Submission.DifferentialGeometry.Topology.genLoopCircleUncurry_natural



theorem basedCircleHomotopyGroupMulEquiv_mk (n : ℕ) (p : P)
    (Γ : GenLoop (Fin (n + 1)) (basedCircleLoop p) (basedCircleConstant p)) :
    basedCircleHomotopyGroupMulEquiv n p ⟦Γ⟧ = ⟦genLoopCircleUncurry p Γ⟧ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_mk ``Submission.DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_mk



theorem basedCircleHomotopyGroupMulEquiv_natural (n : ℕ) (f : C(P, Q)) (p : P)
    (a : HomotopyGroup (Fin (n + 1)) (basedCircleLoop p) (basedCircleConstant p)) :
    basedCircleHomotopyGroupMulEquiv n (f p)
      (homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) a) =
      homotopyGroupMap f p (basedCircleHomotopyGroupMulEquiv n p a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact congrArg
      (fun r : GenLoop (Fin (n + 1) ⊕ Fin 1) Q (f p) =>
        (⟦r⟧ : HomotopyGroup (Fin (n + 1) ⊕ Fin 1) Q (f p)))
      (genLoopCircleUncurry_natural f p Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_natural ``Submission.DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv_natural


theorem basedCirclePiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    (a : HomotopyGroup (Fin 2) (basedCircleLoop p) (basedCircleConstant p)) :
    basedCirclePiTwoMulEquiv (f p)
      (homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) a) =
      homotopyGroupMap f p (basedCirclePiTwoMulEquiv p a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    apply congrArg (fun r : GenLoop (Fin 3) Q (f p) => (⟦r⟧ : HomotopyGroup (Fin 3) Q (f p)))
    ext t
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv_natural ``Submission.DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv_natural

end DifferentialGeometry.Topology
