import Submission.DifferentialGeometry.Topology.Homotopy.LoopTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {K N X : Type*} [TopologicalSpace X] [DecidableEq K] [DecidableEq N]


theorem genLoop_reindex_transAt (e : K ≃ N) (x : X) (i : K) (p q : GenLoop K X x) :
    GenLoop.congr x e (GenLoop.transAt i p q) =
      GenLoop.transAt (e i) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  ext t
  change (GenLoop.transAt i p q) (t ∘ e) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy, Function.comp_apply]
  split_ifs
  · change p _ = p _
    exact congrArg p (_root_.Function.update_comp_eq_of_injective t e.injective i _).symm
  · change q _ = q _
    exact congrArg q (_root_.Function.update_comp_eq_of_injective t e.injective i _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoop_reindex_transAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoop_reindex_transAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoop_reindex_transAt ``Submission.DifferentialGeometry.Topology.genLoop_reindex_transAt


def homotopyGroupReindexMulEquiv [Nonempty K] [Nonempty N] (e : K ≃ N) (x : X) :
    HomotopyGroup K X x ≃* HomotopyGroup N X x where
  toEquiv := Quotient.congr (GenLoop.congr x e).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff (GenLoop.congr x e) p q).symm)
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : K := Classical.arbitrary K
        let E : HomotopyGroup K X x ≃ HomotopyGroup N X x :=
          Quotient.congr (GenLoop.congr x e).toEquiv
            (fun p q => (genLoopHomeomorph_homotopic_iff (GenLoop.congr x e) p q).symm)
        have hmul := congrArg E (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        exact (congrArg (fun r : GenLoop N X x => (⟦r⟧ : HomotopyGroup N X x))
          (genLoop_reindex_transAt e x i q p)).trans
            (HomotopyGroup.mul_spec (i := e i) (p := GenLoop.congr x e p) (q := GenLoop.congr x e q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupReindexMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupReindexMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupReindexMulEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupReindexMulEquiv

end DifferentialGeometry.Topology
