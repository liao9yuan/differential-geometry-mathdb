import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] {x : X}




theorem genLoop_homotopic_iff_joined (p q : GenLoop N X x) :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let F : C(unitInterval, GenLoop N X x) :=
      ⟨fun t => ⟨H.toHomotopy.curry t, fun y hy =>
        (H.eq_fst t hy).trans (GenLoop.boundary p y hy)⟩,
        H.toHomotopy.curry.continuous.subtype_mk _⟩
    refine ⟨⟨F, ?_, ?_⟩⟩
    · apply GenLoop.ext
      intro y
      exact H.apply_zero y
    · apply GenLoop.ext
      intro y
      exact H.apply_one y
  · rintro ⟨P⟩
    let F : C(unitInterval, C(N → unitInterval, X)) :=
      ⟨fun t => (P t).val, continuous_subtype_val.comp P.continuous⟩
    refine ⟨⟨⟨F.uncurry, ?_, ?_⟩, ?_⟩⟩
    · intro y
      change (P 0) y = p y
      rw [P.source]
    · intro y
      change (P 1) y = q y
      rw [P.target]
    · intro t y hy
      change (P t) y = p y
      rw [GenLoop.boundary (P t) y hy, GenLoop.boundary p y hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoop_homotopic_iff_joined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoop_homotopic_iff_joined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoop_homotopic_iff_joined ``Submission.DifferentialGeometry.Topology.genLoop_homotopic_iff_joined



theorem genLoopHomeomorph_homotopic_iff {K Y : Type*} [TopologicalSpace Y] {y : Y}
    (e : GenLoop N X x ≃ₜ GenLoop K Y y) (p q : GenLoop N X x) :
    GenLoop.Homotopic (e p) (e q) ↔ GenLoop.Homotopic p q := by
  rw [genLoop_homotopic_iff_joined, genLoop_homotopic_iff_joined]
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using h.map e.symm.continuous
  · exact fun h => h.map e.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopHomeomorph_homotopic_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopHomeomorph_homotopic_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopHomeomorph_homotopic_iff ``Submission.DifferentialGeometry.Topology.genLoopHomeomorph_homotopic_iff



def homotopyGroupIteratedLoopEquiv {K : Type*} (x : X) :
    HomotopyGroup K (GenLoop N X x) GenLoop.const ≃ HomotopyGroup (K ⊕ N) X x :=
  Quotient.congr (GenLoop.genLoopGenLoopEquiv (M := K) (N := N) x).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff
      (GenLoop.genLoopGenLoopEquiv (M := K) (N := N) x) p q).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupIteratedLoopEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupIteratedLoopEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupIteratedLoopEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupIteratedLoopEquiv

end DifferentialGeometry.Topology
