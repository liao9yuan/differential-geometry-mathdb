import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}

def annulusSphereProductHomeomorph (ha : 0 ≤ a) :
    {x : E // a < ‖x‖ ∧ ‖x‖ < 1} ≃ₜ _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioo a 1 := by
  let S : Set E := {x | a < ‖x‖ ∧ ‖x‖ < 1}
  let T : Set (_root_.Set.Ioi (0 : ℝ)) := {r | a < r.val ∧ r.val < 1}
  have hS : S ⊆ Set.range (Subtype.val : ({0}ᶜ : Set E) → E) := by
    intro x hx
    exact ⟨⟨x, norm_pos_iff.mp (ha.trans_lt hx.1)⟩, rfl⟩
  have hT : _root_.Set.Ioo a 1 ⊆ Set.range (Subtype.val : _root_.Set.Ioi (0 : ℝ) → ℝ) := by
    intro r hr
    exact ⟨⟨r, ha.trans_lt hr.1⟩, rfl⟩
  let e₁ : S ≃ₜ {x : ({0}ᶜ : Set E) // a < ‖x.val‖ ∧ ‖x.val‖ < 1} :=
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hS).symm
  let e₂ : {x : ({0}ᶜ : Set E) // a < ‖x.val‖ ∧ ‖x.val‖ < 1} ≃ₜ
      ((Set.univ : Set (_root_.Metric.sphere (0 : E) 1)) ×ˢ T) :=
    (homeomorphUnitSphereProd E).subtype (by
      intro x
      simp only [Set.mem_prod, Set.mem_univ, true_and, T, Set.mem_ofPred_eq,
        homeomorphUnitSphereProd_apply_snd_coe])
  let e₃ : T ≃ₜ _root_.Set.Ioo a 1 :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hT
  exact e₁.trans (e₂.trans ((Homeomorph.Set.prod Set.univ T).trans
    ((Homeomorph.Set.univ _).prodCongr e₃)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.annulusSphereProductHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.annulusSphereProductHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.annulusSphereProductHomeomorph ``Submission.DifferentialGeometry.Topology.annulusSphereProductHomeomorph

theorem simplyConnectedSpace_annulus (ha : 0 ≤ a) (ha₁ : a < 1)
    [SimplyConnectedSpace (_root_.Metric.sphere (0 : E) 1)] :
    SimplyConnectedSpace {x : E // a < ‖x‖ ∧ ‖x‖ < 1} := by
  have hp : a < (a + 1) / 2 ∧ (a + 1) / 2 < 1 := by constructor <;> linarith
  let : ContractibleSpace (_root_.Set.Ioo a (1 : ℝ)) := (convex_Ioo a 1).contractibleSpace ⟨_, hp⟩
  let e : ContinuousMap.HomotopyEquiv (_root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioo a (1 : ℝ))
      (_root_.Metric.sphere (0 : E) 1) :=
    ((ContinuousMap.HomotopyEquiv.refl (_root_.Metric.sphere (0 : E) 1)).prodCongr
      (ContractibleSpace.hequiv_unit (_root_.Set.Ioo a (1 : ℝ))).some).trans
        (Homeomorph.prodUnique (_root_.Metric.sphere (0 : E) 1) Unit).toHomotopyEquiv
  exact ((annulusSphereProductHomeomorph (E := E) ha).toHomotopyEquiv.trans e).simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_annulus ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_annulus

end DifferentialGeometry.Topology
