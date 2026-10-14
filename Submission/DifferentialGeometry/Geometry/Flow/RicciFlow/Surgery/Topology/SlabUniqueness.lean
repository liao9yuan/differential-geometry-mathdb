import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Compact
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCapBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private theorem hasDerivWithinAt_inner (G : P.IncomingSlab a s)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico a s) (x : P.Carrier) (v w : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun r => (G.flow.base.metric r).inner x v w)
      (-2 * ricciTensor (G.flow.base.metric t) x v w) (_root_.Set.Ici a) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor] using G.hasDerivWithinAt_inner_at_start x v w
  · simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
      (metricDerivAt G.flow G.equation ⟨t, hat, ht.2⟩ x v w).hasDerivWithinAt (s := _root_.Set.Ici a)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.hasDerivWithinAt_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.hasDerivWithinAt_inner target :: scope.openDecls } }

theorem metric_eq_on_Ico_of_initial {b : ℝ}
    (G : P.IncomingSlab a s) (F : P.IncomingSlab a b)
    (hinit : G.flow.base.metric a = F.flow.base.metric a) :
    ∀ t ∈ _root_.Set.Ico a (_root_.Min.min s b), G.flow.base.metric t = F.flow.base.metric t := by
  apply ricci_flow_forward_unique_of_joint_contMDiffOn
    G.flow.base.metric F.flow.base.metric (lt_min G.lt F.lt)
  · exact G.smoothUpTo.jointContMDiffOn.mono
      (_root_.Set.prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_le (min_le_left s b)⟩) subset_rfl)
  · exact F.smoothUpTo.jointContMDiffOn.mono
      (_root_.Set.prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_le (min_le_right s b)⟩) subset_rfl)
  · intro t ht x v w
    exact hasDerivWithinAt_inner G ⟨ht.1, ht.2.trans_le (min_le_left s b)⟩ x v w
  · intro t ht x v w
    exact hasDerivWithinAt_inner F ⟨ht.1, ht.2.trans_le (min_le_right s b)⟩ x v w
  · exact hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_eq_on_Ico_of_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_eq_on_Ico_of_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_eq_on_Ico_of_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_eq_on_Ico_of_initial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
