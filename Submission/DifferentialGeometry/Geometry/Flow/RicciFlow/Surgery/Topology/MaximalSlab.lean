import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeTranslation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTensorContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {T : ℝ}

private theorem smoothUpTo_flowTo (F : FlowTo (I := ThreeModel) (M := P.Carrier) g T) :
    P.MetricSmoothUpTo F.S.family.metric (_root_.Set.Ico 0 T) := by
  have hj := metricCLMSection_jointContMDiffOn_of_chartGram_on
    F.S.family.metric (_root_.Set.Ico 0 T) F.joint
  intro p t ht
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  have hb : 0 < b := ht.1.trans_lt htb
  obtain ⟨U, hU, hpU, hUbase, V, hV, htV, A, hA, hEq⟩ :=
    MetricSmoothUpTo.of_contMDiffOn_Ico P F.S.family.metric hb hbT hj p t ⟨ht.1, htb.le⟩
  refine ⟨U, hU, hpU, hUbase, V ∩ _root_.Set.Iio b, hV.inter isOpen_Iio,
    ⟨htV, htb⟩, A, ?_, ?_⟩
  · intro i j
    exact (hA i j).mono (Set.prod_mono _root_.Set.inter_subset_left subset_rfl)
  · intro s hs x hx i j
    exact hEq s ⟨hs.1.1, hs.2.1, hs.1.2.le⟩ x hx i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.smoothUpTo_flowTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.smoothUpTo_flowTo target :: scope.openDecls } }

def incomingSlabOfFlowTo (F : FlowTo (I := ThreeModel) (M := P.Carrier) g T) :
    P.IncomingSlab 0 T where
  lt := F.time_pos
  flow := F.S
  equation := F.isSolution
  smoothUpTo := smoothUpTo_flowTo F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo

theorem incomingSlabOfFlowTo_metric (F : FlowTo (I := ThreeModel) (M := P.Carrier) g T)
    (t : ℝ) : (incomingSlabOfFlowTo F).flow.base.metric t = F.S.base.metric t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_metric

theorem incomingSlabOfFlowTo_initial (F : FlowTo (I := ThreeModel) (M := P.Carrier) g T) :
    (incomingSlabOfFlowTo F).flow.base.metric 0 = g := F.start

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.incomingSlabOfFlowTo_initial

theorem IncomingSlab.singularEndpoint_of_maximal {a s : ℝ}
    (G : P.IncomingSlab a s) (hmax : IsMaximalAtEndpoint G.lt G.flow) :
    G.SingularEndpoint := by
  intro L hL d hd
  obtain ⟨b, hdb, hbs⟩ := exists_between hd.2
  have hab : a < b := hd.1.trans_lt hdb
  obtain ⟨K, hK, hbound⟩ := (G.closedPrefix b hab hbs).curvature_bound P
  have hunbounded := rmUnbounded_of_maximal (I := ThreeModel) (by simp)
    G.equation hmax (rm04Realizes_metric G.flow)
  obtain ⟨t, x, hat, hts, hN⟩ := hunbounded (_root_.Max.max (L ^ 2) (K ^ 2))
  have hN0 : 0 ≤ curvatureNormSq G.flow G.flow.base.rm04 t x :=
    (sq_nonneg L).trans ((le_max_left _ _).trans hN.le)
  have hroot : Real.sqrt (curvatureNormSq G.flow G.flow.base.rm04 t x) ^ 2 =
      curvatureNormSq G.flow G.flow.base.rm04 t x := Real.sq_sqrt hN0
  have hlate : b < t := by
    by_contra ht
    have hB := hbound t ⟨hat, le_of_not_gt ht⟩ x
    change Real.sqrt (curvatureNormSq G.flow G.flow.base.rm04 t x) ≤ K at hB
    have hNK := (le_max_right (L ^ 2) (K ^ 2)).trans_lt hN
    nlinarith [Real.sqrt_nonneg (curvatureNormSq G.flow G.flow.base.rm04 t x)]
  refine ⟨t, ⟨hdb.trans hlate, hts⟩, x, ?_⟩
  change L < Real.sqrt (curvatureNormSq G.flow G.flow.base.rm04 t x)
  have hNL := (le_max_left (L ^ 2) (K ^ 2)).trans_lt hN
  nlinarith [Real.sqrt_nonneg (curvatureNormSq G.flow G.flow.base.rm04 t x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.singularEndpoint_of_maximal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.singularEndpoint_of_maximal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.singularEndpoint_of_maximal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.singularEndpoint_of_maximal

theorem exists_closedSlab_or_maximal_incomingSlab
    (P : OrientedThreeStage.{u}) (g : P.Metric) {B : ℝ} (hB : 0 < B) :
    (∃ G : P.ClosedSlab 0 B, G.flow.base.metric 0 = g) ∨
      ∃ (s : ℝ) (G : P.IncomingSlab 0 s), s ≤ B ∧
        G.flow.base.metric 0 = g ∧ IsMaximalAtEndpoint G.lt G.flow := by
  rcases exists_flowTo_beyond_or_maximal_before g B with ⟨T, hBT, F⟩ | ⟨s, F, hsB, hmax⟩
  · let Q := F.some
    have hj := metricCLMSection_jointContMDiffOn_of_chartGram_on
      Q.S.family.metric (_root_.Set.Ico 0 T) Q.joint
    exact Or.inl ⟨ClosedSlab.ofClosedOpen P Q.time_pos Q.S Q.isSolution hj hB hBT, Q.start⟩
  · exact Or.inr ⟨s, incomingSlabOfFlowTo F, hsB, F.start, hmax⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_maximal_incomingSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_maximal_incomingSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_maximal_incomingSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_maximal_incomingSlab

theorem exists_closedSlab_or_singular_incomingSlab
    (P : OrientedThreeStage.{u}) (g : P.Metric) {B : ℝ} (hB : 0 < B) :
    (∃ G : P.ClosedSlab 0 B, G.flow.base.metric 0 = g) ∨
      ∃ (s : ℝ) (G : P.IncomingSlab 0 s), s ≤ B ∧
        G.flow.base.metric 0 = g ∧ G.SingularEndpoint := by
  rcases exists_closedSlab_or_maximal_incomingSlab P g hB with h | ⟨s, G, hs, hinit, hmax⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, G, hs, hinit, G.singularEndpoint_of_maximal hmax⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab

end OrientedThreeStage

theorem OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab_from_time
    (P : OrientedThreeStage.{u}) (g : P.Metric) {a B : ℝ} (haB : a < B) :
    (∃ G : P.ClosedSlab a B, G.flow.base.metric a = g) ∨
      ∃ (s : ℝ) (G : P.IncomingSlab a s), s ≤ B ∧
        G.flow.base.metric a = g ∧ G.SingularEndpoint := by
  obtain h | ⟨s, G, hs, hinit, hsing⟩ :=
    P.exists_closedSlab_or_singular_incomingSlab g (sub_pos.mpr haB)
  · obtain ⟨G, hinit⟩ := h
    have hout : ∃ H : P.ClosedSlab (0 + a) ((B - a) + a),
        H.flow.base.metric a = g := by
      refine ⟨G.timeTranslate a, ?_⟩
      rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric, sub_self]
      exact hinit
    rw [zero_add, sub_add_cancel] at hout
    exact Or.inl hout
  · have hout : ∃ H : P.IncomingSlab (0 + a) (s + a),
        H.flow.base.metric a = g ∧ H.SingularEndpoint := by
      refine ⟨G.timeTranslate a, ?_, (G.timeTranslate_singularEndpoint_iff a).mpr hsing⟩
      rw [OrientedThreeStage.IncomingSlab.timeTranslate_metric, sub_self]
      exact hinit
    rw [zero_add] at hout
    obtain ⟨H, hinit', hsing'⟩ := hout
    exact Or.inr ⟨s + a, H, by linarith, hinit', hsing'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab_from_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab_from_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab_from_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_closedSlab_or_singular_incomingSlab_from_time

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
