import Submission.DifferentialGeometry.Geometry.Metric.Restriction.Ball
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComponentTimeShift
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegionConvexity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem componentTimeShift_rescaledMetric (c : ConnectedComponents P.Carrier)
    (t Q : ℝ) (hQ : 0 < Q) (v : ℝ) :
    rescaledMetric (G.componentTimeShift c) t Q hQ v =
      (rescaledMetric G.flow (t + a) Q hQ v).restrictOpen (P.componentOpen c) := by
  have ht : parabolicTime t Q v + a = parabolicTime (t + a) Q v := by
    dsimp only [parabolicTime]
    ring
  apply SmoothRiemannianMetric.ext_inner
  intro x V W
  simp only [rescaledMetric, G.componentTimeShift_metric, scaleMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner, ht]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_rescaledMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_rescaledMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_rescaledMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_rescaledMetric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
  {c : ConnectedComponents P.Carrier} {eps kappa t : ℝ} {x : P.componentOpen c}

def WindowedModelWitness.ofComponentTimeShift
    (W : WindowedModelWitness eps kappa (G.componentTimeShift c) x t) :
    WindowedModelWitness eps kappa G.flow x.val (t + a) := by
  let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := I3) (P.componentOpen c) ⟨x⟩
  let F := W.embedding.trans j
  have hsc : (G.componentTimeShift c).scalar t x = G.flow.scalar (t + a) x.val :=
    G.componentTimeShift_scalar c t x
  have hQ : 0 < G.flow.scalar (t + a) x.val := hsc ▸ W.scalar_pos
  have hmetric (v : ℝ) :
      rescaledMetric (G.componentTimeShift c) t ((G.componentTimeShift c).scalar t x)
        W.scalar_pos v =
        (rescaledMetric G.flow (t + a) (G.flow.scalar (t + a) x.val) hQ v).restrictOpen
          (P.componentOpen c) := by
    simp only [G.componentTimeShift_rescaledMetric, hsc]
  have hsource : F.source = W.embedding.source := by
    ext y
    change (y ∈ W.embedding.source ∧ W.embedding y ∈ (Set.univ : Set (P.componentOpen c))) ↔
      y ∈ W.embedding.source
    simp only [_root_.Set.mem_univ, and_true]
  have hball : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (by linarith : modelRadius eps ≤ modelRadius eps + 1)).trans
      W.buffered_ball
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := ?_
      scalar_pos := hQ
      window_mem := ?_
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := F
      buffered_ball := hsource ▸ W.buffered_ball
      base_map := ?_
      comparison :=
        { pullback := W.comparison.pullback
          pullback_eq := ?_
          jet := W.comparison.jet
          jet_zero := W.comparison.jet_zero
          jet_succ := W.comparison.jet_succ
          equivalence := W.comparison.equivalence
          close := W.comparison.close }
      source_capture := ?_ }
  · have ht := W.time_mem
    change t ∈ _root_.Set.Ico 0 (s - a) at ht
    change t + a ∈ _root_.Set.Ico a s
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro v hv
    have hv' : v - a ∈ _root_.Set.Icc (t - (eps * (G.componentTimeShift c).scalar t x)⁻¹) t := by
      rw [hsc]
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hh := W.window_mem hv'
    change v - a ∈ _root_.Set.Ico 0 (s - a) at hh
    change v ∈ _root_.Set.Ico a s
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · exact congrArg Subtype.val W.base_map
  · intro v y hy V
    rw [W.comparison.pullback_eq v y hy V, hmetric]
    have hder : mfderiv I3 I3 (F : W.model.M → P.Carrier) y =
        (mfderiv I3 I3 (Subtype.val : P.componentOpen c → P.Carrier) (W.embedding y)).comp
          (mfderiv I3 I3 W.embedding y) :=
      mfderiv_comp y (hasMFDerivAt_subtype_val (P.componentOpen c) (W.embedding y)).mdifferentiableAt
        (W.embedding.mdifferentiableAt (by decide) (hball hy))
    rw [hder]
    simp only [DifferentialGeometry.mfderiv_subtype_val,
      SmoothRiemannianMetric.restrictOpen_inner]
    rfl
  · intro y hy
    rw [DifferentialGeometry.riemannianBallOf_eq_image_restrictOpen_of_isClosed _
      (P.componentOpen c) (P.componentOpen_isClosed c) x (modelRadius eps - 1)] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z ∈ riemannianBallOf
        (rescaledMetric (G.componentTimeShift c) t ((G.componentTimeShift c).scalar t x)
          W.scalar_pos 0) x (modelRadius eps - 1) := by
      rw [hmetric]
      exact hz
    obtain ⟨w, hw, hweq⟩ := W.source_capture hz'
    exact ⟨w, hsource.symm ▸ hw, congrArg Subtype.val hweq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift

@[simp] theorem WindowedModelWitness.ofComponentTimeShift_model
    (W : WindowedModelWitness eps kappa (G.componentTimeShift c) x t) :
    W.ofComponentTimeShift.model = W.model := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_model ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_model

@[simp] theorem WindowedModelWitness.ofComponentTimeShift_embedding_apply
    (W : WindowedModelWitness eps kappa (G.componentTimeShift c) x t) (y : W.model.M) :
    W.ofComponentTimeShift.embedding y = (W.embedding y).val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding_apply

theorem WindowedModelWitness.ofComponentTimeShift_embedding
    (W : WindowedModelWitness eps kappa (G.componentTimeShift c) x t) :
    W.ofComponentTimeShift.embedding = W.embedding.trans
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
        (I := I3) (P.componentOpen c) ⟨x⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_embedding

theorem WindowedModelWitness.ofComponentTimeShift_source
    (W : WindowedModelWitness eps kappa (G.componentTimeShift c) x t) :
    W.ofComponentTimeShift.embedding.source = W.embedding.source := by
  ext y
  change (y ∈ W.embedding.source ∧ W.embedding y ∈ (Set.univ : Set (P.componentOpen c))) ↔
    y ∈ W.embedding.source
  simp only [_root_.Set.mem_univ, and_true]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_source

theorem WindowedModelWitness.ofComponentTimeShift_target
    (W : WindowedModelWitness eps kappa (G.componentTimeShift c) x t) :
    W.ofComponentTimeShift.embedding.target = Subtype.val '' W.embedding.target := by
  rw [← W.ofComponentTimeShift.embedding.toPartialEquiv.image_source_eq_target,
    W.ofComponentTimeShift_source]
  change (Subtype.val ∘ W.embedding) '' W.embedding.source = Subtype.val '' W.embedding.target
  calc
    _ = Subtype.val '' (W.embedding '' W.embedding.source) :=
      (Set.image_image Subtype.val W.embedding W.embedding.source).symm
    _ = Subtype.val '' W.embedding.target :=
      congrArg (Set.image Subtype.val) W.embedding.toPartialEquiv.image_source_eq_target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.ofComponentTimeShift_target

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem componentTimeShift_model_activeStage (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {c : ConnectedComponents (H.stage i.castSucc).Carrier}
    {eps kappa t : ℝ} {x : (H.stage i.castSucc).componentOpen c}
    (W : WindowedModelWitness eps kappa ((H.event i).incoming.componentTimeShift c) x t) :
    ∃ ht : t + H.time i.castSucc ∈ _root_.Set.Icc (0 : ℝ) H.horizon,
      H.activeStage ⟨t + H.time i.castSucc, ht⟩ = i.castSucc ∧
        H.stageMetric i.castSucc (t + H.time i.castSucc) =
          (H.event i).incoming.flow.base.metric (t + H.time i.castSucc) := by
  have ht : t + H.time i.castSucc ∈ H.stageDomain i.castSucc := by
    simpa only [stageDomain, Fin.lastCases_castSucc, RealTimeInterval.closedOpen] using
      W.ofComponentTimeShift.time_mem
  refine ⟨H.stageDomain_subset i.castSucc ht, (H.mem_stageDomain_iff _ i.castSucc).mp ht, ?_⟩
  simp only [stageMetric, Fin.lastCases_castSucc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.componentTimeShift_model_activeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.componentTimeShift_model_activeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.componentTimeShift_model_activeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.componentTimeShift_model_activeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
