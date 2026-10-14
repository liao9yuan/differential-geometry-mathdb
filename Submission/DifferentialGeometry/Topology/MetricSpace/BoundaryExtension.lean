import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.ContinuousMap.Basic
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.Normed.Module.RCLike.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Topology

open _root_.UniformContinuousOn in
theorem UniformContinuousOn.exists_continuous_extension_of_boundary_approach
    {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    {s t : Set X} (hst : s ⊆ t) (hts : t ⊆ closure s)
    {v η : X → Y} (hv : UniformContinuousOn v s)
    (happroach : ∀ p ∈ t, p ∉ s → ∀ ε > 0, ∀ R > 0,
      ∃ z ∈ s, _root_.Dist.dist z p < R ∧ _root_.Dist.dist (v z) (η p) < ε) :
    ∃ q : C(t, Y), UniformContinuous q ∧
      (∀ z : s, q (Set.inclusion hst z) = v z) ∧
      (∀ (p : X) (hp : p ∈ t), p ∉ s → q ⟨p, hp⟩ = η p) ∧
      ∀ K : Set Y, IsClosed K → _root_.Set.MapsTo v s K → _root_.Set.range q ⊆ K := by
  let i : s → t := Set.inclusion hst
  have hi : Isometry i := fun _ _ => rfl
  have hdense : DenseRange i := (denseRange_inclusion_iff hst).mpr hts
  have hv' : UniformContinuous (fun z : s => v z) := hv.restrict
  let q₀ := (hi.isUniformInducing.isDenseInducing hdense).extend (fun z : s => v z)
  have hq₀ : UniformContinuous q₀ :=
    uniformContinuous_uniformly_extend hi.isUniformInducing hdense hv'
  have heq (z : s) : q₀ (i z) = v z :=
    uniformly_extend_of_ind hi.isUniformInducing hdense hv' z
  let q : C(t, Y) := ⟨q₀, hq₀.continuous⟩
  refine ⟨q, hq₀, heq, ?_, ?_⟩
  · intro p hp hps
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ, hqδ⟩ := (Metric.uniformContinuous_iff.mp hq₀) (ε / 2) (half_pos hε)
    obtain ⟨z, hz, hzp, hvz⟩ := happroach p hp hps (ε / 2) (half_pos hε) δ hδ
    have hdist : _root_.Dist.dist (q₀ (⟨p, hp⟩ : t)) (q₀ (i ⟨z, hz⟩)) < ε / 2 :=
      hqδ (by change _root_.Dist.dist p z < δ; rwa [dist_comm])
    rw [heq] at hdist
    change _root_.Dist.dist (q ⟨p, hp⟩) (v z) < ε / 2 at hdist
    exact (dist_triangle (q ⟨p, hp⟩) (v z) (η p)).trans
      ((add_lt_add hdist hvz).trans_eq (add_halves ε)).le
  · intro K hK hvK y hy
    obtain ⟨z, rfl⟩ := hy
    refine hdense.induction_on (p := fun x : t => q x ∈ K) z
      (hK.preimage q.continuous) ?_
    intro x
    change q₀ (i x) ∈ K
    rw [heq]
    exact hvK x.property

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.UniformContinuousOn
  let env ← Lean.getEnv
  if env.contains `UniformContinuousOn.exists_continuous_extension_of_boundary_approach then
    throwError "Refusing to shadow existing declaration UniformContinuousOn.exists_continuous_extension_of_boundary_approach"
  Lean.modifyEnv fun env => Lean.addAlias env `UniformContinuousOn.exists_continuous_extension_of_boundary_approach ``Submission.UniformContinuousOn.exists_continuous_extension_of_boundary_approach

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

theorem exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach
    {v η : ℂ → F} (hv : UniformContinuousOn v (_root_.Metric.ball (0 : ℂ) 1))
    (happroach : ∀ p ∈ _root_.Metric.sphere (0 : ℂ) 1, ∀ ε > 0, ∀ R > 0,
      ∃ z ∈ _root_.Metric.ball (0 : ℂ) 1, _root_.Dist.dist z p < R ∧ ‖v z - η p‖ < ε) :
    ∃ q : C(closedDisk, F), UniformContinuous q ∧
      (∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1), q ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ = v z) ∧
      (∀ p (hp : p ∈ _root_.Metric.sphere (0 : ℂ) 1), q ⟨p, _root_.Metric.sphere_subset_closedBall hp⟩ = η p) ∧
      ∀ K : Set F, IsClosed K → _root_.Set.MapsTo v (_root_.Metric.ball (0 : ℂ) 1) K → _root_.Set.range q ⊆ K := by
  have hdense : _root_.Metric.closedBall (0 : ℂ) 1 ⊆ closure (_root_.Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
  have hboundary : ∀ p ∈ _root_.Metric.closedBall (0 : ℂ) 1, p ∉ _root_.Metric.ball (0 : ℂ) 1 →
      ∀ ε > 0, ∀ R > 0, ∃ z ∈ _root_.Metric.ball (0 : ℂ) 1,
        dist z p < R ∧ _root_.Dist.dist (v z) (η p) < ε := by
    intro p hp hpn ε hε R hR
    have hps : p ∈ _root_.Metric.sphere (0 : ℂ) 1 := by
      rw [_root_.Metric.mem_sphere]
      exact le_antisymm hp (not_lt.mp hpn)
    simpa only [dist_eq_norm] using happroach p hps ε hε R hR
  obtain ⟨q, hq, hi, hb, hK⟩ :=
    hv.exists_continuous_extension_of_boundary_approach _root_.Metric.ball_subset_closedBall hdense hboundary
  refine ⟨q, hq, (fun z hz => hi ⟨z, hz⟩), ?_, hK⟩
  intro p hp
  apply hb p (_root_.Metric.sphere_subset_closedBall hp)
  intro hpin
  have heq : _root_.Dist.dist p (0 : ℂ) = 1 := hp
  exact (ne_of_lt hpin) heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach ``Submission.DifferentialGeometry.Topology.exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach

end DifferentialGeometry.Topology

end
