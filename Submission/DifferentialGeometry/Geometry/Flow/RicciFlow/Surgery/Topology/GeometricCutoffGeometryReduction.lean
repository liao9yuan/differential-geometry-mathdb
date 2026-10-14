import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapPersistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace D]
  [TopologicalSpace N]

theorem iUnion_range_cap_eq_empty (E : CutCapTopology M Q D N) [IsEmpty E.tubes.Index] :
    (⋃ b : E.tubes.Boundary, Set.range (E.capping.cap b)) = ∅ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
  exact fun b => isEmptyElim b.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.iUnion_range_cap_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.iUnion_range_cap_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.iUnion_range_cap_eq_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.iUnion_range_cap_eq_empty

theorem range_coreInclusion_eq_univ (E : CutCapTopology M Q D N) [IsEmpty E.tubes.Index] :
    Set.range E.capping.coreInclusion = Set.univ := by
  have h := E.capping.exhaustive
  rw [iUnion_range_cap_eq_empty E, Set.union_empty] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.range_coreInclusion_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.range_coreInclusion_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.range_coreInclusion_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.range_coreInclusion_eq_univ

theorem exists_notMem_retainedCore (E : CutCapTopology M Q D N) [IsEmpty E.tubes.Index] :
    ∃ x : E.tubes.core, x ∉ E.retainedCore := by
  rcases E.nontrivial with h | h
  · exact isEmptyElim h.some
  · obtain ⟨d⟩ := h
    have hsurj : Function.Surjective fun x : E.tubes.core =>
        E.presentation (E.capping.coreInclusion x) := by
      intro y
      obtain ⟨n, hn⟩ := E.presentation.surjective y
      have hnmem : n ∈ Set.range E.capping.coreInclusion := by
        rw [range_coreInclusion_eq_univ E]
        exact Set.mem_univ n
      obtain ⟨x, hx⟩ := hnmem
      exact ⟨x, by change E.presentation (E.capping.coreInclusion x) = y; rw [hx]; exact hn⟩
    obtain ⟨x, hx⟩ := hsurj (Sum.inr d)
    refine ⟨x, fun hxr => ?_⟩
    obtain ⟨q, hq⟩ := hxr
    exact Sum.inr_ne_inl (hx.symm.trans hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.exists_notMem_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.exists_notMem_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.exists_notMem_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.exists_notMem_retainedCore

end CutCapTopology

variable (H : ObservedHistory.{u}) (i : Fin H.eventCount)

theorem geometricCutoff_no_cuts_discard
    [IsEmpty (H.event i).transition.trace.tubes.Index] :
    ∃ x : (H.event i).transition.trace.tubes.core,
      x ∉ (H.event i).transition.trace.retainedCore :=
  CutCapTopology.exists_notMem_retainedCore (H.event i).transition.trace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricCutoff_no_cuts_discard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricCutoff_no_cuts_discard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricCutoff_no_cuts_discard ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricCutoff_no_cuts_discard

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem retainedBoundary_iff_capRetained (b : E.transition.trace.tubes.Boundary) :
    E.RetainedBoundary b ↔ E.transition.trace.capRetained b :=
  (E.transition.trace.capRetained_iff_coreBoundarySphere_mem_retainedCore b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedBoundary_iff_capRetained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedBoundary_iff_capRetained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedBoundary_iff_capRetained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedBoundary_iff_capRetained

theorem one_retained_side_iff_cap (α : E.transition.trace.tubes.Index) :
    (E.RetainedBoundary (α, _root_.Bool.true) ↔ ¬ E.RetainedBoundary (α, _root_.Bool.false)) ↔
      (E.transition.trace.capRetained (α, _root_.Bool.true) ↔
        E.transition.trace.capDiscarded (α, _root_.Bool.false)) := by
  rw [retainedBoundary_iff_capRetained, retainedBoundary_iff_capRetained,
    CutCapTopology.capDiscarded_iff_not_capRetained]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.one_retained_side_iff_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.one_retained_side_iff_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.one_retained_side_iff_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.one_retained_side_iff_cap

end MetricCutCapEvent

def canonicalNominalRadius {ι : Type*} (s : ι → ℝ) (h : Nonempty ι) : ℝ :=
  Real.sqrt ((s (Classical.choice h))⁻¹)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius

theorem canonicalNominalRadius_pos {ι : Type*} {s : ι → ℝ} (hpos : ∀ a, 0 < s a)
    (h : Nonempty ι) : 0 < canonicalNominalRadius s h :=
  Real.sqrt_pos.2 (inv_pos.2 (hpos _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_pos

theorem canonicalNominalRadius_sq {ι : Type*} {s : ι → ℝ} (hpos : ∀ a, 0 < s a)
    (hconst : ∀ a b, s a = s b) (a : ι) :
    ((canonicalNominalRadius s ⟨a⟩) ^ 2)⁻¹ = s a := by
  have hchoice : s (Classical.choice (⟨a⟩ : Nonempty ι)) = s a := hconst _ _
  have hsq : (canonicalNominalRadius s ⟨a⟩) ^ 2 = (s a)⁻¹ := by
    rw [canonicalNominalRadius, hchoice,
      Real.sq_sqrt (le_of_lt (inv_pos.2 (hpos a)))]
  rw [hsq, inv_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_sq

theorem scale_const_of_scale_eq_shape {ι : Type*} {s : ι → ℝ} {r : Nonempty ι → ℝ}
    (h : ∀ α, s α = ((r ⟨α⟩) ^ 2)⁻¹) : ∀ α β, s α = s β := by
  intro α β
  have hp : (⟨α⟩ : Nonempty ι) = ⟨β⟩ := Subsingleton.elim _ _
  rw [h α, h β, hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scale_const_of_scale_eq_shape then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scale_const_of_scale_eq_shape"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scale_const_of_scale_eq_shape ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scale_const_of_scale_eq_shape

theorem canonicalNominalRadius_eq_of_scale_eq_shape {ι : Type*} {s : ι → ℝ}
    {r : Nonempty ι → ℝ} (hpos : ∀ h, 0 < r h) (h : ∀ α, s α = ((r ⟨α⟩) ^ 2)⁻¹)
    (hh : Nonempty ι) : canonicalNominalRadius s hh = r hh := by
  set α : ι := Classical.choice hh
  have hα : (⟨α⟩ : Nonempty ι) = hh := Subsingleton.elim _ _
  have hs : s α = ((r hh) ^ 2)⁻¹ := by rw [h α, hα]
  have hsq : (r hh) ^ 2 = (s α)⁻¹ := by rw [hs, inv_inv]
  rw [canonicalNominalRadius, ← hsq, Real.sqrt_sq (le_of_lt (hpos hh))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_eq_of_scale_eq_shape then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_eq_of_scale_eq_shape"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_eq_of_scale_eq_shape ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNominalRadius_eq_of_scale_eq_shape

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

def TubeBandHit (x : E.transition.trace.tubes.core) : Prop :=
  ∃ t : E.transition.trace.tubes.Index, x.1 ∈ E.transition.trace.tubes.tube t ''
    {z : TubeDomain | (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.TubeBandHit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.TubeBandHit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.TubeBandHit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.TubeBandHit

theorem old_eq_retained_of_old_tubeBand
    (h : ∀ x ∈ E.transition.trace.retainedCore, E.TubeBandHit x → x ∈ E.old) :
    E.old = E.transition.trace.retainedCore := by
  refine Set.Subset.antisymm E.old_retained fun x hx => ?_
  by_cases hband : E.TubeBandHit x
  · exact h x hx hband
  · exact E.old_contains_outside x hx fun t ht => hband ⟨t, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_old_tubeBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_old_tubeBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_old_tubeBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_old_tubeBand

theorem old_tubeBand_of_old_eq_retained (h : E.old = E.transition.trace.retainedCore) :
    ∀ x ∈ E.transition.trace.retainedCore, E.TubeBandHit x → x ∈ E.old := by
  intro x hx _
  rw [h]
  exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_tubeBand_of_old_eq_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_tubeBand_of_old_eq_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_tubeBand_of_old_eq_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_tubeBand_of_old_eq_retained

theorem old_eq_retained_of_isEmpty_index [IsEmpty E.transition.trace.tubes.Index] :
    E.old = E.transition.trace.retainedCore :=
  E.old_eq_retained_of_old_tubeBand fun _ _ hb => by
    obtain ⟨t, _⟩ := hb
    exact isEmptyElim t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_isEmpty_index ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.old_eq_retained_of_isEmpty_index

end MetricCutCapEvent

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem scale_const_of_scale_eq (α β : (H.event i).transition.trace.tubes.Index) :
    (G.neck α).scale = (G.neck β).scale :=
  scale_const_of_scale_eq_shape G.scale_eq α β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scale_const_of_scale_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scale_const_of_scale_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scale_const_of_scale_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scale_const_of_scale_eq

theorem nominalRadius_eq_canonical (α : (H.event i).transition.trace.tubes.Index) :
    G.nominalRadius ⟨α⟩ = canonicalNominalRadius (fun γ => (G.neck γ).scale) ⟨α⟩ :=
  (canonicalNominalRadius_eq_of_scale_eq_shape G.nominal_pos G.scale_eq ⟨α⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nominalRadius_eq_canonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nominalRadius_eq_canonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nominalRadius_eq_canonical ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nominalRadius_eq_canonical

end GeometricCutoffRecord

theorem tube_eq_of_abs_snd_le_two {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) (z : neckBuffer (G.delta α))
    (hz : |(z.1.2)| ≤ 2) :
    ∃ w : TubeDomain, (H.event i).transition.trace.tubes.tube α w = ((G.neck α).chart z).1 := by
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  exact ⟨(z.1.1, ⟨z.1.2, hz1, hz2⟩),
    G.tube_eq α (z.1.1, ⟨z.1.2, hz1, hz2⟩) z.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_eq_of_abs_snd_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_eq_of_abs_snd_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_eq_of_abs_snd_le_two ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tube_eq_of_abs_snd_le_two

theorem pairwise_disjoint_chart_range_central {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters)
    {α β : (H.event i).transition.trace.tubes.Index} (h : α ≠ β) :
    Disjoint (Set.range fun z : {z : neckBuffer (G.delta α) | |(z.1.2)| ≤ 2} =>
        (G.neck α).chart z)
      (Set.range fun z : {z : neckBuffer (G.delta β) | |(z.1.2)| ≤ 2} =>
        (G.neck β).chart z) := by
  refine Set.disjoint_left.mpr fun p hp hq => ?_
  obtain ⟨z, rfl⟩ := hp
  obtain ⟨z', hz'⟩ := hq
  obtain ⟨w, hw⟩ := tube_eq_of_abs_snd_le_two G α z z.2
  obtain ⟨w', hw'⟩ := tube_eq_of_abs_snd_le_two G β z' z'.2
  refine Set.disjoint_left.mp ((H.event i).transition.trace.tubes.disjoint h) ⟨w, hw⟩ ?_
  exact ⟨w', hw'.trans (congrArg Subtype.val hz')⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_chart_range_central then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_chart_range_central"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_chart_range_central ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_chart_range_central

theorem standardNeckCutCap_one_retained_side :
    (∀ z : Sphere 2, standardNeckCutCap.tubes.coreBoundarySphere (PUnit.unit, _root_.Bool.true) z ∈
        standardNeckCutCap.retainedCore) ↔
      ¬ (∀ z : Sphere 2,
        standardNeckCutCap.tubes.coreBoundarySphere (PUnit.unit, _root_.Bool.false) z ∈
          standardNeckCutCap.retainedCore) := by
  constructor
  · intro h
    exact absurd (h sphereNorth)
      (standardNeckCutCap_coreBoundarySphere_true_not_mem_retainedCore sphereNorth)
  · intro h
    exact absurd (fun z =>
      standardNeckCutCap_coreBoundarySphere_false_mem_retainedCore z) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckCutCap_one_retained_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckCutCap_one_retained_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckCutCap_one_retained_side ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckCutCap_one_retained_side

structure GeometricCutoffGeometryFrontier (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (parameters : CutoffParameters) where
  delta : (H.event i).transition.trace.tubes.Index → ℝ
  delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ)
  order : (H.event i).transition.trace.tubes.Index → ℕ
  order_lower : ∀ α, _root_.Max.max (parameters.modelOrder + 6)
    (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)
  scale_const : ∀ α β, (neck α).scale = (neck β).scale
  nominal_small : ∀ h, canonicalNominalRadius (fun α => (neck α).scale) h <
    (parameters.delta (H.time i.succ))^2 * parameters.neckRadius (H.time i.succ)
  nominal_time : ∀ h, (canonicalNominalRadius (fun α => (neck α).scale) h)^2 ≤
    H.time i.succ
  backward : ∀ α, IncomingBackwardNeck H i (neck α)
    (canonicalNominalRadius (fun α => (neck α).scale) ⟨α⟩)
  singular : (H.event i).incoming.SingularEndpoint
  buffer_disjoint : Pairwise fun α β =>
    Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  protected_interior : ∀ x : (H.event i).incoming.terminalRegularOpen,
    metricScalarAt (H.event i).terminal.metric x ≤
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
    x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
    (∃ x : (H.event i).transition.trace.tubes.core,
      ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      ∃ hx : x.1 ∈ (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
          metricScalarAt (H.event i).terminal.metric x ≤
            ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹
  one_retained_side : ∀ α,
    (H.event i).RetainedBoundary (α, _root_.Bool.true) ↔ ¬ (H.event i).RetainedBoundary (α, _root_.Bool.false)
  old_tube_band : ∀ x ∈ (H.event i).transition.trace.retainedCore,
    MetricCutCapEvent.TubeBandHit (H.event i) x → x ∈ (H.event i).old
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric a x) →
    ∀ x : (H.stage i.succ).Carrier, InFixedHamiltonIveyRegion (H.event i).outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      L ≤ metricScalarAt (H.event i).terminal.metric x) →
    ∀ x : (H.stage i.succ).Carrier, L ≤ metricScalarAt (H.event i).outputMetric x
  recenter : HasRecenterConstants.{u} parameters
  staticFrontier : ∀ b : (H.event i).RetainedBoundaryIndex,
    PresentedStaticCapFrontier H i parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy
      (recenterNeck (H := H) (i := i) (parameters := parameters) recenter neck
        (fun α => delta_le α) (fun α => order_lower α) b) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier

namespace GeometricCutoffGeometryFrontier

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

def toReduction (F : GeometricCutoffGeometryFrontier H i parameters) :
    GeometricCutoffFrontierReduction H i parameters where
  singular := F.singular
  nominalRadius := canonicalNominalRadius fun α => (F.neck α).scale
  nominal_small := fun h => F.nominal_small h
  nominal_time := fun h => F.nominal_time h
  delta := F.delta
  delta_le := F.delta_le
  order := F.order
  order_lower := F.order_lower
  neck := F.neck
  scale_eq := fun α => (canonicalNominalRadius_sq
    (s := fun β => (F.neck β).scale) (fun β => (F.neck β).scale_pos) F.scale_const α).symm
  buffer_disjoint := F.buffer_disjoint
  tube_eq := F.tube_eq
  backward := fun α => F.backward α
  protected_interior := F.protected_interior
  retained_meets_protected := F.retained_meets_protected
  one_retained_side := F.one_retained_side
  no_cuts_discard := fun h => @geometricCutoff_no_cuts_discard H i h
  old_eq_retained := (H.event i).old_eq_retained_of_old_tubeBand F.old_tube_band
  curvature_preserving := F.curvature_preserving
  scalar_preserving := F.scalar_preserving
  recenter := F.recenter
  staticFrontier := F.staticFrontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toReduction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toReduction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toReduction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toReduction

def toFrontier (F : GeometricCutoffGeometryFrontier H i parameters) :
    GeometricCutoffFrontier H i parameters :=
  GeometricCutoffFrontierReduction.ofReduction F.toReduction

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.toFrontier

def ofReduction (R : GeometricCutoffFrontierReduction H i parameters) :
    GeometricCutoffGeometryFrontier H i parameters where
  delta := R.delta
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := R.neck
  scale_const := scale_const_of_scale_eq_shape R.scale_eq
  nominal_small := fun h => by
    rw [canonicalNominalRadius_eq_of_scale_eq_shape
      (nominal_pos_of_incomingBackwardNeck R.neck R.backward) R.scale_eq h]
    exact R.nominal_small h
  nominal_time := fun h => by
    rw [canonicalNominalRadius_eq_of_scale_eq_shape
      (nominal_pos_of_incomingBackwardNeck R.neck R.backward) R.scale_eq h]
    exact R.nominal_time h
  backward := fun α => by
    rw [canonicalNominalRadius_eq_of_scale_eq_shape
      (nominal_pos_of_incomingBackwardNeck R.neck R.backward) R.scale_eq ⟨α⟩]
    exact R.backward α
  singular := R.singular
  buffer_disjoint := R.buffer_disjoint
  tube_eq := R.tube_eq
  protected_interior := R.protected_interior
  retained_meets_protected := R.retained_meets_protected
  one_retained_side := R.one_retained_side
  old_tube_band := (H.event i).old_tubeBand_of_old_eq_retained R.old_eq_retained
  curvature_preserving := R.curvature_preserving
  scalar_preserving := R.scalar_preserving
  recenter := R.recenter
  staticFrontier := R.staticFrontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.ofReduction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.ofReduction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.ofReduction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.ofReduction

theorem nonempty_geometricCutoffGeometryFrontier_iff_nonempty_reduction :
    Nonempty (GeometricCutoffGeometryFrontier H i parameters) ↔
      Nonempty (GeometricCutoffFrontierReduction H i parameters) :=
  ⟨fun ⟨F⟩ => ⟨F.toReduction⟩, fun ⟨R⟩ => ⟨ofReduction R⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffGeometryFrontier_iff_nonempty_reduction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffGeometryFrontier_iff_nonempty_reduction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffGeometryFrontier_iff_nonempty_reduction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffGeometryFrontier_iff_nonempty_reduction

theorem nonempty_geometricCutoffRecord_of_geometryFrontier
    (h : Nonempty (GeometricCutoffGeometryFrontier H i parameters)) :
    Nonempty (GeometricCutoffRecord H i parameters) :=
  h.map fun F => GeometricCutoffRecord.ofFrontier F.toFrontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffRecord_of_geometryFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffRecord_of_geometryFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffRecord_of_geometryFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffGeometryFrontier.nonempty_geometricCutoffRecord_of_geometryFrontier

end GeometricCutoffGeometryFrontier

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

def ofEmptyIndex [hindex : IsEmpty (H.event i).transition.trace.tubes.Index]
    (hsingular : (H.event i).incoming.SingularEndpoint)
    (hprotected : ∀ x : (H.event i).incoming.terminalRegularOpen,
      metricScalarAt (H.event i).terminal.metric x ≤ ((p.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
      x.val ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore))
    (hmeets : ∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
      (∃ x : (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
      ∃ x : (H.event i).incoming.terminalRegularOpen,
        ∃ hx : x.val ∈ (H.event i).transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
            metricScalarAt (H.event i).terminal.metric x ≤
              ((p.protectedRadius (H.time i.succ)) ^ 2)⁻¹)
    (hcurvature : ∀ a : ℝ, 0 < a →
      (∀ x : (H.event i).incoming.terminalRegularOpen,
        InFixedHamiltonIveyRegion (H.event i).terminal.metric a x) →
      ∀ x : (H.stage i.succ).Carrier, InFixedHamiltonIveyRegion (H.event i).outputMetric a x)
    (hscalar : ∀ L : ℝ, L ≤ 0 →
      (∀ x : (H.event i).incoming.terminalRegularOpen,
        L ≤ metricScalarAt (H.event i).terminal.metric x) →
      ∀ x : (H.stage i.succ).Carrier, L ≤ metricScalarAt (H.event i).outputMetric x) :
    GeometricCutoffRecord H i p where
  singular := hsingular
  nominalRadius := fun h => (h.elim hindex.false).elim
  nominal_pos := fun h => (h.elim hindex.false).elim
  nominal_small := fun h => (h.elim hindex.false).elim
  nominal_time := fun h => (h.elim hindex.false).elim
  delta := fun α => isEmptyElim α
  delta_pos := fun α => isEmptyElim α
  delta_le := fun α => isEmptyElim α
  order := fun α => isEmptyElim α
  order_lower := fun α => isEmptyElim α
  neck := fun α => isEmptyElim α
  scale_eq := fun α => isEmptyElim α
  buffer_disjoint := fun α => isEmptyElim α
  tube_eq := fun α => isEmptyElim α
  tube_in_buffer := fun α => isEmptyElim α
  backward := fun α => isEmptyElim α
  retained_terminal := retained_terminal_of_old_eq_retained (H.event i)
    (H.event i).old_eq_retained_of_isEmpty_index
  protected_interior := hprotected
  retained_meets_protected := hmeets
  one_retained_side := fun α => isEmptyElim α
  no_cuts_discard := fun _ => geometricCutoff_no_cuts_discard H i
  static := fun b => isEmptyElim b.val.1
  recenter_scale := fun b => isEmptyElim b.val.1
  recenter_mark := fun b => isEmptyElim b.val.1
  recenter_delta := fun b => isEmptyElim b.val.1
  recenter_scale_comparison := fun b => isEmptyElim b.val.1
  recenter_chart := fun b => isEmptyElim b.val.1
  recenter_in_buffer := fun b => isEmptyElim b.val.1
  old_eq_retained := (H.event i).old_eq_retained_of_isEmpty_index
  curvature_preserving := hcurvature
  scalar_preserving := hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofEmptyIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofEmptyIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofEmptyIndex ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofEmptyIndex

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
