import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import Submission.DifferentialGeometry.Topology.Manifold.SphereOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem finrank_threeSpace_eq_three : Module.finrank ℝ ThreeSpace = 3 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finrank_threeSpace_eq_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finrank_threeSpace_eq_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finrank_threeSpace_eq_three ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finrank_threeSpace_eq_three

noncomputable def TangentOrientationSection.ofSmoothOrientation {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel M) :
    TangentOrientationSection M :=
  TangentOrientationSection.ofManifoldOrientation
    (cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel M n)
        finrank_threeSpace_eq_three)
      (Classical.choose
        (DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
          ThreeModel o)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation

noncomputable def OrientedThreeStage.ofSmoothOrientation (M : Type u) [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel M) :
    OrientedThreeStage.{u} where
  Carrier := M
  orientation := TangentOrientationSection.ofSmoothOrientation o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation

noncomputable def OrientedThreeStage.ofFiniteCapQuotient {M : Type u} [TopologicalSpace M]
    {ι : Type u} [Finite ι] {precision : ι → ℝ} {L : ℝ}
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, DifferentialGeometry.Geometry.Neck.bufferedCylinder (precision i) → M)
    (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))))
    [charts : ChartedSpace ThreeSpace
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    [smooth : IsManifold ThreeModel ∞
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    [hausdorff : T2Space
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    [compact : CompactSpace
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel
      (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
        (fun i => (hf i).injective) hdisj)) : OrientedThreeStage.{u} :=
  OrientedThreeStage.ofSmoothOrientation
    (DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient hL hδ f
      (fun i => (hf i).injective) hdisj) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofFiniteCapQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofFiniteCapQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofFiniteCapQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofFiniteCapQuotient

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwoPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwoPoint target :: scope.openDecls } }

private def tubeDomainCoord (z : TubeDomain) : Sphere 2 × ℝ := (z.1, z.2.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainCoord
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainCoord target :: scope.openDecls } }

private theorem continuous_tubeDomainCoord : Continuous tubeDomainCoord :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_tubeDomainCoord
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_tubeDomainCoord target :: scope.openDecls } }

private theorem tubeDomainCoord_mem_bufferedCylinder (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (z : TubeDomain) :
    tubeDomainCoord z ∈ (DifferentialGeometry.Geometry.Neck.bufferedCylinder δ :
      Set (Sphere 2 × ℝ)) := by
  have hδinv : 1 < δ⁻¹ := (one_lt_inv₀ hδ).mpr hδ1
  have hlow : (-2 : ℝ) ≤ z.2.1 := z.2.2.1
  have hhigh : z.2.1 ≤ (2 : ℝ) := z.2.2.2
  change (-δ⁻¹ - 1 : ℝ) < z.2.1 ∧ z.2.1 < δ⁻¹ + 1
  exact ⟨by linarith, by linarith⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainCoord_mem_bufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainCoord_mem_bufferedCylinder target :: scope.openDecls } }

def tubeDomainToBufferedCylinder (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    TubeDomain → DifferentialGeometry.Geometry.Neck.bufferedCylinder δ := fun z =>
  ⟨tubeDomainCoord z, tubeDomainCoord_mem_bufferedCylinder δ hδ hδ1 z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder

theorem continuous_tubeDomainToBufferedCylinder (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Continuous (tubeDomainToBufferedCylinder δ hδ hδ1) :=
  Continuous.subtype_mk continuous_tubeDomainCoord
    (tubeDomainCoord_mem_bufferedCylinder δ hδ hδ1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_tubeDomainToBufferedCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_tubeDomainToBufferedCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_tubeDomainToBufferedCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_tubeDomainToBufferedCylinder

theorem tubeDomainToBufferedCylinder_injective (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Injective (tubeDomainToBufferedCylinder δ hδ hδ1) := by
  intro z w hzw
  have hcoord : tubeDomainCoord z = tubeDomainCoord w := congrArg Subtype.val hzw
  have hfst : z.1 = w.1 := congrArg (fun p : Sphere 2 × ℝ => p.1) hcoord
  have hsnd : z.2.1 = w.2.1 := congrArg (fun p : Sphere 2 × ℝ => p.2) hcoord
  exact Prod.ext hfst (Subtype.ext hsnd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tubeDomainToBufferedCylinder_injective

theorem not_exists_levelPreserving_bufferedCylinder_to_tubeDomain (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ¬∃ g : DifferentialGeometry.Geometry.Neck.bufferedCylinder δ → TubeDomain,
      ∀ q, ((g q).2 : ℝ) = q.val.2 := by
  rintro ⟨g, hg⟩
  have hδinv : 2 < δ⁻¹ := by
    rw [← one_div, lt_div_iff₀ hδ]
    linarith
  have hmem : (sphereTwoPoint, 3) ∈
      (DifferentialGeometry.Geometry.Neck.bufferedCylinder δ : Set (Sphere 2 × ℝ)) :=
    ⟨by linarith [inv_pos.mpr hδ], by linarith⟩
  have hle : ((g ⟨(sphereTwoPoint, 3), hmem⟩).2 : ℝ) ≤ 2 := (g _).2.2.2
  have heq : ((g ⟨(sphereTwoPoint, 3), hmem⟩).2 : ℝ) = 3 := hg _
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_levelPreserving_bufferedCylinder_to_tubeDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_levelPreserving_bufferedCylinder_to_tubeDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_levelPreserving_bufferedCylinder_to_tubeDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_levelPreserving_bufferedCylinder_to_tubeDomain

theorem nonempty_source_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : Nonempty P.Carrier :=
  E.transition.source_nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_source_of_metricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_source_of_metricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_source_of_metricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_source_of_metricCutCapEvent

theorem nontrivial_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) :
    Nonempty E.transition.trace.tubes.Index ∨ Nonempty E.discarded.Carrier :=
  E.transition.trace.nontrivial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nontrivial_of_metricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nontrivial_of_metricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nontrivial_of_metricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nontrivial_of_metricCutCapEvent

theorem nonempty_cutCapTopology_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) :
    Nonempty (CutCapTopology P.Carrier Q.Carrier E.discarded.Carrier E.capped.Carrier) :=
  ⟨E.transition.trace⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutCapTopology_of_metricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutCapTopology_of_metricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutCapTopology_of_metricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutCapTopology_of_metricCutCapEvent

theorem isEmpty_metricCutCapEvent_of_isEmpty_source {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (hP : IsEmpty P.Carrier) : IsEmpty (MetricCutCapEvent P Q a s) :=
  ⟨fun E => hP.false E.transition.source_nonempty.some⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_metricCutCapEvent_of_isEmpty_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_metricCutCapEvent_of_isEmpty_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_metricCutCapEvent_of_isEmpty_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_metricCutCapEvent_of_isEmpty_source

theorem isEmpty_cutCapTopology_pempty : IsEmpty (CutCapTopology PEmpty PEmpty PEmpty PEmpty) :=
  ⟨fun E => by
    rcases E.nontrivial with h | h
    · obtain ⟨a⟩ := h
      exact PEmpty.elim ((E.tubes.tube a) (sphereTwoPoint, ⟨0, by norm_num, by norm_num⟩))
    · exact PEmpty.elim h.some⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_cutCapTopology_pempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_cutCapTopology_pempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_cutCapTopology_pempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmpty_cutCapTopology_pempty

theorem nonempty_smoothCutCapTransition_of_metricCutCapEvent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    Nonempty (SmoothCutCapTransition P Q E.discarded E.capped) :=
  ⟨E.transition⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_metricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_metricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_metricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_metricCutCapEvent

theorem nonempty_incomingSlab_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : Nonempty (P.IncomingSlab a s) :=
  ⟨E.incoming⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_incomingSlab_of_metricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_incomingSlab_of_metricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_incomingSlab_of_metricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_incomingSlab_of_metricCutCapEvent

theorem nonempty_terminalLimitMetric_of_metricCutCapEvent {P Q : OrientedThreeStage.{u}}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    Nonempty E.incoming.TerminalLimitMetric :=
  ⟨E.terminal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_terminalLimitMetric_of_metricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_terminalLimitMetric_of_metricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_terminalLimitMetric_of_metricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_terminalLimitMetric_of_metricCutCapEvent

private noncomputable def threeSpaceSmoothOrientation :
    DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel ThreeSpace :=
  DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation ThreeSpace
    (Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three).symm
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeSpaceSmoothOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeSpaceSmoothOrientation target :: scope.openDecls } }

theorem nonempty_tangentOrientationSection_threeSpace :
    Nonempty (TangentOrientationSection ThreeSpace) :=
  ⟨TangentOrientationSection.ofSmoothOrientation threeSpaceSmoothOrientation⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_tangentOrientationSection_threeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_tangentOrientationSection_threeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_tangentOrientationSection_threeSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_tangentOrientationSection_threeSpace

private noncomputable def sphereThreeSmoothOrientation :
    DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel (Sphere 3) :=
  DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation ThreeModel
    (cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel (Sphere 3) n)
        finrank_threeSpace_eq_three.symm)
      (DifferentialGeometry.sphereOrientation 3 (by decide)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeSmoothOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeSmoothOrientation target :: scope.openDecls } }

theorem nonempty_orientedThreeStage : Nonempty OrientedThreeStage.{0} :=
  ⟨OrientedThreeStage.ofSmoothOrientation (Sphere 3) sphereThreeSmoothOrientation⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_orientedThreeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_orientedThreeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_orientedThreeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_orientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem manifoldOrientation_cast_orientation
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {n m : ℕ} (h : n = m)
    (O : DifferentialGeometry.ManifoldOrientation ThreeModel M n) (x : M) :
    (cast (congrArg (fun k => DifferentialGeometry.ManifoldOrientation ThreeModel M k) h)
      O).orientation x =
      Orientation.reindex ℝ (TangentSpace ThreeModel x) (finCongr h) (O.orientation x) := by
  subst m
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.manifoldOrientation_cast_orientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.manifoldOrientation_cast_orientation target :: scope.openDecls } }

@[simp]
theorem TangentOrientationSection.ofSmoothOrientation_apply
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel M) (x : M) :
    (TangentOrientationSection.ofSmoothOrientation o).orientation x =
      Orientation.reindex ℝ (TangentSpace ThreeModel x)
        (finCongr finrank_threeSpace_eq_three) (o.val x) := by
  unfold TangentOrientationSection.ofSmoothOrientation
  rw [TangentOrientationSection.ofManifoldOrientation_apply, manifoldOrientation_cast_orientation]
  exact congrArg
    (Orientation.reindex ℝ (TangentSpace ThreeModel x) (finCongr finrank_threeSpace_eq_three))
    (congrFun (Classical.choose_spec
      (DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
        ThreeModel o)) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation_apply

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


end

section
noncomputable section
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
def OrientedThreeStage.smoothOrientation (P : OrientedThreeStage.{u}) :
    SmoothOrientation ThreeModel P.Carrier :=
  smoothOrientationOfManifoldOrientation ThreeModel
    (cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel P.Carrier n)
      finrank_threeSpace_eq_three.symm) P.toClosedOrientedManifold.orientation)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.smoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.smoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.smoothOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.smoothOrientation

theorem OrientedThreeStage.ofSmoothOrientation_smoothOrientation (P : OrientedThreeStage.{u}) :
    OrientedThreeStage.ofSmoothOrientation P.Carrier P.smoothOrientation = P := by
  have ho : TangentOrientationSection.ofSmoothOrientation P.smoothOrientation = P.orientation := by
    have heq : (TangentOrientationSection.ofSmoothOrientation P.smoothOrientation).orientation =
        P.orientation.orientation := by
      funext x
      rw [TangentOrientationSection.ofSmoothOrientation_apply]
      change Orientation.reindex ℝ (TangentSpace ThreeModel x) (finCongr finrank_threeSpace_eq_three)
        ((cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel P.Carrier n)
          finrank_threeSpace_eq_three.symm) P.toClosedOrientedManifold.orientation).orientation x) = _
      dsimp only [OrientedThreeStage.toClosedOrientedManifold]
      rw [manifoldOrientation_cast_orientation (h := finrank_threeSpace_eq_three.symm)]
      exact (Orientation.reindex ℝ (TangentSpace ThreeModel x) (finCongr finrank_threeSpace_eq_three)).apply_symm_apply
        (P.orientation.orientation x)
    cases ha : TangentOrientationSection.ofSmoothOrientation P.smoothOrientation with
    | mk oa hlocalA =>
      cases hb : P.orientation with
      | mk ob hlocalB =>
        simp only [ha, hb] at heq
        cases heq
        rfl
  exact congrArg (fun orientation : TangentOrientationSection P.Carrier =>
    { P with orientation := orientation }) ho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation_smoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation_smoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation_smoothOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ofSmoothOrientation_smoothOrientation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end

end
