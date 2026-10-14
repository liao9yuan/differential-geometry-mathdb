import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import Submission.DifferentialGeometry.Topology.Manifold.InteriorImage
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionRange
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Immersion
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

private theorem mem_interior_old_of_regularCrossing
    {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    p ∈ interior (Subtype.val '' E.old) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  obtain ⟨z, hz, hp, _⟩ := h
  let f := fun y : E.old => (y.val.val : P.Carrier)
  have hopen : IsOpen (f '' (𝓡∂ 3).interior E.old) :=
    DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion
      E.old_induced.isImmersion rfl
  have hsub : f '' (𝓡∂ 3).interior E.old ⊆ Subtype.val '' E.old := by
    rintro y ⟨w, _, rfl⟩
    exact ⟨w.val, w.property, rfl⟩
  exact interior_maximal hsub hopen ⟨z, hz, hp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.mem_interior_old_of_regularCrossing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.mem_interior_old_of_regularCrossing target :: scope.openDecls } }

theorem RegularCrossing.exists_survivor_partialDiffeomorph
    {p : E.incoming.terminalRegularOpen} {q : Q.Carrier}
    (h : E.RegularCrossing p.val q) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = {x | x.val ∈ interior (Subtype.val '' E.old)} ∧
      p ∈ F.source ∧ F p = q ∧ q ∈ F.target ∧
      (∀ x ∈ F.source, E.RegularCrossing x.val (F x)) ∧
      ∀ x ∈ F.source, ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
          E.terminal.metric.inner x v w := by
  let W : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
    ⟨{x | x.val ∈ interior (Subtype.val '' E.old)},
      isOpen_interior.preimage continuous_subtype_val⟩
  have hp : p ∈ W := E.mem_interior_old_of_regularCrossing h
  obtain ⟨F, hsource, hcross, _, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph W ⟨p, hp⟩ (fun _ hx => hx)
  have hpF : p ∈ F.source := by rw [hsource]; exact hp
  have heq : F p = q := E.regularCrossing_right_unique (hcross p hp) h
  refine ⟨F, hsource, hpF, heq, heq ▸ F.map_source hpF, ?_, ?_⟩
  · intro x hx
    exact hcross x (by change x ∈ (W : Set E.incoming.terminalRegularOpen); rwa [← hsource])
  · intro x hx
    exact hmetric x (by change x ∈ (W : Set E.incoming.terminalRegularOpen); rwa [← hsource])

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph

theorem metric_inner_eq_of_eventually_regularCrossing
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {XH : Type*} [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH}
    {X : Type*} [TopologicalSpace X] [ChartedSpace XH X]
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    {x : X} (hφ : MDifferentiableAt I ThreeModel φ x)
    (hcross : ∀ᶠ y in 𝓝 x, E.RegularCrossing (φ y).val (ψ y)) :
    ∀ v w : TangentSpace I x,
      E.outputMetric.inner (ψ x)
        (mfderiv I ThreeModel ψ x v) (mfderiv I ThreeModel ψ x w) =
      E.terminal.metric.inner (φ x)
        (mfderiv I ThreeModel φ x v) (mfderiv I ThreeModel φ x w) := by
  obtain ⟨F, _, hx, _, _, hFcross, hmetric⟩ :=
    (hcross.self_of_nhds).exists_survivor_partialDiffeomorph E
  have hstay : ∀ᶠ y in 𝓝 x, φ y ∈ F.source :=
    hφ.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hx)
  have heq : ψ =ᶠ[𝓝 x] (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ φ := by
    filter_upwards [hcross, hstay] with y hy hys
    exact E.regularCrossing_right_unique hy (hFcross (φ y) hys)
  intro v w
  rw [heq.mfderiv_eq (I := I) (I' := ThreeModel), heq.self_of_nhds, mfderiv_comp x
    (F.mdifferentiableAt (by simp) hx) hφ]
  exact hmetric (φ x) hx _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.metric_inner_eq_of_eventually_regularCrossing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.metric_inner_eq_of_eventually_regularCrossing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.metric_inner_eq_of_eventually_regularCrossing ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.metric_inner_eq_of_eventually_regularCrossing

variable {V XH : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace XH X]

theorem exists_survivor_partialDiffeomorph_of_regularCrossing_chart
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x))
    (x₀ : X) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = _root_.Set.range φ ∧ ψ = (F : _ → _) ∘ φ ∧
      ∀ p ∈ F.source, ∀ v w : TangentSpace ThreeModel p,
        E.outputMetric.inner (F p) (mfderiv ThreeModel ThreeModel (F : _ → _) p v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) p w) =
          E.terminal.metric.inner p v w := by
  let W : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
    ⟨range φ, Manifold.isOpen_range_of_isSmoothEmbedding hdim hφ⟩
  have hW : ∀ p ∈ W, p.val ∈ interior (Subtype.val '' E.old) := by
    rintro p ⟨y, rfl⟩
    exact E.mem_interior_old_of_regularCrossing (hcross y)
  obtain ⟨F, hsource, hcrossF, _, hmetric⟩ := E.exists_survivor_partialDiffeomorph
    W ⟨φ x₀, _root_.Set.mem_range_self x₀⟩ hW
  have heq : ψ = (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ φ := by
    funext y
    exact E.regularCrossing_right_unique (hcross y) (hcrossF (φ y) (_root_.Set.mem_range_self y))
  refine ⟨F, hsource, heq, ?_⟩
  intro p hp
  exact hmetric p (by
    change p ∈ (W : Set E.incoming.terminalRegularOpen)
    rwa [← hsource])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_partialDiffeomorph_of_regularCrossing_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_partialDiffeomorph_of_regularCrossing_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_partialDiffeomorph_of_regularCrossing_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_partialDiffeomorph_of_regularCrossing_chart

theorem isSmoothEmbedding_of_regularCrossing_chart
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x)) :
    IsSmoothEmbedding I ThreeModel ∞ ψ := by
  by_cases hX : Nonempty X
  · obtain ⟨F, hsource, heq, _⟩ :=
      E.exists_survivor_partialDiffeomorph_of_regularCrossing_chart φ ψ hφ hdim hcross hX.some
    rw [heq]
    exact DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F hφ
      (by rw [hsource])
  · let _ : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨⟨PUnit, inferInstance, inferInstance, fun x => isEmptyElim x⟩,
      ⟨⟨by ext s; simp⟩, fun x => isEmptyElim x⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.isSmoothEmbedding_of_regularCrossing_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.isSmoothEmbedding_of_regularCrossing_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.isSmoothEmbedding_of_regularCrossing_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.isSmoothEmbedding_of_regularCrossing_chart

theorem regularCrossing_chart_metric_inner
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x))
    (x : X) (v w : TangentSpace I x) :
    E.outputMetric.inner (ψ x) (mfderiv I ThreeModel ψ x v)
        (mfderiv I ThreeModel ψ x w) =
      E.terminal.metric.inner (φ x) (mfderiv I ThreeModel φ x v)
        (mfderiv I ThreeModel φ x w) := by
  obtain ⟨F, hsource, heq, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph_of_regularCrossing_chart φ ψ hφ hdim hcross x
  have hmd : MDifferentiableAt ThreeModel ThreeModel
      (F : E.incoming.terminalRegularOpen → Q.Carrier) (φ x) :=
    F.mdifferentiableAt (by simp) (by rw [hsource]; exact _root_.Set.mem_range_self x)
  have hd := mfderiv_comp x hmd (hφ.contMDiff.mdifferentiableAt (by simp))
  rw [heq, hd]
  exact hmetric (φ x) (by rw [hsource]; exact _root_.Set.mem_range_self x)
    (mfderiv I ThreeModel φ x v) (mfderiv I ThreeModel φ x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_chart_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_chart_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_chart_metric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_chart_metric_inner

theorem immersionInducedMetric_eq_of_regularCrossing_chart [IsManifold I ∞ X] [T2Space X]
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x)) :
    immersionInducedMetric E.terminal.metric hφ.isImmersion =
      immersionInducedMetric E.outputMetric
        (E.isSmoothEmbedding_of_regularCrossing_chart φ ψ hφ hdim hcross).isImmersion := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [immersionInducedMetric_inner]
  exact (E.regularCrossing_chart_metric_inner φ ψ hφ hdim hcross x v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.immersionInducedMetric_eq_of_regularCrossing_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.immersionInducedMetric_eq_of_regularCrossing_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.immersionInducedMetric_eq_of_regularCrossing_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.immersionInducedMetric_eq_of_regularCrossing_chart

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem RegularCrossing.mem_terminalRegularRegion
    {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    p ∈ E.incoming.terminalRegularRegion := by
  obtain ⟨z, _, hp, _⟩ := h
  have heq : (E.oldTerminal z).val = p := (E.oldTerminal_eq z).trans hp
  exact heq ▸ (E.oldTerminal z).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion

variable {V XH : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace XH X]

theorem exists_terminal_chart_of_regularCrossing
    (f : X → P.Carrier) (ψ : X → Q.Carrier)
    (hf : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ f)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (f x) (ψ x)) :
    ∃ φ : X → E.incoming.terminalRegularOpen,
      (∀ x, (φ x).val = f x) ∧ _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ ∧
      _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ ψ ∧
      ∀ (x : X) (v w : TangentSpace I x),
        E.outputMetric.inner (ψ x) (mfderiv I ThreeModel ψ x v)
          (mfderiv I ThreeModel ψ x w) =
        E.terminal.metric.inner (φ x) (mfderiv I ThreeModel φ x v)
          (mfderiv I ThreeModel φ x w) := by
  let φ : X → E.incoming.terminalRegularOpen := fun x =>
    ⟨f x, (hcross x).mem_terminalRegularRegion E⟩
  have hφ : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
      E.incoming.terminalRegularOpen φ hf
  exact ⟨φ, fun _ => rfl, hφ,
    E.isSmoothEmbedding_of_regularCrossing_chart φ ψ hφ hdim hcross,
    E.regularCrossing_chart_metric_inner φ ψ hφ hdim hcross⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_chart_of_regularCrossing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_chart_of_regularCrossing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_chart_of_regularCrossing ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_chart_of_regularCrossing

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
