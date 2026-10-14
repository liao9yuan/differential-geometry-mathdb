import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import Submission.DifferentialGeometry.Geometry.Neck.Orientation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTubeIndexBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutRetention
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CentralNeckReparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instFiniteHornCutIndex : Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instFiniteHornCutIndex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instFiniteHornCutIndex target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }

theorem cuttingSphereComponent_mem_of_central_horn_matching
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j < 1)
    (a : ∀ c, P.hornIndex c → ℝ) (ha : ∀ c e, 1 < a c e)
    (f : ∀ j, bufferedCylinder (δ j) → D.stage.Carrier)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
    (hd : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))
    (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (hmatch : ∀ j q, q ∈ controlledCylinder (δ j) →
      f j q = (P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)).val)
    (j : P.HornCutIndex) (side : Bool) :
    cuttingSphereComponent hδ f hf hd (j,side) ∈
      scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius^2)⁻¹ ↔
      side = true := by
  have hi (j : P.HornCutIndex) : 1 < (δ j)⁻¹ := (one_lt_inv₀ (hδ j)).mpr (hδ1 j)
  have hcore : cutCore f = cutCore (P.hornCutMap δ a) := by
    apply cutCore_eq_of_central_sphere_reparametrization ν
    intro j q hq
    exact hmatch j q ⟨by linarith [(hi j),hq.1],by linarith [(hi j),hq.2]⟩
  let x := cuttingSphereAttachment hδ f (fun j => (hf j).injective) hd ⟨(j,side),spherePoint⟩
  change ConnectedComponents.mk x ∈ _ ↔ _
  rw [mem_scalarSublevelComponents_of_cutCore_eq D.slab.terminalRegularOpen D.terminal.metric
    (P.coreRadius^2)⁻¹ hcore x]
  have hx : (Homeomorph.setCongr hcore x).val =
      (P.horn j.1.val j.2 (ν j spherePoint,a j.1.val j.2-cuttingSign side)).val := by
    apply hmatch j _
    cases side <;> constructor <;> norm_num [cuttingSign] <;> linarith [hi j]
  cases side
  · obtain ⟨hz,hn⟩ := (P.hornCutMap_retains_exactly_inner_side δ hδ a ha j).2 (ν j spherePoint)
    have heq : Homeomorph.setCongr hcore x =
        (⟨(P.horn j.1.val j.2 (ν j spherePoint,a j.1.val j.2+1)).val,hz⟩ : cutCore (P.hornCutMap δ a)) := by
      apply Subtype.ext
      simpa [cuttingSign] using hx
    rw [heq]
    exact iff_of_false hn (by decide)
  · obtain ⟨hz,hm⟩ := (P.hornCutMap_retains_exactly_inner_side δ hδ a ha j).1 (ν j spherePoint)
    have heq : Homeomorph.setCongr hcore x =
        (⟨(P.horn j.1.val j.2 (ν j spherePoint,a j.1.val j.2-1)).val,hz⟩ : cutCore (P.hornCutMap δ a)) := by
      apply Subtype.ext
      exact hx
    rw [heq]
    exact iff_of_true hm rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.cuttingSphereComponent_mem_of_central_horn_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.cuttingSphereComponent_mem_of_central_horn_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.cuttingSphereComponent_mem_of_central_horn_matching ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.cuttingSphereComponent_mem_of_central_horn_matching

theorem retainedCore_terminal_of_central_horn_matching
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j < 1)
    (a : ∀ c, P.hornIndex c → ℝ) (ha : ∀ c e, 0 < a c e)
    (f : ∀ j, bufferedCylinder (δ j) → D.stage.Carrier)
    (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (hmatch : ∀ j q, q ∈ controlledCylinder (δ j) →
      f j q = (P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)).val) :
    _root_.Set.MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
      (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
        (P.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  have hi (j : P.HornCutIndex) : 1 < (δ j)⁻¹ := (one_lt_inv₀ (hδ j)).mpr (hδ1 j)
  have hcore : cutCore f = cutCore (P.hornCutMap δ a) := by
    apply cutCore_eq_of_central_sphere_reparametrization ν
    intro j q hq
    exact hmatch j q ⟨by linarith [hi j,hq.1],by linarith [hi j,hq.2]⟩
  intro x hx
  have hret : (Homeomorph.setCongr hcore x) ∈ retainedCore (P.hornCutMap δ a)
      (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ a)
        (P.coreRadius^2)⁻¹) := by
    exact (mem_scalarSublevelComponents_of_cutCore_eq D.slab.terminalRegularOpen D.terminal.metric
      (P.coreRadius^2)⁻¹ hcore x).mp hx
  exact P.hornCutMap_retained_terminal δ hδ a ha hret

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retainedCore_terminal_of_central_horn_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retainedCore_terminal_of_central_horn_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retainedCore_terminal_of_central_horn_matching ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retainedCore_terminal_of_central_horn_matching


theorem retained_oriented_neck_family_of_horn_matching
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (a : ∀ c, P.hornIndex c → ℝ) (ha : ∀ c e, δ⁻¹ + 1 < a c e)
    (x : P.HornCutIndex → D.slab.terminalRegularOpen) (k : P.HornCutIndex → ℕ)
    (d : ∀ j, normalizedDatum D.terminal.metric (x j) δ (k j))
    (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (hmatch : ∀ j (q : bufferedCylinder δ),
      (d j).oriented.map q = P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)) :
    let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
    ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
      (hd : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))),
      (∀ j side, cuttingSphereComponent (fun _ => hδ) f hf hd (j,side) ∈
        scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius^2)⁻¹ ↔ side = _root_.Bool.true) ∧
      _root_.Set.MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
        (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
          (P.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
  have hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j) :=
    fun j => isOpenEmbedding_neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
  have hnonneg (j : P.HornCutIndex) (q : bufferedCylinder δ) : 0 < a j.1.val j.2-q.val.2 := by
    have hq : q.val.2 < δ⁻¹ + 1 := q.property.2
    linarith [ha j.1.val j.2]
  have hsubset (j : P.HornCutIndex) : _root_.Set.range ((d j).oriented.map) ⊆ hornHalfRange P j.1.val j.2 := by
    rintro x ⟨q,rfl⟩
    rw [hmatch]
    exact ⟨⟨(ν j q.val.1, a j.1.val j.2 - q.val.2),(hnonneg j q).le⟩,rfl⟩
  have hd : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)) := by
    intro i j hij
    rw [_root_.Set.disjoint_left]
    rintro x ⟨q,rfl⟩ ⟨q',heq⟩
    have hindices : (⟨i.1.val,i.2⟩ : (c : ConnectedComponents D.slab.terminalRegularOpen) × P.hornIndex c) ≠
        ⟨j.1.val,j.2⟩ := by
      intro hh
      apply hij
      cases i with
      | mk c e =>
        cases j with
        | mk c' e' =>
          have hcc := congrArg Sigma.fst hh
          have hc : c = c' := Subtype.ext hcc
          subst c'
          exact congrArg (Sigma.mk c) (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)
    exact (P.hornHalfRange_pairwise_disjoint hindices).le_bot
      ⟨hsubset i ⟨q,rfl⟩,hsubset j ⟨q',Subtype.ext heq⟩⟩
  have ham (c) (e : P.hornIndex c) : 1 < a c e := by linarith [ha c e,inv_pos.mpr hδ]
  have hm (j) (q : bufferedCylinder δ) (_ : q ∈ controlledCylinder δ) :
      f j q = (P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)).val :=
    congrArg Subtype.val (hmatch j q)
  exact ⟨hf,hd,fun j side => P.cuttingSphereComponent_mem_of_central_horn_matching
    (fun _ => δ) (fun _ => hδ) (fun _ => hδ1) a ham f hf hd ν hm j side,
    P.retainedCore_terminal_of_central_horn_matching (fun _ => δ) (fun _ => hδ)
      (fun _ => hδ1) a (fun c e => zero_lt_one.trans (ham c e)) f ν hm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retained_oriented_neck_family_of_horn_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retained_oriented_neck_family_of_horn_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retained_oriented_neck_family_of_horn_matching ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.retained_oriented_neck_family_of_horn_matching


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
