import Submission.DifferentialGeometry.Topology.Connected.CompactComponentUnion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hsub : _root_.Set.Icc a b ⊆ D.carrier) :
    terminalRegularRegion S.base.metric a b = ⊤ := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_curvature_bound_on_carrier_interval_of_isSolutionOn (I := I) S hS hsub
  refine terminalRegularRegion_eq_top_of_uniform_bound (I := I) S.base.metric a b hab
    (Real.sqrt C) (Real.sqrt_nonneg C) (fun t ht y => ?_)
  refine Real.sqrt_le_sqrt ?_
  simpa only [SolutionOn.family_metric, metricRm04_apply]
    using hbound t (_root_.Set.Ico_subset_Icc_self ht) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval

theorem mapsTo_terminalRegularRegion_of_isSolutionOn_closedInterval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hsub : _root_.Set.Icc a b ⊆ D.carrier)
    {A : Type*} (f : A → M) (u : Set A) :
    MapsTo f u (terminalRegularRegion S.base.metric a b) := by
  rw [terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval S hS hab hsub]
  exact fun _ _ => Set.mem_univ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.mapsTo_terminalRegularRegion_of_isSolutionOn_closedInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.mapsTo_terminalRegularRegion_of_isSolutionOn_closedInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.mapsTo_terminalRegularRegion_of_isSolutionOn_closedInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.mapsTo_terminalRegularRegion_of_isSolutionOn_closedInterval

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

theorem ClosedSlab.mem_terminalRegularRegion {u v : ℝ} (G : P.ClosedSlab u v)
    (x : P.Carrier) :
    x ∈ (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularRegion := by
  rw [G.terminalRegularRegion_eq_univ P]
  exact Set.mem_univ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_terminalRegularRegion

theorem ClosedSlab.mapsTo_retainedCore {u v : ℝ} {Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (G : P.ClosedSlab u v) :
    _root_.Set.MapsTo (Subtype.val : X.trace.tubes.core → P.Carrier) X.trace.retainedCore
      (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularRegion :=
  fun _ _ => G.mem_terminalRegularRegion _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mapsTo_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mapsTo_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mapsTo_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mapsTo_retainedCore

theorem IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint {a s : ℝ}
    (G : P.IncomingSlab a s) (h : G.SingularEndpoint) :
    G.terminalRegularRegion ≠ Set.univ := by
  classical
  intro htop
  have hmem : ∀ x : P.Carrier, x ∈ G.terminalRegularRegion := fun x => by
    rw [htop]
    exact Set.mem_univ x
  simp only [IncomingSlab.terminalRegularRegion, Set.mem_ofPred_eq] at hmem
  have hmem' : ∀ x : P.Carrier, ∃ (U : Set P.Carrier) (a' K : ℝ),
      IsOpen U ∧ x ∈ U ∧ a' ∈ _root_.Set.Ico a s ∧ 0 ≤ K ∧
        ∀ y ∈ U, ∀ t ∈ _root_.Set.Ico a' s, G.riemannNorm t y ≤ K := by
    intro x
    obtain ⟨U, hU, hxU, a', ha', K, hK, hb⟩ := hmem x
    exact ⟨U, a', K, hU, hxU, ha', hK, hb⟩
  choose U a' K hU hxU ha' hK hbound using hmem'
  have hcover : (Set.univ : Set P.Carrier) ⊆ ⋃ x, U x :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hxU y⟩
  obtain ⟨tcover, htcover⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let S : Finset (Option P.Carrier) := _root_.Insert.insert _root_.Option.none (tcover.image _root_.Option.some)
  have hSne : S.Nonempty := ⟨none, by simp [S]⟩
  let A : Option P.Carrier → ℝ := fun o => o.elim a a'
  let B : Option P.Carrier → ℝ := fun o => o.elim 0 K
  have hA : ∀ o ∈ S, A o ∈ _root_.Set.Ico a s := by
    intro o _
    rcases o with _ | x
    · exact ⟨le_rfl, G.lt⟩
    · exact ha' x
  have hB : ∀ o ∈ S, 0 ≤ B o := by
    intro o _
    rcases o with _ | x
    · exact le_rfl
    · exact hK x
  obtain ⟨oA, hoA, hAmax⟩ := S.exists_max_image A hSne
  obtain ⟨oB, hoB, hBmax⟩ := S.exists_max_image B hSne
  let a₀ : ℝ := A oA
  let K₀ : ℝ := B oB
  have ha₀ : a₀ ∈ _root_.Set.Ico a s := hA oA hoA
  have hK₀ : 0 ≤ K₀ := hB oB hoB
  have hbound₀ : ∀ y : P.Carrier, ∀ t ∈ _root_.Set.Ico a₀ s, G.riemannNorm t y ≤ K₀ := by
    intro y t ht
    have hy : y ∈ ⋃ i ∈ tcover, U i := htcover (Set.mem_univ y)
    rw [Set.mem_iUnion] at hy
    obtain ⟨x, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨hx, hyx⟩ := hy
    have hsome : _root_.Option.some x ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _root_.Option.some hx)
    have h1 : a' x ≤ a₀ := hAmax (_root_.Option.some x) hsome
    have h2 : K x ≤ K₀ := hBmax (_root_.Option.some x) hsome
    exact (hbound x y hyx t ⟨h1.trans ht.1, ht.2⟩).trans h2
  obtain ⟨t, ht, y, hyt⟩ := h (K₀ + 1) (by linarith) a₀ ha₀
  exact absurd (hbound₀ y t ⟨ht.1.le, ht.2⟩)
    (not_le.mpr (lt_trans (lt_add_one K₀) hyt))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint

theorem IncomingSlab.not_isCompact_connectedComponent_of_singularEndpoint
    {a s : ℝ} (G : P.IncomingSlab a s) [PreconnectedSpace P.Carrier]
    (hsingular : G.SingularEndpoint) (x : G.terminalRegularOpen) :
    ¬ IsCompact (connectedComponent x) := by
  let _ : LocallyConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyConnectedSpace ThreeSpace G.terminalRegularOpen
  intro hcompact
  have htop := DifferentialGeometry.Topology.eq_univ_of_isOpen_of_isCompact_connectedComponent
    (U := (G.terminalRegularOpen : Set P.Carrier)) G.terminalRegularOpen.isOpen x hcompact
  exact G.terminalRegularRegion_ne_univ_of_singularEndpoint hsingular htop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.not_isCompact_connectedComponent_of_singularEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.not_isCompact_connectedComponent_of_singularEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.not_isCompact_connectedComponent_of_singularEndpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.not_isCompact_connectedComponent_of_singularEndpoint


end OrientedThreeStage

theorem GeometricCutoffRecord.terminalRegularRegion_ne_univ
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (R : GeometricCutoffRecord H i parameters) :
    (H.event i).incoming.terminalRegularRegion ≠ Set.univ :=
  OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint _
    R.singular

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.terminalRegularRegion_ne_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.terminalRegularRegion_ne_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.terminalRegularRegion_ne_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.terminalRegularRegion_ne_univ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
