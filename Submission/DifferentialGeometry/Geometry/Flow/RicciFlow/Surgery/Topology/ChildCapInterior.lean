import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreNeighborhood
import Submission.DifferentialGeometry.Topology.ClosedBall.OpenAnnulus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem childCap_image_compl_range_sphereToThreeBall (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    E.childCap c b '' (Set.range sphereToThreeBall)ᶜ =
      Set.range (E.childCap c b) \ Set.range (E.childCoreInclusion c) := by
  have hrange : E.childCap c b '' Set.range sphereToThreeBall =
      Set.range (E.childSeamSphere c b) := by
    rw [← Set.range_comp]
    congr 1
    exact funext (E.childCap_boundary_eq c b)
  rw [_root_.Set.compl_eq_univ_sdiff, Set.image_sdiff (E.childCap_isEmbedding c b).injective,
    Set.image_univ, hrange, ← E.range_childCoreInclusion_inter_range_childCap]
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_image_compl_range_sphereToThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_image_compl_range_sphereToThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_image_compl_range_sphereToThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_image_compl_range_sphereToThreeBall

private theorem isOpen_range_childCap_sdiff_range_childCoreInclusion (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    IsOpen (Set.range (E.childCap c b) \ Set.range (E.childCoreInclusion c)) := by
  rw [← E.childCap_image_compl_range_sphereToThreeBall c b]
  exact E.isOpen_childCap_image_of_disjoint_boundary c b
    (isCompact_range sphereToThreeBall.continuous).isClosed.isOpen_compl (Set.Subset.refl _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.isOpen_range_childCap_sdiff_range_childCoreInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.isOpen_range_childCap_sdiff_range_childCoreInclusion target :: scope.openDecls } }

def childCapInterior (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Set (E.ChildCarrier c) :=
  Set.range (E.childCap c b) \ Set.range (E.childCoreInclusion c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInterior

theorem isOpen_childCapInterior (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    IsOpen (E.childCapInterior c b) :=
  E.isOpen_range_childCap_sdiff_range_childCoreInclusion c b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.isOpen_childCapInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.isOpen_childCapInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.isOpen_childCapInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.isOpen_childCapInterior

theorem pairwise_disjoint_childCapInterior (c : ConnectedComponents Q.Carrier) :
    Pairwise fun b b' => Disjoint (E.childCapInterior c b) (E.childCapInterior c b') := by
  intro b b' hne
  exact (E.disjoint_range_childCap hne).mono Set.sdiff_subset Set.sdiff_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pairwise_disjoint_childCapInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pairwise_disjoint_childCapInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pairwise_disjoint_childCapInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pairwise_disjoint_childCapInterior

theorem childCoreNeighborhood_union_iUnion_childCapInterior
    (c : ConnectedComponents Q.Carrier) {r : ℝ} (hr : r < 1) :
    E.childCoreNeighborhood c r ∪ ⋃ b : E.ChildCapBoundary c, E.childCapInterior c b = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hcore : x ∈ Set.range (E.childCoreInclusion c)
  · exact Or.inl (E.range_childCoreInclusion_subset_childCoreNeighborhood c hr hcore)
  · have hcov : x ∈ Set.range (E.childCoreInclusion c) ∪
        ⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b) := by
      rw [E.range_childCoreInclusion_union_range_childCap]
      trivial
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hcov.resolve_left hcore)
    exact Or.inr (Set.mem_iUnion.mpr ⟨b, hb, hcore⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhood_union_iUnion_childCapInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhood_union_iUnion_childCapInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhood_union_iUnion_childCapInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhood_union_iUnion_childCapInterior

private theorem childCap_not_mem_core_iff (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (x : ThreeBall) :
    E.childCap c b x ∉ Set.range (E.childCoreInclusion c) ↔ ‖x.1‖ < 1 := by
  have hxle : ‖x.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
  have hmem : E.childCap c b x ∈
      E.childCap c b '' (Set.range sphereToThreeBall)ᶜ ↔
        x ∉ Set.range sphereToThreeBall := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (E.childCap_isEmbedding c b).injective hyx ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  rw [E.childCap_image_compl_range_sphereToThreeBall] at hmem
  simp only [Set.mem_sdiff, Set.mem_range_self, true_and] at hmem
  rw [hmem]
  constructor
  · intro hx
    apply lt_of_le_of_ne hxle
    intro hn
    exact hx ⟨⟨x.1, by simpa using hn⟩, Subtype.ext rfl⟩
  · rintro hx ⟨y, hy⟩
    have hn : ‖x.1‖ = 1 := by
      rw [← hy]
      exact norm_eq_of_mem_sphere y
    exact (ne_of_lt hx) hn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_not_mem_core_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_not_mem_core_iff target :: scope.openDecls } }

theorem childCap_mem_childCapInterior_iff (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (x : ThreeBall) :
    E.childCap c b x ∈ E.childCapInterior c b ↔ ‖x.1‖ < 1 := by
  change (_ ∈ Set.range (E.childCap c b) ∧ _) ↔ _
  simp only [Set.mem_range_self, true_and, E.childCap_not_mem_core_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mem_childCapInterior_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mem_childCapInterior_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mem_childCapInterior_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mem_childCapInterior_iff

private def childCapInteriorMap (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    C(Metric.ball (0 : ThreeSpace) 1,
      E.childCapInterior c b) where
  toFun x := ⟨E.childCap c b ⟨x.1, Metric.ball_subset_closedBall x.2⟩,
    ⟨Set.mem_range_self _, (E.childCap_not_mem_core_iff c b _).mpr (by simpa only [Metric.mem_ball, dist_zero_right] using x.2)⟩⟩
  continuous_toFun :=
    ((E.childCap c b).continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorMap target :: scope.openDecls } }

def childCapInteriorHomeomorph (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    Metric.ball (0 : ThreeSpace) 1 ≃ₜ
      E.childCapInterior c b := by
  have he : _root_.Topology.IsEmbedding (E.childCapInteriorMap c b) := by
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    change _root_.Topology.IsEmbedding (E.childCap c b ∘ _)
    apply (E.childCap_isEmbedding c b).comp
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact _root_.Topology.IsEmbedding.subtypeVal
  apply he.toHomeomorphOfSurjective
  intro x
  obtain ⟨z, hz⟩ := x.2.1
  have hn : ‖z.1‖ < 1 := (E.childCap_not_mem_core_iff c b z).mp (hz ▸ x.2.2)
  refine ⟨⟨z.1, by simpa only [Metric.mem_ball, dist_zero_right] using hn⟩, ?_⟩
  exact Subtype.ext hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph

theorem simplyConnectedSpace_childCapInterior (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    SimplyConnectedSpace (E.childCapInterior c b) := by
  let : ContractibleSpace (Metric.ball (0 : ThreeSpace) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  exact (E.childCapInteriorHomeomorph c b).symm.toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCapInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCapInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCapInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCapInterior


@[simp] theorem childCapInteriorHomeomorph_apply_val (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (x : Metric.ball (0 : ThreeSpace) 1) :
    ((E.childCapInteriorHomeomorph c b x : E.childCapInterior c b) : E.ChildCarrier c) =
      E.childCap c b ⟨x.1, Metric.ball_subset_closedBall x.2⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph_apply_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapInteriorHomeomorph_apply_val

private def annulusToThreeBall (r : ℝ) :
    C({x : ThreeSpace // r < ‖x‖ ∧ ‖x‖ < 1}, ThreeBall) where
  toFun x := ⟨x.1, mem_closedBall_zero_iff.mpr x.2.2.le⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.annulusToThreeBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.annulusToThreeBall target :: scope.openDecls } }

private def childCapOpenAnnulusMap (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (r : ℝ) :
    C({x : ThreeSpace // r < ‖x‖ ∧ ‖x‖ < 1},
      ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b)) where
  toFun x := ⟨E.childCap c b (annulusToThreeBall r x),
    ⟨(E.childCap_mem_childCoreNeighborhood_iff c b r _).mpr x.2.1,
      (E.childCap_mem_childCapInterior_iff c b _).mpr x.2.2⟩⟩
  continuous_toFun :=
    ((E.childCap c b).continuous.comp (annulusToThreeBall r).continuous).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapOpenAnnulusMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapOpenAnnulusMap target :: scope.openDecls } }

def childCoreNeighborhoodCapInteriorHomeomorph (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (r : ℝ) :
    {x : ThreeSpace // r < ‖x‖ ∧ ‖x‖ < 1} ≃ₜ
      ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b) := by
  have he : _root_.Topology.IsEmbedding (E.childCapOpenAnnulusMap c b r) := by
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    change _root_.Topology.IsEmbedding (E.childCap c b ∘ annulusToThreeBall r)
    apply (E.childCap_isEmbedding c b).comp
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact _root_.Topology.IsEmbedding.subtypeVal
  apply he.toHomeomorphOfSurjective
  intro x
  obtain ⟨z, hz⟩ := x.2.2.1
  have hlo : r < ‖z.1‖ := (E.childCap_mem_childCoreNeighborhood_iff c b r z).mp (hz ▸ x.2.1)
  have hhi : ‖z.1‖ < 1 := (E.childCap_mem_childCapInterior_iff c b z).mp (hz ▸ x.2.2)
  refine ⟨⟨z.1, hlo, hhi⟩, ?_⟩
  exact Subtype.ext hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph

@[simp] theorem childCoreNeighborhoodCapInteriorHomeomorph_apply_val
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) (r : ℝ)
    (x : {x : ThreeSpace // r < ‖x‖ ∧ ‖x‖ < 1}) :
    ((E.childCoreNeighborhoodCapInteriorHomeomorph c b r x :
      ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b)) : E.ChildCarrier c) =
      E.childCap c b ⟨x.1, mem_closedBall_zero_iff.mpr x.2.2.le⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph_apply_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreNeighborhoodCapInteriorHomeomorph_apply_val

theorem simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) {r : ℝ}
    (hr1 : r < 1) :
    SimplyConnectedSpace ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b) := by
  let : SimplyConnectedSpace (Metric.sphere (0 : ThreeSpace) 1) :=
    DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace
  let : SimplyConnectedSpace ({x : ThreeSpace // r < ‖x‖ ∧ ‖x‖ < 1}) := by
    by_cases hr : 0 ≤ r
    · exact DifferentialGeometry.Topology.simplyConnectedSpace_annulus hr hr1
    · have hr0 : r < 0 := lt_of_not_ge hr
      have hmodel : {x : ThreeSpace | r < ‖x‖ ∧ ‖x‖ < 1} =
          Metric.ball (0 : ThreeSpace) 1 := by
        ext x
        simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
        exact and_iff_right (hr0.trans_le (norm_nonneg x))
      let : ContractibleSpace (Metric.ball (0 : ThreeSpace) 1) :=
        Metric.contractibleSpace_ball (by norm_num)
      exact (Homeomorph.setCongr hmodel).toHomotopyEquiv.simplyConnectedSpace
  exact (E.childCoreNeighborhoodCapInteriorHomeomorph c b r).symm.toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
