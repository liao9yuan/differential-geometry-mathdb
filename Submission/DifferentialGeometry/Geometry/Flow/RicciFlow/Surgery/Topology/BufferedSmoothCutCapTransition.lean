import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingCompletion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedBoundaryOrientation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedCutCapPresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCappingSmooth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingReparametrization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedCappingOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [CompactSpace M] [Nonempty M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instLocallyPathConnectedSpace_differentialGeometry : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instLocallyPathConnectedSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instLocallyPathConnectedSpace_differentialGeometry target :: scope.openDecls } }
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded hL hδ f hf hdisj R

include hs in
theorem exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps :
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : T2Space Q := (finiteCapQuotient_topological_properties ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj).2.1
    letI : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Ret := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).1
    letI : IsManifold ThreeModel ∞ Disc := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).2
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
    ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b, A b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ A b = LinearIsometryEquiv.neg ℝ) ∧
      (∀ b x, (B b x : ThreeSpace) = A b x) ∧
      ∃ X : SmoothCutCapTransition (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet)
        (OrientedThreeStage.ofSmoothOrientation Disc oDisc)
        (OrientedThreeStage.ofSmoothOrientation Q oQ),
        X.trace = (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
          (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary ∧
          X.boundaryFrameReversing := by
  classical
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := (finiteCapQuotient_topological_properties ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj).2.1
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Ret := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).1
  let : IsManifold ThreeModel ∞ Disc := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).2
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  let : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) := cutCoreBoundaryChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) := cutCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  obtain ⟨oE, oQ, oRet, oDisc, oSum, _, hmatched, _, _, hcore, hcap, hret, hdisc, hsuml, hsumr, _, hpres⟩ :=
    exists_finiteCapSelectedSmoothOrientations ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R o
  choose A B a hchoice hB ha hboundary hA using fun b : ι × Bool =>
    exists_cap_reparametrization_map_orientation
      (Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three) (oE b)) b.2
  let E := (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
    (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary
  let P := OrientedThreeStage.ofSmoothOrientation M o
  let Qs := OrientedThreeStage.ofSmoothOrientation Ret oRet
  let Ds := OrientedThreeStage.ofSmoothOrientation Disc oDisc
  let Ns := OrientedThreeStage.ofSmoothOrientation Q oQ
  let := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
  let : IsManifold (𝓡∂ 3) ∞ (T).core := bufferedCutCore_isManifold hδ hδ1 f hf hdisj hs
  let X : SmoothCutCapTransition P Qs Ds Ns :=
    { trace := E
      source_nonempty := (show Nonempty M from inferInstance)
      tube_smooth := by
        let : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
        intro i
        exact originalTubularMap_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three
          (hδ i) (hδ1 i) (f i) (hf i) (hs i)
      coreCharts := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
      coreSmooth := bufferedCutCore_isManifold hδ hδ1 f hf hdisj hs
      core_induced := bufferedCutCore_isSmoothEmbedding hδ hδ1 f hf hdisj hs
      core_boundary := bufferedCutCore_boundary hδ hδ1 f hf hdisj hs
      core_inclusion_smooth := Capping.ofBufferedFiniteCaps_coreInclusion_isSmoothEmbedding hL hδ hδ1 f hf hdisj hs
      ballCharts := threeBallChartedSpace
      ballSmooth := threeBall_isManifold
      ball_induced := isSmoothEmbedding_threeBall_inclusion
      ball_boundary := threeBall_boundary_eq_sphere
      cap_smooth := fun b => isSmoothEmbedding_diffeomorph_precomp _
        (Capping.ofBufferedFiniteCaps_cap_isSmoothEmbedding hL hδ hδ1 f hf hdisj hs b) (B b)
      attaching := a
      attaching_eq := fun _ => rfl
      core_positive := fun x _ =>
        Capping.ofBufferedFiniteCaps_core_positive_of_preserving_orientation
          hL hδ hδ1 f hf hdisj hs o oQ hcore x
      cap_positive := fun b x _ =>
        cap_positive_of_preserving_orientation hL
          (fun y => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩)
          (finiteCapInclusion_ball_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs b)
          (oE b) oQ (A b) (B b) b.2 (hB b) (hA b) (hcap b) x
      presentation := (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj R).symm
      presentation_eq := rfl
      presentation_positive := by
        intro x
        change Q at x
        let F := (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj R).symm
        let J : ThreeSpace ≃ₗ[ℝ] ThreeSpace :=
          (differentialEquivOfBijective ThreeModel ThreeModel F
            (fun y => (F.mfderivToContinuousLinearEquiv (by simp) y).bijective) x).toLinearEquiv
        have hh := DifferentialGeometry.orientation_map_inverse_trans_of_tangentOrientationEquiv
          finrank_threeSpace_eq_three (LinearEquiv.refl ℝ ThreeSpace) J (oQ.val x)
          (tangentOrientationEquiv_refl (oQ.val x)) (hpres x)
        have htarget : Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three)
            (oSum.val (F x)) = match F x with
              | Sum.inl q => Qs.orientation.orientation q
              | Sum.inr d => Ds.orientation.orientation d := by
          cases hfx : F x with
          | inl q =>
            change Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three)
                (oSum.val (Sum.inl q)) = (TangentOrientationSection.ofSmoothOrientation oRet).orientation q
            rw [hsuml]
            exact (TangentOrientationSection.ofSmoothOrientation_apply oRet q).symm
          | inr d =>
            change Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three)
                (oSum.val (Sum.inr d)) = (TangentOrientationSection.ofSmoothOrientation oDisc).orientation d
            rw [hsumr]
            exact (TangentOrientationSection.ofSmoothOrientation_apply oDisc d).symm
        refine ⟨(F.mfderivToContinuousLinearEquiv (by simp) x).bijective, ?_⟩
        change Orientation.map (Fin 3) J ((TangentOrientationSection.ofSmoothOrientation oQ).orientation x) = _
        rw [TangentOrientationSection.ofSmoothOrientation_apply]
        apply hh.trans
        convert htarget using 2
        cases F x <;> rfl }
  refine ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, X, rfl, ?_⟩
  apply (X.boundaryFrameReversing_iff_tubeFrame).mpr
  intro b z v w
  exact buffered_boundary_orientation_signed hδ hδ1 f hf hdisj hs hL b o (oE b)
    (A b) (a b) (ha b) (hA b) (hmatched b) z v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
