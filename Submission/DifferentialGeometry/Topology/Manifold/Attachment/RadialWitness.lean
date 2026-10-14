import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.IsManifold _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Handle _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E2 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.S2 target :: scope.openDecls } }
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Cap target :: scope.openDecls } }
private abbrev Retained (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Retained target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }

abbrev retainedFace (B : ℝ) := {q : Retained B // q.2.val = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFace ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFace

def retainedFaceHomeomorph {B : ℝ} (hB : 0 < B) : S2 ≃ₜ retainedFace B where
  toFun y := ⟨retainedBoundary hB y, rfl⟩
  invFun q := q.val.1
  left_inv _ := rfl
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact q.property.symm
  continuous_toFun := Continuous.subtype_mk (continuous_id.prodMk continuous_const) _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceHomeomorph

@[reducible] def retainedFaceChartedSpace {B : ℝ} (hB : 0 < B) :
    ChartedSpace E2 (retainedFace B) :=
  chartedSpaceOfHomeomorph (M := S2) (retainedFaceHomeomorph hB).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceChartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceChartedSpace

theorem retainedFace_isManifold {B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    IsManifold (𝓡 2) ∞ (retainedFace B) := by
  let := retainedFaceChartedSpace hB
  exact @isManifoldOfHomeomorph ℝ _ E2 E2 _ _ _ (𝓡 2) S2 _
    inferInstance ∞ (retainedFace B) _ (retainedFaceHomeomorph hB).symm inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFace_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFace_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFace_isManifold ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFace_isManifold

def retainedFaceDiffeomorph {B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ retainedFace B := by
  let := retainedFaceChartedSpace hB
  let e := retainedFaceHomeomorph hB
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e.symm (𝓡 2) ∞
      contMDiff_invFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e.symm (𝓡 2) ∞ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceDiffeomorph

def radialCapGluingDiffeomorph {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    letI := retainedFaceChartedSpace hB
    BoundaryManifold (𝓡∂ 3) (Cap L) ≃ₘ⟮𝓡 2, 𝓡 2⟯ retainedFace B := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let := retainedFaceChartedSpace hB
  exact (closedBallBoundaryDiffeomorph hL).trans (retainedFaceDiffeomorph hB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph

theorem radialCapGluingDiffeomorph_coherence {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    letI := retainedFaceChartedSpace hB
    ∀ b : BoundaryManifold (𝓡∂ 3) (Cap L),
      adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) b.val =
        adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)
          (radialCapGluingDiffeomorph hL hB b).val := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let := retainedFaceChartedSpace hB
  intro b
  have hb : radialCapBoundary hL (closedBallBoundaryDiffeomorph hL b) = b.val := by
    apply Subtype.ext
    change L • (L⁻¹ • b.val.val) = b.val.val
    simp [smul_smul, hL.ne']
  have h := adjunction_coherence (radialCapBoundary hL) (retainedBoundary hB)
    (closedBallBoundaryDiffeomorph hL b)
  rw [hb] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph_coherence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph_coherence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph_coherence ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapGluingDiffeomorph_coherence

theorem radialCapAttachment_inclusions_cover {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    _root_.Set.range (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB)) ∪
      range (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  induction p using Quot.inductionOn with
  | h q =>
    rcases q with x | y
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨y, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_cover ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_cover

theorem radialCapAttachment_cap_eq_retained_iff {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Cap L) (q : Retained B) :
    adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x =
      adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) q ↔
      x = radialCapBoundary hL q.1 ∧ q.2.val = 0 := by
  constructor
  · intro he
    have hr := congrArg (fun p => (radialCapAttachmentHomeomorph hL hB p : E3)) he
    change x.val = (L + q.2.val) • q.1.val at hr
    have hn := x.property
    rw [hr, norm_smul, Real.norm_eq_abs,
      abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one] at hn
    have hzero : q.2.val = 0 := le_antisymm (by linarith) q.2.property.1
    refine ⟨?_, hzero⟩
    apply Subtype.ext
    change x.val = L • q.1.val
    simpa only [hzero, add_zero] using hr
  · rintro ⟨hx, hq⟩
    have he : retainedBoundary hB q.1 = q := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact hq.symm
    rw [hx, ← he]
    exact adjunction_coherence (radialCapBoundary hL) (retainedBoundary hB) q.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_cap_eq_retained_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_cap_eq_retained_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_cap_eq_retained_iff ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_cap_eq_retained_iff

theorem radialCapAttachment_inclusions_inter {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    _root_.Set.range (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB)) ∩
        range (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) =
      range (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) ∘ radialCapBoundary hL) := by
  ext p
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨q, hq⟩⟩
    have he := (radialCapAttachment_cap_eq_retained_iff hL hB x q).mp (hx.trans hq.symm)
    exact ⟨q.1, by change adjunctionCell _ _ (radialCapBoundary hL q.1) = p; rw [← he.1]; exact hx⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨radialCapBoundary hL y, rfl⟩,
      ⟨retainedBoundary hB y, (adjunction_coherence (radialCapBoundary hL) (retainedBoundary hB) y).symm⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_inter ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_inclusions_inter

theorem radialCapAttachment_tip_interior {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    let x : Cap L := ⟨0, by simpa using hL.le⟩
    x ∉ (𝓡∂ 3).boundary (Cap L) ∧
      adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x ∉
        range (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) := by
  let := closedBallChartedSpace hL
  let x : Cap L := ⟨0, by simpa using hL.le⟩
  constructor
  · rw [closedBall_boundary_eq_sphere hL]
    change ¬ ‖(0 : E3)‖ = L
    simpa only [norm_zero] using ne_of_lt hL
  · rintro ⟨q, hq⟩
    have he := (radialCapAttachment_cap_eq_retained_iff hL hB x q).mp hq.symm
    have hn := congrArg (fun y : Cap L => ‖y.val‖) he.1
    change ‖(0 : E3)‖ = ‖L • q.1.val‖ at hn
    rw [norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hL,
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one] at hn
    exact hL.ne' hn.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_tip_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_tip_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_tip_interior ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_tip_interior

end DifferentialGeometry.Topology.Manifold.Attachment
