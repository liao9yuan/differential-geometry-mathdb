import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialBoundaryOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Module _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
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
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Ball target :: scope.openDecls } }
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
private abbrev E1 := EuclideanSpace ℝ (Fin 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E1 target :: scope.openDecls } }
private abbrev ER := E2 × E1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.ER
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.ER target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.IR target :: scope.openDecls } }
private abbrev Collar (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Collar target :: scope.openDecls } }
private def b2 : _root_.Module.Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.b2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.b2 target :: scope.openDecls } }
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.i2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.i2 target :: scope.openDecls } }
private def i3 : Fin 3 ≃ Fin (Module.finrank ℝ E3) := finCongr (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.i3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.i3 target :: scope.openDecls } }
private def iR : Fin 3 ≃ Fin (Module.finrank ℝ ER) := finCongr (by simp [ER, E2, E1])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.iR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.iR target :: scope.openDecls } }
private def collarDerivative {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    Collar B → ER ≃L[ℝ] E3 := by
  let := halfClosedIntervalChartedSpace hB
  exact differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L B)
    (radialCollarOrientationMap_mfderiv_bijective hL hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.collarDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.collarDerivative target :: scope.openDecls } }

def radialCollarTangentOrientationThree {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := halfClosedIntervalChartedSpace hB
    Collar B → Orientation ℝ ER (Fin 3) := by
  let := halfClosedIntervalChartedSpace hB
  exact fun q => Orientation.map (Fin 3) (collarDerivative hL hB q).symm.toLinearEquiv o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree

theorem radialCollarTangentOrientationThree_eq {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    ∀ q : Collar B, Orientation.reindex ℝ ER iR (radialCollarTangentOrientationThree hL hB o q) =
      (radialCollarSmoothOrientation hL hB (Orientation.reindex ℝ E3 i3 o)).val q := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  intro q
  change Orientation.reindex ℝ ER iR (Orientation.map (Fin 3) (collarDerivative hL hB q).symm.toLinearEquiv o) =
    tangentOrientationEquiv (collarDerivative hL hB q).symm.toLinearEquiv (Orientation.reindex ℝ E3 i3 o)
  induction o using Module.Ray.ind
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree_eq ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarTangentOrientationThree_eq

theorem retainedFaceInclusion_contMDiff {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    ContMDiff (𝓡 2) IR ∞ (Subtype.val : retainedFace B → Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let z : _root_.Set.Ico (0 : ℝ) B := ⟨0, le_rfl, hB⟩
  have he : (Subtype.val : retainedFace B → Collar B) =
      (fun q => ((retainedFaceDiffeomorph hB).symm q, z)) := by
    funext q
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact q.property
  rw [he]
  exact (retainedFaceDiffeomorph hB).symm.contMDiff.prodMk
    (show ContMDiff (𝓡 2) (𝓡∂ 1) ∞ (fun _ : retainedFace B => z) from contMDiff_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceInclusion_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceInclusion_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceInclusion_contMDiff ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceInclusion_contMDiff

def retainedFaceIntrinsicFrame {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    retainedFace B → (ℝ × E2) ≃ₗ[ℝ] ER := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact fun q => (hypersurfaceNormalFrameEquiv (retainedFaceAmbientMap L B)
    (retainedFaceOutwardNormal B) (retainedFaceNormalFrame_bijective hL hB) q).toLinearEquiv.trans
      (collarDerivative hL hB q.val).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame
private def faceInclusionDerivative {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    retainedFace B → E2 →L[ℝ] ER := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  exact fun q => mfderiv (𝓡 2) IR (Subtype.val : retainedFace B → Collar B) q

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.faceInclusionDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.faceInclusionDerivative target :: scope.openDecls } }
private def faceAmbientDerivative {L B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    retainedFace B → E2 →L[ℝ] E3 := by
  let := retainedFaceChartedSpace hB
  exact fun q => mfderiv (𝓡 2) (𝓡 3) (retainedFaceAmbientMap L B) q

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.faceAmbientDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.faceAmbientDerivative target :: scope.openDecls } }
private theorem face_inclusion_chain {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    ∀ q : retainedFace B, faceAmbientDerivative (L := L) hB q =
      (collarDerivative hL hB q.val : ER →L[ℝ] E3).comp (faceInclusionDerivative hB q) := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  intro q
  exact mfderiv_comp q ((radialCollarOrientationMap_isSmoothEmbedding hL hB).contMDiff.mdifferentiableAt (by simp))
    ((retainedFaceInclusion_contMDiff hB).mdifferentiableAt (by simp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.face_inclusion_chain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.face_inclusion_chain target :: scope.openDecls } }

theorem retainedFaceIntrinsicFrame_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace B, ∀ t : ℝ, ∀ v : E2,
      let D : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (Subtype.val : retainedFace B → Collar B) q
      retainedFaceIntrinsicFrame hL hB q (t,v) =
        t • (differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L B)
          (radialCollarOrientationMap_mfderiv_bijective hL hB) q.val).symm (retainedFaceOutwardNormal B q) + D v := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro q t v
  change (collarDerivative hL hB q.val).symm
    (t • retainedFaceOutwardNormal B q + faceAmbientDerivative (L := L) hB q v) =
      t • (collarDerivative hL hB q.val).symm (retainedFaceOutwardNormal B q) + faceInclusionDerivative hB q v
  rw [map_add, map_smul, face_inclusion_chain hL hB q]
  change t • (collarDerivative hL hB q.val).symm (retainedFaceOutwardNormal B q) +
    (collarDerivative hL hB q.val).symm ((collarDerivative hL hB q.val) (faceInclusionDerivative hB q v)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame_apply ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceIntrinsicFrame_apply

theorem retainedFaceSmoothOrientation_induced {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace B, (retainedFaceSmoothOrientation hL hB o).val q = Orientation.reindex ℝ E2 i2
      (normalFirstOrientation (retainedFaceIntrinsicFrame hL hB q) b2
        (radialCollarTangentOrientationThree hL hB o q.val)) := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro q
  rw [retainedFaceSmoothOrientation_apply]
  have h := normalFirstOrientation_map
    (hypersurfaceNormalFrameEquiv (retainedFaceAmbientMap L B) (retainedFaceOutwardNormal B)
      (retainedFaceNormalFrame_bijective hL hB) q).toLinearEquiv
    (collarDerivative hL hB q.val).symm.toLinearEquiv b2 o
  exact congrArg (Orientation.reindex ℝ E2 i2) h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceSmoothOrientation_induced then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceSmoothOrientation_induced"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceSmoothOrientation_induced ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedFaceSmoothOrientation_induced
end DifferentialGeometry.Topology.Manifold.Attachment
