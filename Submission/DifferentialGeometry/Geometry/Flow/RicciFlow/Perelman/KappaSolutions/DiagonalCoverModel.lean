import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCoverScalarNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
open private exists_diffeomorph_orbitQuotient from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance diagonalCoverSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diagonalCoverSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diagonalCoverSphereDimension target :: scope.openDecls } }

theorem ShrinkingCylinderCover.exists_diagonal_shrinking_model
    (P : PointedFlowData.{u, 0, 0} ThreeModel ancientTimeInterval)
    (C : ShrinkingCylinderCover P) (hdiagonal : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) :
    ∃ d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮SpatialNeckCylinderModel, ThreeModel⟯ P.M,
      (∀ p : SpatialNeckCylinder, d (cylinderDiagonalQuotientMap p) = C.projection p) ∧
      ∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (P.S.base.metric t) d)
          cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  obtain ⟨d0, hd0⟩ := hdiagonal.1
  obtain ⟨e, he⟩ := exists_diffeomorph_orbitQuotient
  let d := e.symm.trans d0
  have hprojection (p : SpatialNeckCylinder) :
      d (cylinderDiagonalQuotientMap p) = C.projection p := by
    change d0 (e.symm (cylinderDiagonalQuotientMap p)) = C.projection p
    rw [← he p, e.symm_apply_apply]
    exact hd0 p
  have hcomp : (d : Geometry.CylinderDiagonalQuotient → P.M) ∘
      cylinderDiagonalQuotientMap = C.projection := funext hprojection
  refine ⟨d, hprojection, ?_⟩
  intro t ht
  have hmetric : localPullMetric (P.S.base.metric t) C.projection C.projection_local =
      scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z V W
    have hpull := localPullMetric_inner (P.S.base.metric t) C.projection C.projection_local z V W
    have hh := C.projection_metric t ht z.1 z.2 V.1 W.1 V.2 W.2
    rw [C.extinctionTime_eq_one_of_scalar_at_base_one hbase] at hh
    exact hpull.trans (hh.trans (scalarOneShrinkingCylinderMetric_inner t _ z.1 z.2 V.1 W.1 V.2 W.2).symm)
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  have hcompose := localPullMetric_comp (P.S.base.metric t) d cylinderDiagonalQuotientMap
    d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph
    (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
  rw [hcompose]
  simpa only [hcomp] using hmetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_diagonal_shrinking_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_diagonal_shrinking_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_diagonal_shrinking_model ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_diagonal_shrinking_model

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
