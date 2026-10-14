import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Curvature.Product
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : PointedFlowData.{u, uE, uH} I ancientTimeInterval}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension target :: scope.openDecls } }

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cyl" => S2 × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

namespace ShrinkingCylinderCover

theorem metric_inner_eq_sub_two_mul_ricci
    (C : ShrinkingCylinderCover F) (t : ℝ) (ht : t ≤ 0)
    (x : F.M) (v w : TangentSpace I x) :
    (F.S.base.metric t).inner x v w =
      (F.S.base.metric 0).inner x v w -
        2 * t * ricciTensor (F.S.base.metric 0) x v w := by
  let g0 : SmoothRiemannianMetric CI Cyl :=
    (scaleMetric (2 * C.extinctionTime)
      (mul_pos (by norm_num) C.extinctionTime_pos) gS).prod (euclideanMetric (E := ℝ))
  have hpull : localPullMetric (F.S.base.metric 0) C.projection C.projection_local = g0 := by
    apply SmoothRiemannianMetric.ext_inner
    rintro ⟨y, s⟩ ⟨a, b⟩ ⟨c, d⟩
    erw [localPullMetric_inner]
    calc
      _ = (2 * C.extinctionTime) * (gS).inner y a c + b * d := by
        have hh := C.projection_metric 0 le_rfl y s a c b d
        change (F.S.base.metric 0).inner (C.projection (y, s))
          (mfderiv CI I C.projection (y, s) (a, b))
          (mfderiv CI I C.projection (y, s) (c, d)) = _ at hh
        simpa only [sub_zero] using hh
      _ = g0.inner (y, s) (a, b) (c, d) := by
        dsimp only [g0]
        erw [SmoothRiemannianMetric.prod_inner, scaleMetric_inner]
        change (2 * C.extinctionTime) * (gS).inner y a c + b * d =
          (2 * C.extinctionTime) * (gS).inner y a c + _root_.Inner.inner ℝ b d
        rw [Real.inner_apply]
  have hricci (z : Cyl) (a b : TangentSpace CI z) :
      ricciTensor (F.S.base.metric 0) (C.projection z)
          (mfderiv CI I C.projection z a) (mfderiv CI I C.projection z b) =
        (gS).inner z.1 a.1 b.1 := by
    rw [← ricciTensor_localPull (F.S.base.metric 0) C.projection C.projection_local z a b,
      hpull]
    change ricciTensor ((scaleMetric (2 * C.extinctionTime)
      (mul_pos (by norm_num) C.extinctionTime_pos) gS).prod (euclideanMetric (E := ℝ))) z a b = _
    rw [ricciTensor_productMetric]
    erw [ricciTensor_scaleMetric, roundMetric_ricciTensor, euclideanMetric_ricciTensor]
    norm_num
  obtain ⟨z, rfl⟩ := C.surjective x
  let d := C.projection_local.mfderivToContinuousLinearEquiv
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) z
  obtain ⟨a, ha⟩ := d.surjective v
  obtain ⟨b, hb⟩ := d.surjective w
  have hda : mfderiv CI I C.projection z a = v := by
    have hcoe := C.projection_local.mfderivToContinuousLinearEquiv_coe
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) z
    exact (congrArg (fun f => f a) hcoe).symm.trans ha
  have hdb : mfderiv CI I C.projection z b = w := by
    have hcoe := C.projection_local.mfderivToContinuousLinearEquiv_coe
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) z
    exact (congrArg (fun f => f b) hcoe).symm.trans hb
  change (F.S.base.metric t).inner (C.projection z) v w =
    (F.S.base.metric 0).inner (C.projection z) v w -
      2 * t * ricciTensor (F.S.base.metric 0) (C.projection z) v w
  rw [← hda, ← hdb, hricci]
  have htensor := C.projection_metric t ht z.1 z.2 a.1 b.1 a.2 b.2
  have hzero := C.projection_metric 0 le_rfl z.1 z.2 a.1 b.1 a.2 b.2
  change (F.S.family.metric t).inner (C.projection z)
      (mfderiv CI I C.projection z a) (mfderiv CI I C.projection z b) =
    (F.S.family.metric 0).inner (C.projection z)
      (mfderiv CI I C.projection z a) (mfderiv CI I C.projection z b) -
      2 * t * (gS).inner z.1 a.1 b.1
  erw [htensor, hzero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metric_inner_eq_sub_two_mul_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metric_inner_eq_sub_two_mul_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metric_inner_eq_sub_two_mul_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metric_inner_eq_sub_two_mul_ricci

end ShrinkingCylinderCover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
