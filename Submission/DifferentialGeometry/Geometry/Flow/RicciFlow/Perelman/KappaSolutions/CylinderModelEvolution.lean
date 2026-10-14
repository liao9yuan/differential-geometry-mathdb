import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.AffinePullback
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension target :: scope.openDecls } }

theorem doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric :
    doubleSphereCylinderMetric = roundThreeCylinderShrinkerMetric := by
  have hsphere : roundTwoSphereShrinkerMetric =
      scaleMetric 2 (by norm_num) (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
      roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
    norm_num
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, s⟩ ⟨v, a⟩ ⟨w, b⟩
  erw [doubleSphereCylinderMetric_inner, roundThreeCylinderShrinkerMetric, hsphere,
    SmoothRiemannianMetric.prod_inner, scaleMetric_inner]
  change _ = _ + _root_.Inner.inner ℝ a b
  rw [Real.inner_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric

theorem doubleSphereCylinderMetric_eq_roundCylinderMetric :
    doubleSphereCylinderMetric =
      Geometry.Metric.roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2) := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, s⟩ ⟨v, a⟩ ⟨w, b⟩
  erw [doubleSphereCylinderMetric_inner, Geometry.Metric.roundCylinderMetric_inner,
    roundMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.doubleSphereCylinderMetric_eq_roundCylinderMetric

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]

theorem localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci
    (g g₀ : SmoothRiemannianMetric J M) {t : ℝ}
    (hflow : ∀ x : M, ∀ v w : TangentSpace J x,
      g.inner x v w = g₀.inner x v w - 2 * t * ricciTensor g₀ x v w)
    (j : SpatialNeckCylinder → M) (hj : IsLocalDiffeomorph SpatialNeckCylinderModel J ∞ j)
    (hzero : localPullMetric g₀ j hj = roundThreeCylinderShrinkerMetric)
    (ht : t < 1) :
    localPullMetric g j hj = scalarOneShrinkingCylinderMetric t ht := by
  have hsphere : roundTwoSphereShrinkerMetric =
      scaleMetric 2 (by norm_num) (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
      roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
    norm_num
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, s⟩ ⟨v, a⟩ ⟨w, b⟩
  erw [localPullMetric_inner, hflow]
  erw [← localPullMetric_inner g₀ j hj,
    ← ricciTensor_localPull g₀ j hj, hzero]
  erw [roundThreeCylinderShrinkerMetric, hsphere, SmoothRiemannianMetric.prod_inner,
    scaleMetric_inner, ricciTensor_productMetric, ricciTensor_scaleMetric,
    roundMetric_ricciTensor, euclideanMetric_ricciTensor,
    scalarOneShrinkingCylinderMetric_inner]
  change 2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
      _root_.Inner.inner ℝ a b - 2 * t *
        (((2 : ℝ) - 1) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + 0) = _
  rw [Real.inner_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci

theorem localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci
    (g : ℝ → SmoothRiemannianMetric J M)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : M, ∀ v w : TangentSpace J x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w)
    (j : SpatialNeckCylinder → M) (hj : IsLocalDiffeomorph SpatialNeckCylinderModel J ∞ j)
    (hzero : localPullMetric (g 0) j hj = roundThreeCylinderShrinkerMetric)
    (t : ℝ) (ht : t ≤ 0) :
    localPullMetric (g t) j hj = scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  exact localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci
    (g t) (g 0) (hflow t ht) j hj hzero (ht.trans_lt (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci

theorem eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci
    (g g₀ : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder) {t : ℝ}
    (hflow : ∀ x : SpatialNeckCylinder, ∀ v w : TangentSpace SpatialNeckCylinderModel x,
      g.inner x v w = g₀.inner x v w - 2 * t * ricciTensor g₀ x v w)
    (hzero : g₀ = doubleSphereCylinderMetric) (ht : t < 1) :
    g = scalarOneShrinkingCylinderMetric t ht := by
  have hs := localPullMetric_eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci
    g g₀ hflow (Diffeomorph.refl SpatialNeckCylinderModel SpatialNeckCylinder ∞)
    (Diffeomorph.refl SpatialNeckCylinderModel SpatialNeckCylinder ∞).isLocalDiffeomorph
    (by
      rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric,
        Diffeomorph.pullbackMetricCross_refl, hzero,
        doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric]) ht
  rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    Diffeomorph.pullbackMetricCross_refl] at hs
  exact hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci

theorem eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci_of_roundCylinderMetric
    (g : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder) {t : ℝ}
    (hflow : ∀ x : SpatialNeckCylinder, ∀ v w : TangentSpace SpatialNeckCylinderModel x,
      g.inner x v w =
        (Geometry.Metric.roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w -
          2 * t * ricciTensor
            (Geometry.Metric.roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x v w)
    (ht : t < 1) :
    g = scalarOneShrinkingCylinderMetric t ht :=
  eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci g _ hflow
    doubleSphereCylinderMetric_eq_roundCylinderMetric.symm ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci_of_roundCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci_of_roundCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci_of_roundCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci_of_roundCylinderMetric

theorem pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci
    (g : ℝ → SmoothRiemannianMetric J M)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : M, ∀ v w : TangentSpace J x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w)
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, J⟯ M)
    (hzero : Diffeomorph.pullbackMetricCross (g 0) d = roundThreeCylinderShrinkerMetric)
    (t : ℝ) (ht : t ≤ 0) :
    Diffeomorph.pullbackMetricCross (g t) d =
      scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric] at hzero ⊢
  exact localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci g hflow d
    d.isLocalDiffeomorph hzero t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci

theorem pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci
    (g : ℝ → SmoothRiemannianMetric J M)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : M, ∀ v w : TangentSpace J x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w)
    (d : DifferentialGeometry.Geometry.CylinderDiagonalQuotient ≃ₘ⟮SpatialNeckCylinderModel, J⟯ M)
    (hzero : Diffeomorph.pullbackMetricCross (g 0) d = cylinderDiagonalQuotientMetric)
    (t : ℝ) (ht : t ≤ 0) :
    localPullMetric (Diffeomorph.pullbackMetricCross (g t) d) cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph =
        scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  let h := fun s => Diffeomorph.pullbackMetricCross (g s) d
  have hflow' : ∀ s : ℝ, s ≤ 0 → ∀ x, ∀ v w : TangentSpace SpatialNeckCylinderModel x,
      (h s).inner x v w = (h 0).inner x v w - 2 * s * ricciTensor (h 0) x v w := by
    intro s hs x v w
    exact pullback_metric_inner_eq_sub_two_mul_ricci g hflow d (h 0) rfl s hs x v w
  have hzero' : localPullMetric (h 0) cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph = roundThreeCylinderShrinkerMetric := by
    change localPullMetric (Diffeomorph.pullbackMetricCross (g 0) d) _ _ = _
    rw [hzero, localPullMetric_cylinderDiagonalQuotientMetric]
  exact localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci h hflow'
    cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph hzero' t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci

theorem pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci
    (g : ℝ → SmoothRiemannianMetric J M)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : M, ∀ v w : TangentSpace J x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w)
    (d : CylinderAntipodalQuotient ≃ₘ⟮SpatialNeckCylinderModel, J⟯ M)
    (hzero : Diffeomorph.pullbackMetricCross (g 0) d = cylinderAntipodalQuotientMetric)
    (t : ℝ) (ht : t ≤ 0) :
    localPullMetric (Diffeomorph.pullbackMetricCross (g t) d) cylinderAntipodalQuotientMap
      cylinderAntipodalQuotientMap_isLocalDiffeomorph =
        scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  let h := fun s => Diffeomorph.pullbackMetricCross (g s) d
  have hflow' : ∀ s : ℝ, s ≤ 0 → ∀ x, ∀ v w : TangentSpace SpatialNeckCylinderModel x,
      (h s).inner x v w = (h 0).inner x v w - 2 * s * ricciTensor (h 0) x v w := by
    intro s hs x v w
    exact pullback_metric_inner_eq_sub_two_mul_ricci g hflow d (h 0) rfl s hs x v w
  have hzero' : localPullMetric (h 0) cylinderAntipodalQuotientMap
      cylinderAntipodalQuotientMap_isLocalDiffeomorph = roundThreeCylinderShrinkerMetric := by
    change localPullMetric (Diffeomorph.pullbackMetricCross (g 0) d) _ _ = _
    rw [hzero, localPullMetric_cylinderAntipodalQuotientMetric]
  exact localPullMetric_eq_shrinkingCylinderMetric_of_affine_ricci h hflow'
    cylinderAntipodalQuotientMap cylinderAntipodalQuotientMap_isLocalDiffeomorph hzero' t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
