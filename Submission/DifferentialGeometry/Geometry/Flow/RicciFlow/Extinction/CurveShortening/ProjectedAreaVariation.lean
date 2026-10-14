import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ImmersedPersistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

theorem projection_X_ne_zero_of_angle_sq_lt_one
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ)
    (hs : c.speed g lambda x t ≠ 0) (ha : c.angle g lambda x t ^ 2 < 1) :
    c.projection.X (I := I) x t ≠ 0 := by
  intro hX
  have hspeed : c.speed g lambda x t ^ 2 =
      lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 := by
    rw [speed_sq, inner_X_self, hX]
    simp
  have hmul : c.angle g lambda x t * c.speed g lambda x t =
      lambda * deriv (fun z => c.y z t) x := by
    rw [angle_eq]
    field_simp
  have hsq : (c.angle g lambda x t ^ 2 - 1) * c.speed g lambda x t ^ 2 = 0 := by
    nlinarith [congrArg (fun r : ℝ => r ^ 2) hmul]
  have heq : c.angle g lambda x t ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hsq).resolve_right (pow_ne_zero 2 hs)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_X_ne_zero_of_angle_sq_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_X_ne_zero_of_angle_sq_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_X_ne_zero_of_angle_sq_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_X_ne_zero_of_angle_sq_lt_one

theorem projection_immersedOn_of_angle_sq_lt_one
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) {lambda : ℝ}
    (hlambda : 0 < lambda) {J : Set ℝ} (hi : c.ImmersedOn (I := I) J)
    (ha : ∀ x t, t ∈ J → c.angle g lambda x t ^ 2 < 1) :
    c.projection.ImmersedOn (I := I) J := by
  intro x t ht
  exact projection_X_ne_zero_of_angle_sq_lt_one c g lambda x t
    (speed_pos_of_immersedOn c g lambda hlambda hi x t ht).ne' (ha x t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_immersedOn_of_angle_sq_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_immersedOn_of_angle_sq_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_immersedOn_of_angle_sq_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_immersedOn_of_angle_sq_lt_one

theorem exists_projection_immersedOn_Icc_of_angle_sq_lt_one
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) {lambda a b t : ℝ}
    (hlambda : 0 < lambda) (hc : c.SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : c.ImmersedOn (I := I) (_root_.Set.Icc a b)) (ht : t ∈ _root_.Set.Ico a b)
    (ha : ∀ x, c.angle g lambda x t ^ 2 < 1) :
    ∃ τ, 0 < τ ∧ τ ≤ b - t ∧ c.projection.ImmersedOn (I := I) (_root_.Set.Icc t (t + τ)) := by
  have hsub : _root_.Set.Icc t b ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc_left ht.1
  have hsm : c.projection.SmoothOn (I := I) (_root_.Set.Icc t b) :=
    hc.1.mono (Set.prod_mono (Subset.refl _) hsub)
  refine curveShorteningImmersedPersistence (I := I) (M := M) ht.2 c.projection hsm ?_
  intro x
  exact projection_X_ne_zero_of_angle_sq_lt_one c g lambda x t
    (speed_pos_of_immersedOn c g lambda hlambda hi x t ⟨ht.1, ht.2.le⟩).ne' (ha x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_Icc_of_angle_sq_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_Icc_of_angle_sq_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_Icc_of_angle_sq_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_Icc_of_angle_sq_lt_one

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

namespace ProductCurve

theorem projection_areaError_le_of_abs_angle_le
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J)
    (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (eta : ℝ) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (hu : ∀ x, |c.angle g lambda x t| ≤ eta) :
    c.projection.areaError g J t ≤
      eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.totalCurvature g lambda t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heta_sqrt_pos : 0 < Real.sqrt (1 - eta ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [heta_one, sq_nonneg eta])
  have hpoint : ∀ x, Real.sqrt (c.projection.normSq g
        (c.projection.normalVelocityError g J) x t) *
        c.projection.speed g x t ≤
      eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
        (c.curvature g lambda x t * c.speed g lambda x t) := by
    intro x
    have hNVE := ProductCurve.projection_normalVelocityError c g lambda hlambda hc hi x t ht
    have ha2 : 0 ≤ c.angle g lambda x t ^ 2 := sq_nonneg _
    have hnorm : c.projection.normSq g
        (c.projection.normalVelocityError g J) x t =
        (c.angle g lambda x t ^ 2) ^ 2 * c.projection.curvatureSq g x t := by
      dsimp only [CurveMap.normSq, CurveMap.curvatureSq]
      rw [hNVE]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hsqrt : Real.sqrt (c.projection.normSq g
          (c.projection.normalVelocityError g J) x t) =
        c.angle g lambda x t ^ 2 * c.projection.curvature g x t := by
      rw [hnorm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
      rfl
    have hhpos : 0 < c.horizontalSpeedFraction g lambda x t :=
      ProductCurve.horizontalSpeedFraction_pos c g lambda hlambda hi x t ht
    have hpsp : c.projection.speed g x t =
        c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t :=
      ProductCurve.projection_speed_eq c g lambda hlambda hi x t ht
    have h1 : c.projection.curvature g x t *
        (c.horizontalSpeedFraction g lambda x t *
          c.horizontalSpeedFraction g lambda x t) ≤
        c.curvature g lambda x t := by
      nlinarith [ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le
        c g lambda hlambda hc hi x t ht]
    have hAk : c.angle g lambda x t ^ 2 *
        c.projection.curvature g x t *
        (c.horizontalSpeedFraction g lambda x t *
          c.horizontalSpeedFraction g lambda x t) ≤
        c.angle g lambda x t ^ 2 * c.curvature g lambda x t := by
      nlinarith [mul_le_mul_of_nonneg_left h1 ha2]
    have heta_sq_nonneg : 0 ≤ eta ^ 2 := sq_nonneg eta
    have hh_ge : Real.sqrt (1 - eta ^ 2) ≤
        c.horizontalSpeedFraction g lambda x t := by
      rw [ProductCurve.horizontalSpeedFraction]
      refine Real.sqrt_le_sqrt ?_
      have h2 : c.angle g lambda x t ^ 2 ≤ eta ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) heta).2 (hu x)
      linarith
    have hAh : c.angle g lambda x t ^ 2 ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          c.horizontalSpeedFraction g lambda x t := by
      have h2 : c.angle g lambda x t ^ 2 ≤ eta ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) heta).2 (hu x)
      have h3 : 1 ≤ c.horizontalSpeedFraction g lambda x t /
          Real.sqrt (1 - eta ^ 2) := (one_le_div heta_sqrt_pos).mpr hh_ge
      have h4 : eta ^ 2 ≤ eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          c.horizontalSpeedFraction g lambda x t := by
        calc eta ^ 2 = eta ^ 2 * 1 := by ring
          _ ≤ eta ^ 2 * (c.horizontalSpeedFraction g lambda x t /
              Real.sqrt (1 - eta ^ 2)) := mul_le_mul_of_nonneg_left h3 heta_sq_nonneg
          _ = eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
              c.horizontalSpeedFraction g lambda x t := by ring
      linarith
    have hAC : c.angle g lambda x t ^ 2 * c.curvature g lambda x t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          (c.curvature g lambda x t * c.horizontalSpeedFraction g lambda x t) := by
      have h := mul_le_mul_of_nonneg_right hAh
        (c.curvature_nonneg g lambda x t)
      nlinarith [h]
    have hfin : c.angle g lambda x t ^ 2 *
        c.projection.curvature g x t *
        c.horizontalSpeedFraction g lambda x t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          c.curvature g lambda x t := by
      refine le_of_mul_le_mul_right ?_ hhpos
      nlinarith [hAk.trans hAC]
    rw [hsqrt, hpsp]
    calc c.angle g lambda x t ^ 2 * c.projection.curvature g x t *
          (c.horizontalSpeedFraction g lambda x t *
            c.speed g lambda x t)
        = (c.angle g lambda x t ^ 2 * c.projection.curvature g x t *
            c.horizontalSpeedFraction g lambda x t) *
              c.speed g lambda x t := by ring
      _ ≤ (eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            c.curvature g lambda x t) * c.speed g lambda x t :=
        mul_le_mul_of_nonneg_right hfin
          (c.speed_nonneg g lambda x t)
      _ = eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          (c.curvature g lambda x t * c.speed g lambda x t) := by ring
  have hint : IntervalIntegrable
      (fun x => c.curvature g lambda x t * c.speed g lambda x t)
      volume 0 1 :=
    ProductCurve.curvature_mul_speed_integrable c g lambda hlambda hc hi t ht
  have hintC : _root_.MeasureTheory.Integrable
      (fun x => eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
        (c.curvature g lambda x t * c.speed g lambda x t))
      (volume.restrict (_root_.Set.Ioc (0 : ℝ) 1)) := hint.1.const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (_root_.Set.Ioc (0 : ℝ) 1)]
      (fun x => Real.sqrt (c.projection.normSq g
        (c.projection.normalVelocityError g J) x t) *
        c.projection.speed g x t) :=
    _root_.MeasureTheory.ae_of_all _ (fun x => mul_nonneg (Real.sqrt_nonneg _)
      (c.projection.speed_nonneg g x t))
  have hle := MeasureTheory.integral_mono_of_nonneg hnn hintC (_root_.MeasureTheory.ae_of_all _ hpoint)
  rw [MeasureTheory.integral_const_mul] at hle
  simpa only [CurveMap.areaError, CurveMap.integral, ProductCurve.totalCurvature,
    ProductCurve.integral, intervalIntegral.integral_of_le zero_le_one] using hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_areaError_le_of_abs_angle_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_areaError_le_of_abs_angle_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_areaError_le_of_abs_angle_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_areaError_le_of_abs_angle_le

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

theorem exists_projection_immersedOn_areaError_le
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    {lambda a b t eta : ℝ} (hlambda : 0 < lambda)
    (hc : c.IsSolutionOn g lambda (_root_.Set.Icc a b)) (ht : t ∈ _root_.Set.Ico a b)
    (heta : 0 ≤ eta) (heta_one : eta < 1)
    (hu : ∀ x, |c.angle g lambda x t| ≤ eta) :
    ∃ τ, 0 < τ ∧ τ ≤ b - t ∧
      c.projection.ImmersedOn (I := I) (_root_.Set.Icc t (t + τ)) ∧
      c.projection.areaError g (_root_.Set.Icc t (t + τ)) t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.totalCurvature g lambda t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have ha : ∀ x, c.angle g lambda x t ^ 2 < 1 := by
    intro x
    have hangle := abs_le.mp (hu x)
    have hsq : c.angle g lambda x t ^ 2 ≤ eta ^ 2 := by
      nlinarith [hangle.1, hangle.2]
    nlinarith [hsq, heta, heta_one]
  obtain ⟨τ, hτ, hτb, hi⟩ :=
    c.exists_projection_immersedOn_Icc_of_angle_sq_lt_one g hlambda hc.smooth hc.immersed ht ha
  have hsol : c.IsSolutionOn g lambda (_root_.Set.Icc t (t + τ)) :=
    hc.mono_Icc ht.1 (by linarith) (by linarith)
  refine ⟨τ, hτ, hτb, hi, ?_⟩
  exact c.projection_areaError_le_of_abs_angle_le g lambda hlambda hsol hi t
    ⟨le_rfl, by linarith⟩ eta heta heta_one hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_areaError_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_areaError_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_areaError_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_projection_immersedOn_areaError_le

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem inner_congr_of_base_eq (g : SmoothRiemannianMetric I M) {a b : M}
    {v w : TangentSpace I a} {v' w' : TangentSpace I b}
    (hab : a = b) (hv : v = v') (hw : w = w') :
    g.inner a v w = g.inner b v' w' := by
  subst hab
  rw [hv, hw]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.inner_congr_of_base_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.inner_congr_of_base_eq target :: scope.openDecls } }

theorem normalVelocityError_congr {c d : CurveMap M}
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (h : ∀ z t, t ∈ J → c z t = d z t) (x t : ℝ) (ht : t ∈ J) :
    c.normalVelocityError g J x t = d.normalVelocityError g J x t := by
  have hbase : c.lift x t = d.lift x t := h (x : Surgery.Topology.Circle) t ht
  have hslice : ∀ y : ℝ, c.lift y t = d.lift y t :=
    fun y => h (y : Surgery.Topology.Circle) t ht
  have hv : c.velocity (I := I) J x t = d.velocity (I := I) J x t :=
    velocity_congr (fun y s hs => h (y : Surgery.Topology.Circle) s hs) ht
  have hcv : c.curvatureVector g x t = d.curvatureVector g x t :=
    curvatureVector_congr hslice x
  have hX : c.X (I := I) x t = d.X (I := I) x t := X_congr hslice x
  have hspeed : c.speed g x t = d.speed g x t :=
    congrArg Real.sqrt (inner_congr_of_base_eq (g t) hbase hX hX)
  have hT : c.unitTangent g x t = d.unitTangent g x t := by
    simp only [unitTangent, hspeed, hX]
    rfl
  have hW : c.velocity (I := I) J x t - c.curvatureVector g x t =
      d.velocity (I := I) J x t - d.curvatureVector g x t := congrArg₂ (· - ·) hv hcv
  have hi := inner_congr_of_base_eq (g t) hbase hW hT
  dsimp only [normalVelocityError]
  rw [hi, hW, hT]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normalVelocityError_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normalVelocityError_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normalVelocityError_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normalVelocityError_congr

theorem areaError_congr {c d : CurveMap M}
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (h : ∀ z t, t ∈ J → c z t = d z t) (t : ℝ) (ht : t ∈ J) :
    c.areaError g J t = d.areaError g J t := by
  unfold areaError integral
  apply intervalIntegral.integral_congr
  intro x _
  have hbase : c.lift x t = d.lift x t := h (x : Surgery.Topology.Circle) t ht
  have hX : c.X (I := I) x t = d.X (I := I) x t :=
    X_congr (fun y => h (y : Surgery.Topology.Circle) t ht) x
  have he := normalVelocityError_congr (g := g) h x t ht
  have hnorm := inner_congr_of_base_eq (g t) hbase he he
  have hinnerX := inner_congr_of_base_eq (g t) hbase hX hX
  simp only [normSq, speed, hnorm, hinnerX]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_congr

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
