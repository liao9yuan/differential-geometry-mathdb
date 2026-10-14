import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import Submission.DifferentialGeometry.Geometry.Metric.AddCircle
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.AddCircle
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothImmersion

omit [IsManifold I ∞ M] in
theorem contMDiff_map (c₀ : SmoothImmersion (I := I) (M := M)) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ c₀.map := by
  apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
    QuotientAddGroup.mk_surjective
  change ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => c₀.map (x : AddCircle (1 : ℝ)))
  exact c₀.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.contMDiff_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.contMDiff_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.contMDiff_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.contMDiff_map

omit [IsManifold I ∞ M] in
theorem mfderiv_map_parameterTangent (c₀ : SmoothImmersion (I := I) (M := M)) (x : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I c₀.map (x : AddCircle (1 : ℝ))
      (AddCircle.parameterTangent (x : AddCircle (1 : ℝ))) =
      mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ))) x (1 : ℝ) := by
  exact (AddCircle.mfderiv_comp_coe
    (c₀.contMDiff_map.mdifferentiableAt (by simp))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.mfderiv_map_parameterTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.mfderiv_map_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.mfderiv_map_parameterTangent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.mfderiv_map_parameterTangent

omit [IsManifold I ∞ M] in
theorem injective_mfderiv_map (c₀ : SmoothImmersion (I := I) (M := M))
    (z : AddCircle (1 : ℝ)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) I c₀.map z) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  intro v w h
  obtain ⟨a, ha⟩ := AddCircle.exists_smul_parameterTangent (x : AddCircle (1 : ℝ)) v
  obtain ⟨b, hb⟩ := AddCircle.exists_smul_parameterTangent (x : AddCircle (1 : ℝ)) w
  rw [← ha, ← hb, map_smul, map_smul] at h
  have hne : mfderiv 𝓘(ℝ, ℝ) I c₀.map (x : AddCircle (1 : ℝ))
      (AddCircle.parameterTangent (x : AddCircle (1 : ℝ))) ≠ 0 := by
    rw [c₀.mfderiv_map_parameterTangent]
    exact c₀.immersed x
  have hab : a = b := (smul_left_injective ℝ hne) h
  rw [hab] at ha
  exact ha.symm.trans hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.injective_mfderiv_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.injective_mfderiv_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.injective_mfderiv_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.injective_mfderiv_map

noncomputable def pullbackMetric (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
  g.pullback c₀.map c₀.contMDiff_map c₀.injective_mfderiv_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric

theorem pullbackMetric_inner_parameterTangent (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (x : ℝ) :
    (c₀.pullbackMetric g).inner (x : AddCircle (1 : ℝ)) (AddCircle.parameterTangent (x : AddCircle (1 : ℝ))) (AddCircle.parameterTangent (x : AddCircle (1 : ℝ))) =
      g.inner (c₀.map (x : AddCircle (1 : ℝ)))
        (mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ))) x (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ))) x (1 : ℝ)) := by
  rw [pullbackMetric, SmoothRiemannianMetric.pullback_inner,
    c₀.mfderiv_map_parameterTangent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent

theorem pullbackMetric_inner_parameterTangent_eq_speed_sq
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M) (x t : ℝ) :
    (c₀.pullbackMetric g).inner (x : AddCircle (1 : ℝ))
      (AddCircle.parameterTangent (x : AddCircle (1 : ℝ)))
      (AddCircle.parameterTangent (x : AddCircle (1 : ℝ))) =
      CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) x t ^ 2 := by
  rw [c₀.pullbackMetric_inner_parameterTangent]
  exact (Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg g _ _)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent_eq_speed_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent_eq_speed_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent_eq_speed_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.pullbackMetric_inner_parameterTangent_eq_speed_sq

theorem metricCoefficient_pullbackMetric
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M) (x t : ℝ) :
    AddCircle.metricCoefficient (c₀.pullbackMetric g) (x : AddCircle (1 : ℝ)) =
      CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) x t ^ 2 :=
  c₀.pullbackMetric_inner_parameterTangent_eq_speed_sq g x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.metricCoefficient_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.metricCoefficient_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.metricCoefficient_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.metricCoefficient_pullbackMetric

end SmoothImmersion

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothImmersion

theorem laplacian_pullbackMetric (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) {f : AddCircle (1 : ℝ) → ℝ} {x : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f (x : AddCircle (1 : ℝ))) (t : ℝ) :
    laplacian (LeviCivita (c₀.pullbackMetric g)) (c₀.pullbackMetric g) f
      (x : AddCircle (1 : ℝ)) =
      (CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) x t ^ 2)⁻¹ *
          deriv (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)))) x -
        deriv (fun y : ℝ => CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) y t ^ 2) x /
          (2 * (CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) x t ^ 2) ^ 2) *
            deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ))) x := by
  rw [AddCircle.laplacian_coe (c₀.pullbackMetric g) hf]
  simp_rw [c₀.pullbackMetric_inner_parameterTangent_eq_speed_sq g _ t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacian_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacian_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacian_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacian_pullbackMetric

theorem laplacianPrincipalCoefficient_pullbackMetric
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M) (x t : ℝ) :
    AddCircle.laplacianPrincipalCoefficient (c₀.pullbackMetric g) (x : AddCircle (1 : ℝ)) =
      (CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) x t ^ 2)⁻¹ := by
  rw [AddCircle.laplacianPrincipalCoefficient_apply, c₀.metricCoefficient_pullbackMetric g x t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianPrincipalCoefficient_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianPrincipalCoefficient_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianPrincipalCoefficient_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianPrincipalCoefficient_pullbackMetric

theorem laplacianDriftCoefficient_pullbackMetric
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M) (x t : ℝ) :
    AddCircle.laplacianDriftCoefficient (c₀.pullbackMetric g) (x : AddCircle (1 : ℝ)) =
      -deriv (fun y : ℝ => CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) y t ^ 2) x /
        (2 * (CurveMap.speed (fun z _ => c₀.map z) (fun _ => g) x t ^ 2) ^ 2) := by
  rw [AddCircle.laplacianDriftCoefficient_apply,
    ← AddCircle.deriv_comp_coe
      ((AddCircle.metricCoefficient (c₀.pullbackMetric g)).contMDiff.mdifferentiableAt (by decide))]
  simp_rw [c₀.metricCoefficient_pullbackMetric g _ t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianDriftCoefficient_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianDriftCoefficient_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianDriftCoefficient_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.laplacianDriftCoefficient_pullbackMetric

end SmoothImmersion

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
