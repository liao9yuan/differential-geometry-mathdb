import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauAreaVariationBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskBoundaryIntegral
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] in
theorem SmoothDisk.conformalFactor_nonneg (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (z : Disk) : 0 ≤ u.conformalFactor g z := by
  rw [SmoothDisk.conformalFactor]
  by_cases h : u.differential z 1 = 0
  · rw [h]
    simp
  · exact (g.pos (u.map z) (u.differential z 1) h).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_nonneg

omit [FiniteDimensional ℝ E] in
theorem SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U) (z : Disk) :
    u.conformalFactor g z = diskMapConformalCoefficient g U (z : ℂ) := by
  unfold SmoothDisk.conformalFactor diskMapConformalCoefficient
  rw [← hU.1 z, SmoothDisk.differential_eq_diskMapPartial u hU z 1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient

theorem SmoothDisk.sectionalDensity_eq_diskMapSectionalDensity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U) (z : Disk) :
    u.sectionalDensity g z = diskMapSectionalDensity g U (z : ℂ) := by
  have hcoef := SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient u g hU z
  have hd1 := SmoothDisk.differential_eq_diskMapPartial u hU z 1
  have hdI := SmoothDisk.differential_eq_diskMapPartial u hU z Complex.I
  unfold SmoothDisk.sectionalDensity diskMapSectionalDensity
  by_cases h : 0 < u.conformalFactor g z
  · rw [if_pos h, ← hcoef, ← hU.1 z, ← hd1, ← hdI]
  · rw [if_neg h]
    have h0 : u.conformalFactor g z = 0 :=
      le_antisymm (not_lt.mp h) (SmoothDisk.conformalFactor_nonneg u g z)
    rw [← hcoef, h0, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.sectionalDensity_eq_diskMapSectionalDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.sectionalDensity_eq_diskMapSectionalDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.sectionalDensity_eq_diskMapSectionalDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.sectionalDensity_eq_diskMapSectionalDensity

end Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [CompactSpace Q]

omit [CompactSpace Q] in
theorem SmoothDisk.metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar_mul
    (hdim : Module.finrank ℝ E = 3)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q} {J : Set ℝ} {t : ℝ} (ht : J ∈ 𝓝 t)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (G t) (U z) X Y) t)
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t) U z) :
    ∀ z : Disk,
      u.metricVariationDensity G J t z =
        -(2 * u.sectionalDensity (G t) z +
          metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map z) * u.conformalFactor (G t) z) := by
  intro z
  have hz : (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := z.property
  have hd1 : derivWithin (fun r : ℝ =>
        (G r).inner (u.map z) (u.differential z 1) (u.differential z 1)) J t =
      deriv (fun r : ℝ => (G r).inner (U (z : ℂ))
        (diskMapPartial U (z : ℂ) 1) (diskMapPartial U (z : ℂ) 1)) t := by
    rw [derivWithin_of_mem_nhds ht]
    congr 1
    funext r
    rw [← hU.1 z, SmoothDisk.differential_eq_diskMapPartial u hU z 1]
  have hd2 : derivWithin (fun r : ℝ =>
        (G r).inner (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)) J t =
      deriv (fun r : ℝ => (G r).inner (U (z : ℂ))
        (diskMapPartial U (z : ℂ) Complex.I) (diskMapPartial U (z : ℂ) Complex.I)) t := by
    rw [derivWithin_of_mem_nhds ht]
    congr 1
    funext r
    rw [← hU.1 z, SmoothDisk.differential_eq_diskMapPartial u hU z Complex.I]
  have hmain := diskMapMetricVariationDensity_eq_neg_sectionalDensity_and_half_scalar_mul
    (E := E) (M := Q) hdim (hconf z hz) (hderiv z hz)
  rw [diskMapMetricVariationDensity, ← hd1, ← hd2] at hmain
  have hsum : derivWithin (fun r : ℝ =>
        (G r).inner (u.map z) (u.differential z 1) (u.differential z 1)) J t +
      derivWithin (fun r : ℝ =>
        (G r).inner (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)) J t =
      -(2 * u.sectionalDensity (G t) z +
        metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map z) * u.conformalFactor (G t) z) := by
    rw [← SmoothDisk.sectionalDensity_eq_diskMapSectionalDensity u (G t) hU z,
      ← SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient u (G t) hU z,
      hU.1 z] at hmain
    linarith
  rw [SmoothDisk.metricVariationDensity]
  by_cases hpos : 0 < u.conformalFactor (G t) z
  · rw [if_pos hpos]
    exact hsum
  · rw [if_neg hpos]
    have h0 : u.conformalFactor (G t) z = 0 :=
      le_antisymm (not_lt.mp hpos) (SmoothDisk.conformalFactor_nonneg u (G t) z)
    unfold SmoothDisk.sectionalDensity
    rw [if_neg hpos, h0, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero, add_zero, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar_mul

omit [CompactSpace Q] in
theorem SmoothDisk.integral_metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar
    (hdim : Module.finrank ℝ E = 3)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q} {J : Set ℝ} {t : ℝ} (ht : J ∈ 𝓝 t)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (G r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (G t) (U z) X Y) t)
    (hconf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (G t) U z)
    (hintSectional : _root_.MeasureTheory.IntegrableOn (diskExtension (u.sectionalDensity (G t)))
      (Metric.closedBall (0 : ℂ) 1))
    (hintScalar : _root_.MeasureTheory.IntegrableOn (diskExtension (fun z : Disk =>
      metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map z) * u.conformalFactor (G t) z))
      (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity G J t) z) =
      -2 * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.sectionalDensity (G t)) z) -
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (fun z : Disk =>
            metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map z) *
              u.conformalFactor (G t) z) z) := by
  have hpt := SmoothDisk.metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar_mul
    hdim u ht hU hderiv hconf
  have hae : (fun z => diskExtension (u.metricVariationDensity G J t) z) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)]
      (fun z => -(2 * diskExtension (u.sectionalDensity (G t)) z +
        diskExtension (fun w : Disk => metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map w) *
          u.conformalFactor (G t) w) z)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
    rw [show diskExtension (u.metricVariationDensity G J t) z =
        u.metricVariationDensity G J t ⟨z, hz⟩ from dif_pos hz,
      show diskExtension (u.sectionalDensity (G t)) z =
        u.sectionalDensity (G t) ⟨z, hz⟩ from dif_pos hz,
      show diskExtension (fun w : Disk => metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map w) *
          u.conformalFactor (G t) w) z =
        metricScalarAt (I := 𝓘(ℝ, E)) (G t) (u.map ⟨z, hz⟩) *
          u.conformalFactor (G t) ⟨z, hz⟩ from dif_pos hz]
    exact hpt ⟨z, hz⟩
  rw [_root_.MeasureTheory.integral_congr_ae hae]
  have h2 : _root_.MeasureTheory.IntegrableOn (fun z => 2 * diskExtension (u.sectionalDensity (G t)) z)
      (Metric.closedBall (0 : ℂ) 1) := hintSectional.const_mul 2
  rw [_root_.MeasureTheory.integral_neg, _root_.MeasureTheory.integral_add h2 hintScalar, _root_.MeasureTheory.integral_const_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integral_metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integral_metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integral_metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integral_metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar

section ScalarMinimum

variable [SigmaCompactSpace Q] [Nonempty Q]
  {F : SolutionFamily (I := 𝓘(ℝ, E)) (M := Q)} {t : ℝ}

omit [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q] [Nonempty Q] in
theorem scalarMinimum_le_scalar (hbdd : BddBelow (Set.range (F.scalar t))) (x : Q) :
    CurveShortening.scalarMinimum F t ≤ F.scalar t x :=
  csInf_le hbdd (Set.mem_range_self x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_le_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_le_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_le_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_le_scalar

omit [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q] [Nonempty Q] in
theorem scalarMinimum_mul_diskArea_le_integral_scalar_mul
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (hbdd : BddBelow (Set.range (F.scalar t)))
    (hintA : _root_.MeasureTheory.IntegrableOn (diskExtension (u.conformalFactor (F.metric t)))
      (Metric.closedBall (0 : ℂ) 1))
    (harea : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.conformalFactor (F.metric t)) z) = diskArea (F.metric t) u.map)
    (hintScalar : _root_.MeasureTheory.IntegrableOn (diskExtension (fun z : Disk =>
      metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t) (u.map z) *
        u.conformalFactor (F.metric t) z)) (Metric.closedBall (0 : ℂ) 1)) :
    CurveShortening.scalarMinimum F t * diskArea (F.metric t) u.map ≤
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (fun z : Disk =>
        metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t) (u.map z) *
          u.conformalFactor (F.metric t) z) z) := by
  have hpt (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      CurveShortening.scalarMinimum F t *
        diskExtension (u.conformalFactor (F.metric t)) z ≤
      diskExtension (fun w : Disk => metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t)
        (u.map w) * u.conformalFactor (F.metric t) w) z := by
    rw [show diskExtension (u.conformalFactor (F.metric t)) z =
        u.conformalFactor (F.metric t) ⟨z, hz⟩ from dif_pos hz,
      show diskExtension (fun w : Disk => metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t)
          (u.map w) * u.conformalFactor (F.metric t) w) z =
        metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t) (u.map ⟨z, hz⟩) *
          u.conformalFactor (F.metric t) ⟨z, hz⟩ from dif_pos hz]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [SolutionFamily.scalar] using
        scalarMinimum_le_scalar (F := F) hbdd (u.map ⟨z, hz⟩))
      (SmoothDisk.conformalFactor_nonneg u (F.metric t) ⟨z, hz⟩)
  have h2 : _root_.MeasureTheory.IntegrableOn (fun z => CurveShortening.scalarMinimum F t *
      diskExtension (u.conformalFactor (F.metric t)) z) (Metric.closedBall (0 : ℂ) 1) :=
    hintA.const_mul _
  calc CurveShortening.scalarMinimum F t * diskArea (F.metric t) u.map
      = CurveShortening.scalarMinimum F t *
          (∫ z in Metric.closedBall (0 : ℂ) 1,
            diskExtension (u.conformalFactor (F.metric t)) z) := by rw [harea]
    _ = ∫ z in Metric.closedBall (0 : ℂ) 1, CurveShortening.scalarMinimum F t *
          diskExtension (u.conformalFactor (F.metric t)) z :=
        (_root_.MeasureTheory.integral_const_mul _ _).symm
    _ ≤ _ := _root_.MeasureTheory.integral_mono_ae h2 hintScalar (by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
      exact hpt z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_mul_diskArea_le_integral_scalar_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_mul_diskArea_le_integral_scalar_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_mul_diskArea_le_integral_scalar_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.scalarMinimum_mul_diskArea_le_integral_scalar_mul

end ScalarMinimum

section ConformalAreaDensity

omit [FiniteDimensional ℝ E] [T2Space Q] [CompactSpace Q] in
def SmoothDisk.HasConformalAreaDensity (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) : Prop :=
  _root_.MeasureTheory.IntegrableOn (diskExtension (u.conformalFactor g)) (Metric.closedBall (0 : ℂ) 1) ∧
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.conformalFactor g) z) =
      diskArea g u.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.HasConformalAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.HasConformalAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.HasConformalAreaDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.HasConformalAreaDensity

omit [FiniteDimensional ℝ E] [T2Space Q] [CompactSpace Q] in
theorem SmoothDisk.hasConformalAreaDensity_const (q : Q)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) :
    (SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).HasConformalAreaDensity g := by
  have hU : SmoothDiskExtension (E := E)
      (SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).map (fun _ : ℂ => q) := by
    refine ⟨fun z => rfl, Set.univ, isOpen_univ, fun z _ => Set.mem_univ z, ?_⟩
    exact contMDiffOn_const
  have hmap : diskExtension (⇑(SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).map) =
      fun _ => q := by
    funext w
    rw [diskExtension]
    split_ifs <;> rfl
  have hzero (z : Disk) :
      (SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).conformalFactor g z = 0 := by
    rw [SmoothDisk.conformalFactor]
    have hd : (SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).differential z 1 = 0 := by
      rw [SmoothDisk.differential, hmap]
      exact congrArg (fun (L : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) q) => L (1 : ℂ))
        (mfderivWithin_const (𝕜 := ℝ) (I := 𝓘(ℝ, ℂ)) (M := ℂ)
          (I' := 𝓘(ℝ, E)) (M' := Q) (s := Metric.closedBall (0 : ℂ) 1)
          (x := (z : ℂ)) (c := q))
    rw [hd]
    simp
  have hfun : (fun z : ℂ => diskExtension (fun w : Disk =>
      (SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).conformalFactor g w) z) =
      fun _ => (0 : ℝ) := by
    funext z
    rw [diskExtension]
    split_ifs with hz
    · exact hzero ⟨z, hz⟩
    · exact hzero diskCenter
  have hmap2 : (⇑(SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).map : Disk → Q) =
      fun _ => q := rfl
  refine ⟨?_, ?_⟩
  · have hInt : _root_.MeasureTheory.IntegrableOn (fun z : ℂ => diskExtension (fun w : Disk =>
        (SmoothDisk.const (I := 𝓘(ℝ, E)) (Q := Q) q).conformalFactor g w) z)
        (Metric.closedBall (0 : ℂ) 1) := by
      rw [hfun]
      exact _root_.MeasureTheory.integrableOn_zero
    exact hInt
  · rw [_root_.MeasureTheory.integral_congr_ae (Filter.EventuallyEq.of_eq hfun), _root_.MeasureTheory.integral_zero, hmap2, diskArea_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.hasConformalAreaDensity_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.hasConformalAreaDensity_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.hasConformalAreaDensity_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.hasConformalAreaDensity_const

end ConformalAreaDensity

section Assembly

variable [SigmaCompactSpace Q] [Nonempty Q]

omit [CompactSpace Q] [SigmaCompactSpace Q] [Nonempty Q] in
theorem SmoothDisk.transportedAreaVariation_le_of_metricDerivative
    (hdim : Module.finrank ℝ E = 3)
    (F : SolutionFamily (I := 𝓘(ℝ, E)) (M := Q))
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) {J : Set ℝ} {t : ℝ} (ht : J ∈ 𝓝 t)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma.toContinuousLoop (sigma.map theta))
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (F.metric r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (F.metric t) (U z) X Y) t)
    (hconf : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      DiskMapConformalAt (F.metric t) U (circleMap 0 1 (2 * Real.pi * x)))
    (hconfBall : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (F.metric t) U z)
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z))
    (hintFlux : IntervalIntegrable (u.boundaryFluxDensity (F.metric t) V) _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) 1)
    (hintCurv : IntervalIntegrable
      (u.boundaryCurvatureDensity (F.metric t) gamma sigma htrace) _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) 1)
    (hintError : IntervalIntegrable (fun x : ℝ => Real.sqrt
      ((F.metric t).inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryNormalVelocityError (F.metric t) gamma sigma htrace V x)
        (u.boundaryNormalVelocityError (F.metric t) gamma sigma htrace V x)) *
        u.boundarySpeed (F.metric t) x) _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) 1)
    (hintSectional : _root_.MeasureTheory.IntegrableOn (diskExtension (u.sectionalDensity (F.metric t)))
      (Metric.closedBall (0 : ℂ) 1))
    (hintScalar : _root_.MeasureTheory.IntegrableOn (diskExtension (fun z : Disk =>
      metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t) (u.map z) *
        u.conformalFactor (F.metric t) z)) (Metric.closedBall (0 : ℂ) 1))
    (hbdd : BddBelow (Set.range (F.scalar t)))
    (hintArea : _root_.MeasureTheory.IntegrableOn (diskExtension (u.conformalFactor (F.metric t)))
      (Metric.closedBall (0 : ℂ) 1))
    (harea : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.conformalFactor (F.metric t)) z) = diskArea (F.metric t) u.map)
    (hcurv : 2 * Real.pi ≤
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity (F.metric t)) z) +
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity (F.metric t) gamma sigma htrace x) :
    (1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity F.metric J t) z) -
        u.boundaryFlux (F.metric t) V ≤
      -2 * Real.pi -
        CurveShortening.scalarMinimum F t * diskArea (F.metric t) u.map / 2 +
        u.boundaryAreaError (F.metric t) gamma sigma htrace V := by
  have hMv := SmoothDisk.integral_metricVariationDensity_eq_neg_two_mul_sectionalDensity_sub_scalar
    (Q := Q) hdim u ht hU hderiv hconfBall hintSectional hintScalar
  have hscal := scalarMinimum_mul_diskArea_le_integral_scalar_mul (F := F) u hbdd
    hintArea harea hintScalar
  exact SmoothDisk.transportedAreaVariation_le u (F.metric t) gamma sigma htrace hU hconf V
    hintFlux hintCurv hintError
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (fun z : Disk =>
      metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t) (u.map z) *
        u.conformalFactor (F.metric t) z) z)
    (CurveShortening.scalarMinimum F t)
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskExtension (u.metricVariationDensity F.metric J t) z)
    hMv hcurv hscal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.transportedAreaVariation_le_of_metricDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.transportedAreaVariation_le_of_metricDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.transportedAreaVariation_le_of_metricDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.transportedAreaVariation_le_of_metricDerivative

end Assembly

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
