import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.Conormal
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology _root_.Filter _root_.Manifold _root_.VectorField
open scoped _root_.ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)


def chartField (p : M) (V : (y : M) → TangentSpace I y) : E → E :=
  _root_.VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm V (_root_.Set.range I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.chartField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.chartField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.chartField ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.chartField

variable [IsManifold I 1 M]


theorem chartField_self (p : M) (V : (y : M) → TangentSpace I y) :
    chartField I p V (extChartAt I p p) = V p := by
  change (show E →L[ℝ] E from mfderivWithin 𝓘(ℝ, E) I
    (extChartAt I p).symm (_root_.Set.range I) (extChartAt I p p)).inverse
      (V ((extChartAt I p).symm (extChartAt I p p))) = V p
  have hv := congrArg (show M → E from V) (extChartAt_to_inv (I := I) p)
  rw [hv]
  exact mfderivWithin_extChartAt_symm_inverse_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.chartField_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.chartField_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.chartField_self ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.chartField_self

theorem mfderivWithin_symm_chartField (p : M) (V : (y : M) → TangentSpace I y)
    {z : E} (hz : z ∈ (extChartAt I p).target) :
    (show E →L[ℝ] E from mfderivWithin 𝓘(ℝ, E) I
      (extChartAt I p).symm (_root_.Set.range I) z) (chartField I p V z) = V ((extChartAt I p).symm z) := by
  let L : E →L[ℝ] E := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (_root_.Set.range I) z
  have hL : L.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hz
  exact (hL.inverse_apply_eq.mp (show L.inverse (V ((extChartAt I p).symm z)) =
    chartField I p V z from rfl)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.mfderivWithin_symm_chartField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.mfderivWithin_symm_chartField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.mfderivWithin_symm_chartField ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.mfderivWithin_symm_chartField

theorem chartField_eq_mfderiv (p : M) (V : (y : M) → TangentSpace I y)
    {z : E} (hz : z ∈ (extChartAt I p).target) :
    chartField I p V z =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z))
        (V ((extChartAt I p).symm z)) := by
  have hh := congrArg
    (fun L : E →L[ℝ] E => L (chartField I p V z))
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz)
  change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z))
    ((show E →L[ℝ] E from mfderivWithin 𝓘(ℝ, E) I
      (extChartAt I p).symm (_root_.Set.range I) z) (chartField I p V z)) = chartField I p V z at hh
  rw [mfderivWithin_symm_chartField I p V hz] at hh
  exact hh.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.chartField_eq_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.chartField_eq_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.chartField_eq_mfderiv ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.chartField_eq_mfderiv

theorem isMIntegralCurveOn_of_chartField (p : M) (V : (y : M) → TangentSpace I y)
    {γ : ℝ → E} {s : Set ℝ} (hstay : _root_.Set.MapsTo γ s (extChartAt I p).target)
    (hγ : ∀ t ∈ s, HasDerivWithinAt γ (chartField I p V (γ t)) s t) :
    IsMIntegralCurveOn ((extChartAt I p).symm ∘ γ) V s := by
  intro t ht
  have hinv := (mdifferentiableWithinAt_extChartAt_symm (hstay ht)).hasMFDerivWithinAt
  have hcurve := (hγ t ht).hasFDerivWithinAt.hasMFDerivWithinAt
  have hh := hinv.comp t hcurve (fun u hu => extChartAt_target_subset_range p (hstay hu))
  have he : (show E →L[ℝ] E from mfderivWithin 𝓘(ℝ, E) I
      (extChartAt I p).symm (_root_.Set.range I) (γ t)).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (chartField I p V (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (show E from V ((extChartAt I p).symm (γ t))) := by
    apply ContinuousLinearMap.ext
    intro a
    change (show E →L[ℝ] E from mfderivWithin 𝓘(ℝ, E) I
      (extChartAt I p).symm (_root_.Set.range I) (γ t)) (a • chartField I p V (γ t)) =
        a • V ((extChartAt I p).symm (γ t))
    rw [map_smul, mfderivWithin_symm_chartField I p V (hstay ht)]
    rfl
  erw [he] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_of_chartField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_of_chartField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_of_chartField ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_of_chartField

variable [CompleteSpace E] [IsManifold I ∞ M]

theorem contDiffOn_chartField (p : M) {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I I.tangent ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M))) :
    ContDiffOn ℝ ∞ (chartField I p V) (extChartAt I p).target := by
  intro z hz
  apply contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
  have hh := (hV ((extChartAt I p).symm z)).contMDiffWithinAt.mpullbackWithin_vectorField
    (contMDiffWithinAt_extChartAt_symm_range p hz)
    (isInvertible_mfderivWithin_extChartAt_symm hz)
    (extChartAt_target_subset_range p hz)
    (uniqueMDiffOn_iff_uniqueDiffOn.mpr I.uniqueDiffOn) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    (_root_.Set.mapsTo_univ _ _)
  exact hh.mono (extChartAt_target_subset_range p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.contDiffOn_chartField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.contDiffOn_chartField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.contDiffOn_chartField ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.contDiffOn_chartField

end General

theorem chartField_normal_pos
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]
    (p : M) (V : (y : M) → TangentSpace (𝓡∂ n) y)
    (hV : 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V p)) :
    0 < (chartField (𝓡∂ n) p V (extChartAt (𝓡∂ n) p p)) 0 := by
  rw [chartField_self]
  exact hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.chartField_normal_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.chartField_normal_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.chartField_normal_pos ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.chartField_normal_pos

end DifferentialGeometry.Manifold.BoundaryCollar
