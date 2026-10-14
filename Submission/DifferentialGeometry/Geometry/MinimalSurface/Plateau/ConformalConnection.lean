import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates
import Mathlib.Analysis.Calculus.TangentCone.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem fderiv_conformalPairing_within
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ K, DiskMapConformalAt g U q)
    {z : ℂ} (hz : z ∈ s) (hzK : z ∈ K) (hK : UniqueDiffWithinAt ℝ K z) (v w x : ℂ) :
    fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q w) (diskMapPartial U q x)) z v =
      fderiv ℝ (diskMapConformalCoefficient g U) z v * _root_.Inner.inner ℝ w x := by
  have heq : _root_.Set.EqOn (fun q => g.inner (U q) (diskMapPartial U q w) (diskMapPartial U q x))
      (fun q => diskMapConformalCoefficient g U q * _root_.Inner.inner ℝ w x) K :=
    fun q hq => (hconf q hq).inner_partials w x
  have ha := ((contDiffOn_diskMapConformalCoefficient g hs hU z hz).contDiffAt
    (hs.mem_nhds hz)).differentiableAt (by simp)
  have hp := ((contDiffOn_diskMapMetricPairing g hs hU w x z hz).contDiffAt
    (hs.mem_nhds hz)).differentiableAt (by simp)
  have hd := fderivWithin_congr' (𝕜 := ℝ) heq hzK
  rw [fderivWithin_eq_fderiv hK hp, fderivWithin_eq_fderiv hK (ha.mul_const _)] at hd
  rw [hd, (ha.hasFDerivAt.mul_const (_root_.Inner.inner ℝ w x)).fderiv]
  simp [mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.fderiv_conformalPairing_within
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.fderiv_conformalPairing_within target :: scope.openDecls } }




theorem diskMapCovariantPartial_inner_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ K, DiskMapConformalAt g U q)
    {z : ℂ} (hz : z ∈ s) (hzK : z ∈ K) (hK : UniqueDiffWithinAt ℝ K z) (v w x : ℂ) :
    g.inner (U z) (diskMapCovariantPartial g U z v w) (diskMapPartial U z x) =
      (fderiv ℝ (diskMapConformalCoefficient g U) z v * _root_.Inner.inner ℝ w x +
        fderiv ℝ (diskMapConformalCoefficient g U) z w * _root_.Inner.inner ℝ v x -
        fderiv ℝ (diskMapConformalCoefficient g U) z x * _root_.Inner.inner ℝ v w) / 2 := by
  have hv := fderiv_conformalPairing_within g hs hU hconf hz hzK hK v w x
  have hw := fderiv_conformalPairing_within g hs hU hconf hz hzK hK w v x
  have hx := fderiv_conformalPairing_within g hs hU hconf hz hzK hK x v w
  rw [fderiv_diskMapMetricPairing g hs hU hz] at hv hw hx
  rw [g.symm (U z) (diskMapPartial U z w)] at hv
  rw [g.symm (U z) (diskMapPartial U z v)] at hw hx
  rw [diskMapCovariantPartial_symm g hs hU hz w v] at hw
  rw [diskMapCovariantPartial_symm g hs hU hz x v,
    diskMapCovariantPartial_symm g hs hU hz x w] at hx
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal ``Submission.DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal



theorem diskMapCovariantPartial_inner_conformal_closedDisk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) (v w x : ℂ) :
    g.inner (U z) (diskMapCovariantPartial g U z v w) (diskMapPartial U z x) =
      (fderiv ℝ (diskMapConformalCoefficient g U) z v * _root_.Inner.inner ℝ w x +
        fderiv ℝ (diskMapConformalCoefficient g U) z w * _root_.Inner.inner ℝ v x -
        fderiv ℝ (diskMapConformalCoefficient g U) z x * _root_.Inner.inner ℝ v w) / 2 := by
  apply diskMapCovariantPartial_inner_conformal g hs hU hconf (hDs hz) hz
  apply uniqueDiffOn_convex (convex_closedBall (0 : ℂ) 1) _ z hz
  rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  exact ⟨0, Metric.mem_ball_self (by norm_num)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal_closedDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal_closedDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal_closedDisk ``Submission.DifferentialGeometry.Geometry.diskMapCovariantPartial_inner_conformal_closedDisk

end DifferentialGeometry.Geometry
