import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import Submission.DifferentialGeometry.Geometry.Exponential.Radial
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Length
import Submission.DifferentialGeometry.Geometry.Metric.Path.Reparametrization
import Mathlib.Analysis.Convex.PathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

def radialPath (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hv : v ∈ expDomain g p) : Path p (expMap g p v) :=
  ((Path.segment (0 : E) (show E from v)).map'
    ((contMDiffOn_expMap g p).continuousOn.mono (by
      rw [Path.range_segment]
      exact (starConvex_expDomain g p).segment_subset hv))).cast
    (expMap_zero g p).symm rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath

@[simp] theorem radialPath_apply (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) (t : unitInterval) :
    radialPath g p v hv t = expMap g p ((t : ℝ) • v) := by
  have h (w : E) : (Path.segment (0 : E) w) t = (t : ℝ) • w := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]
  exact congrArg (fun w : E => expMap g p (show TangentSpace I p from w)) (h v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.radialPath_apply

theorem eqOn_extend_radialPath (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    EqOn (radialPath g p v hv).extend (fun t : ℝ => expMap g p (t • v)) (_root_.Set.Icc 0 1) := by
  intro t ht
  rw [Path.extend_apply _ ht, radialPath_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.eqOn_extend_radialPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.eqOn_extend_radialPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.eqOn_extend_radialPath ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.eqOn_extend_radialPath

theorem range_radialPath (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    range (radialPath g p v hv) = expMap g p '' segment ℝ 0 v := by
  have h := _root_.Set.range_comp
    (f := (Path.segment (0 : E) (show E from v)))
    (g := fun w : E => expMap g p (show TangentSpace I p from w))
  rw [Path.range_segment] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.range_radialPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.range_radialPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.range_radialPath ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.range_radialPath

theorem contMDiffOn_extend_radialPath (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (radialPath g p v hv).extend (_root_.Set.Icc 0 1) := by
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => t • (show E from v)) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_id.smul contDiff_const
  have h := (contMDiffOn_expMap g p).comp hline.contMDiffOn
    (fun _ ht => smul_mem_expDomain hv ht)
  exact h.congr (eqOn_extend_radialPath g p v hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.contMDiffOn_extend_radialPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.contMDiffOn_extend_radialPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.contMDiffOn_extend_radialPath ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.contMDiffOn_extend_radialPath

theorem extend_radialPath_withSittingInstants (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    (radialPath g p v hv).withSittingInstants.extend =
      fun t : ℝ => expMap g p (Real.smoothTransition (3 * t - 1) • v) := by
  rw [Path.extend_withSittingInstants]
  funext t
  exact eqOn_extend_radialPath g p v hv
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.extend_radialPath_withSittingInstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.extend_radialPath_withSittingInstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.extend_radialPath_withSittingInstants ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.extend_radialPath_withSittingInstants

theorem riemannianELength_radialPath [(x : M) → ENorm (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    (radialPath g p v hv).riemannianELength (I := I) =
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t : ℝ => expMap g p (t • v)) (_root_.Set.Icc 0 1) :=
    ((contMDiffOn_extend_radialPath g p v hv).of_le (by norm_num)).congr
      (eqOn_extend_radialPath g p v hv).symm
  rw [Path.riemannianELength,
    Manifold.pathELength_congr (eqOn_extend_radialPath g p v hv),
    Geodesic.pathELength_eq_arcLength_of_enorm_eq g zero_le_one
      ((Geodesic.speedSqrt_integrableOn_Icc_of_C1 g zero_le_one hγ).mono_set _root_.Set.Ioo_subset_Icc_self)
      (fun t _ => hEnorm _ _)]
  have hdom : (show TangentSpace I p from (1 : ℝ) • (show E from v)) ∈ expDomain g p := by
    change (1 : ℝ) • (show E from v) ∈ expDomain g p
    rw [one_smul]
    exact hv
  simpa only [one_mul] using!
    congrArg ENNReal.ofReal (arcLength_expMap_smul g p (show E from v) hdom)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianELength_radialPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianELength_radialPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianELength_radialPath ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianELength_radialPath

end DifferentialGeometry.Geometry.Riemannian.Exponential
