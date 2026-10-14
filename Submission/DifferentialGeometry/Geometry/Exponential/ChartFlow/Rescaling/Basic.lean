import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.ChartPhase

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.NNReal _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable [I.Boundaryless]

def rescaleChartOrbit (a : ℝ) : E × E → E × E :=
  fun z => (z.1, a • z.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleChartOrbit_apply (a : ℝ) (z : E × E) :
    rescaleChartOrbit a z = (z.1, a • z.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_apply

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleChartOrbit_mk (a : ℝ) (x v : E) :
    rescaleChartOrbit (E := E) a (x, v) = (x, a • v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_mk ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.rescaleChartOrbit_mk

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPhaseVF_rescale
    (g : SmoothRiemannianMetric I M) (α : M)
    (a : ℝ) (x v : E) :
    chartPhaseVF (I := I) g α (x, a • v) =
      (a • v, -(a * a) • chartChristoffelContraction (I := I) g α v v x) := by
  classical
  have h0 : chartPhaseVF (I := I) g α (x, a • v) =
      (a • v, -chartChristoffelContraction (I := I) g α (a • v) (a • v) x) := rfl
  rw [h0]
  refine Prod.ext rfl ?_
  have hΓ : chartChristoffelContraction (I := I) g α (a • v) (a • v) x =
      (a * a) • chartChristoffelContraction (I := I) g α v v x :=
    chartChristoffelContraction_smul_smul (I := I) g α a v x
  change -chartChristoffelContraction (I := I) g α (a • v) (a • v) x =
      -(a * a) • chartChristoffelContraction (I := I) g α v v x
  rw [hΓ, neg_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.chartPhaseVF_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.chartPhaseVF_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.chartPhaseVF_rescale ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.chartPhaseVF_rescale

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma hasDerivAt_rescaled_orbit
    {g : SmoothRiemannianMetric I M} {α : M}
    {c : ℝ → E × E} {s₀ a : ℝ}
    (hd : HasDerivAt c (chartPhaseVF (I := I) g α (c (a * s₀))) (a * s₀)) :
    HasDerivAt (fun s : ℝ => rescaleChartOrbit (E := E) a (c (a * s)))
      (chartPhaseVF (I := I) g α
        (rescaleChartOrbit (E := E) a (c (a * s₀)))) s₀ := by
  classical
  set z : E × E := c (a * s₀) with hz_def
  have hmul : HasDerivAt (fun s : ℝ => a * s) a s₀ := by
    have : HasDerivAt (fun s : ℝ => a * s) (a * 1) s₀ := (hasDerivAt_id s₀).const_mul a
    simpa using this
  have hcomp : HasDerivAt (fun s : ℝ => c (a * s))
      (a • chartPhaseVF (I := I) g α z) s₀ := hd.scomp s₀ hmul
  set rescale : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • (ContinuousLinearMap.id ℝ E))
    with hrescale_def
  have hrescale_apply : ∀ y : E × E, rescale y = (y.1, a • y.2) := by
    intro y
    change ((ContinuousLinearMap.id ℝ E) y.1, (a • (ContinuousLinearMap.id ℝ E)) y.2) =
        (y.1, a • y.2)
    refine Prod.ext rfl ?_
    change (a • (ContinuousLinearMap.id ℝ E)) y.2 = a • y.2
    rw [smul_apply]
    rfl
  have hrescaled_eq : (fun s : ℝ => rescale (c (a * s))) =
      (fun s : ℝ => rescaleChartOrbit (E := E) a (c (a * s))) := by
    funext s
    simp [rescaleChartOrbit, hrescale_apply]
  have hcomp_rescale : HasDerivAt (fun s : ℝ => rescale (c (a * s)))
      (rescale (a • chartPhaseVF (I := I) g α z)) s₀ :=
    rescale.hasFDerivAt.comp_hasDerivAt s₀ hcomp
  rw [hrescaled_eq] at hcomp_rescale
  have hrhs_eq :
      rescale (a • chartPhaseVF (I := I) g α z) =
        chartPhaseVF (I := I) g α
          (rescaleChartOrbit (E := E) a (c (a * s₀))) := by
    rw [hrescale_apply]
    have h_rescaled_form : rescaleChartOrbit (E := E) a (c (a * s₀)) =
        (z.1, a • z.2) := rfl
    rw [h_rescaled_form]
    rw [chartPhaseVF_rescale (I := I) g α a z.1 z.2]
    have hpvf : chartPhaseVF (I := I) g α z =
        (z.2, -chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := rfl
    rw [hpvf]
    simp only [Prod.smul_mk, smul_neg, smul_smul]
    refine Prod.ext rfl ?_
    rw [neg_smul]
  rw [← hrhs_eq]
  exact hcomp_rescale

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.hasDerivAt_rescaled_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.hasDerivAt_rescaled_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.hasDerivAt_rescaled_orbit ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.hasDerivAt_rescaled_orbit

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
