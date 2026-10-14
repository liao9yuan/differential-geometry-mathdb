import Submission.DifferentialGeometry.Geometry.Metric.Cylinder
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiff_vertical_inner
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner (x, t) (0, 1) (0, 1)) := by
  let s : M → M × ℝ := fun x => (x, t)
  have hs : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ s :=
    contMDiff_id.prodMk contMDiff_const
  have hV : ContMDiff I ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) ∞
      (fun x : M => (⟨s x, (0, 1)⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) :=
    DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis.comp hs
  have htotal : ContMDiff I ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial (M × ℝ) ℝ) (s x)
        (g.inner (s x) (0, 1) (0, 1))) :=
    ContMDiff.clm_bundle_apply₂ (g.contMDiff.comp hs) hV hV
  intro x
  have hx := htotal x
  rw [_root_.Bundle.contMDiffAt_totalSpace] at hx
  exact hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.contMDiff_vertical_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.contMDiff_vertical_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.contMDiff_vertical_inner ``Submission.DifferentialGeometry.SmoothRiemannianMetric.contMDiff_vertical_inner

theorem vertical_inner_pos
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (x : M) (t : ℝ) :
    0 < g.inner (x, t) (0, 1) (0, 1) := by
  apply g.pos
  intro hzero
  have h := congrArg Prod.snd hzero
  exact one_ne_zero h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.vertical_inner_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.vertical_inner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.vertical_inner_pos ``Submission.DifferentialGeometry.SmoothRiemannianMetric.vertical_inner_pos

theorem contMDiff_sqrt_vertical_inner
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Real.sqrt (g.inner (x, t) (0, 1) (0, 1))) := by
  intro x
  exact (Real.contDiffAt_sqrt (g.vertical_inner_pos x t).ne').contMDiffAt.comp x
    (g.contMDiff_vertical_inner t).contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.contMDiff_sqrt_vertical_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.contMDiff_sqrt_vertical_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.contMDiff_sqrt_vertical_inner ``Submission.DifferentialGeometry.SmoothRiemannianMetric.contMDiff_sqrt_vertical_inner

theorem sqrt_vertical_inner_pos
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (x : M) (t : ℝ) :
    0 < Real.sqrt (g.inner (x, t) (0, 1) (0, 1)) :=
  Real.sqrt_pos.mpr (g.vertical_inner_pos x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.sqrt_vertical_inner_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.sqrt_vertical_inner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.sqrt_vertical_inner_pos ``Submission.DifferentialGeometry.SmoothRiemannianMetric.sqrt_vertical_inner_pos

end DifferentialGeometry.SmoothRiemannianMetric
