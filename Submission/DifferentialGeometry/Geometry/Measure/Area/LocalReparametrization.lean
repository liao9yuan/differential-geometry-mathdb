import Submission.DifferentialGeometry.Geometry.Measure.Area.RegionCongruence
import Submission.DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]




theorem riemannianArea_precomp_on (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {φ : ℂ → ℂ} {s : Set ℂ} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (hs : IsOpen s) (hφ : LipschitzOnWith K φ s)
    (hL : ∀ x ∈ s, ∀ y ∈ s, _root_.EDist.edist x y ≤ (L : ℝ≥0∞) * _root_.EDist.edist (φ x) (φ y)) :
    riemannianArea g (u ∘ φ) s = riemannianArea g u (φ '' s) := by
  have hinj : _root_.Set.InjOn φ s := by
    intro x hx y hy heq
    apply edist_eq_zero.mp
    apply le_antisymm _ bot_le
    simpa only [heq, _root_.PseudoEMetricSpace.edist_self, _root_.MulZeroClass.mul_zero] using! hL x hx y hy
  let ψ := Function.invFunOn φ s
  have hi : ∀ x ∈ s, ψ (φ x) = x := hinj.leftInvOn_invFunOn
  have hψ : LipschitzOnWith L ψ (φ '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hi x hx, hi y hy]
    exact hL x hx y hy
  obtain ⟨Φ, hΦ, heΦ⟩ := hφ.extend_finite_dimension
  obtain ⟨Ψ, hΨ, heΨ⟩ := hψ.extend_finite_dimension
  have hi' (x : ℂ) (hx : x ∈ s) : Ψ (Φ x) = x := by
    rw [← heΦ hx, ← heΨ (_root_.Set.mem_image_of_mem φ hx), hi x hx]
  calc
    _ = riemannianArea g (u ∘ Φ) s := riemannianArea_congr_on_open g hs
      (fun x hx => congrArg u (heΦ hx))
    _ = riemannianArea g u (Φ '' s) := riemannianArea_precomp g hu hΦ hΨ hs.measurableSet hi'
    _ = _ := by rw [heΦ.image_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_precomp_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_precomp_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_precomp_on ``Submission.DifferentialGeometry.Geometry.riemannianArea_precomp_on

end DifferentialGeometry.Geometry
