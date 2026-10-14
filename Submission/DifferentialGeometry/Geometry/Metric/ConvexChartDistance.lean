import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Manifold _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Manifold
open _root_.Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

set_option backward.isDefEq.respectTransparency false in
open _root_.Manifold in
theorem riemannianEDist_le_mul_edist_of_convex
    {f : V → M} {U S : Set V} {C : ℝ≥0}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) I 1 f U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hC : ∀ p ∈ S, ∀ v : V,
      ‖mfderiv 𝓘(ℝ, V) I f p v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    riemannianEDist I (f x) (f y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η := η.contDiff.contMDiff
  have hηS : _root_.Set.MapsTo η (_root_.Set.Icc (0 : ℝ) 1) S := hS.mapsTo_lineMap hx hy
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (f ∘ η) (_root_.Set.Icc 0 1) :=
    hf.comp hη.contMDiffOn (fun t ht => hSU (hηS ht))
  have hspeed : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) I (f ∘ η) t 1‖ₑ ≤ (C : ℝ≥0∞) * ‖y - x‖ₑ := by
    intro t ht
    have hdf := ((hf _ (hSU (hηS ht))).contMDiffAt
      (hU.mem_nhds (hSU (hηS ht)))).mdifferentiableAt one_ne_zero
    have hder : HasDerivAt η (y - x) t := AffineMap.hasDerivAt_lineMap
    have hDη : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η t (1 : ℝ) = y - x := by
      rw [mfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := η) (x := t)).trans hder.deriv
    rw [mfderiv_comp t hdf hder.differentiableAt.mdifferentiableAt]
    change ‖mfderiv 𝓘(ℝ, V) I f (η t) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η t) 1)‖ₑ ≤ _
    rw [hDη]
    exact hC _ (hηS ht) _
  have hlen : _root_.Manifold.pathELength I (f ∘ η) 0 1 ≤ (C : ℝ≥0∞) * ‖y - x‖ₑ := by
    rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc
      _ ≤ ∫⁻ _t in _root_.Set.Icc (0 : ℝ) 1, (C : ℝ≥0∞) * ‖y - x‖ₑ := by
        apply _root_.MeasureTheory.lintegral_mono_ae
        filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
        exact hspeed t ht
      _ = _ := by simp
  have hd : _root_.Manifold.riemannianEDist I (f x) (f y) ≤ _root_.Manifold.pathELength I (f ∘ η) 0 1 := by
    apply _root_.Manifold.riemannianEDist_le_pathELength hγ _ _ zero_le_one
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_zero]
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_one]
  apply hd.trans
  simpa only [← edist_eq_enorm_sub y x, _root_.PseudoEMetricSpace.edist_comm y x] using hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.riemannianEDist_le_mul_edist_of_convex then
    throwError "Refusing to shadow existing declaration Manifold.riemannianEDist_le_mul_edist_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.riemannianEDist_le_mul_edist_of_convex ``Submission.Manifold.riemannianEDist_le_mul_edist_of_convex

end Manifold

end

end
