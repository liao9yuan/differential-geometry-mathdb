import Submission.DifferentialGeometry.Geometry.Comparison.Splitting.AffineZeroLevelCharts
import Submission.DifferentialGeometry.Geometry.Comparison.Splitting.AffineFlowRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
  {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
  (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
  (hH : ∀ p, hessFun (I := I) g b p = 0)


def affineZeroLevelRetraction (x : M) : {p : M // b p = 0} :=
  ⟨affineGradientFlow (I := I) g hEnorm b x (-b x), by
    rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, add_neg_cancel]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction


theorem affineZeroLevelRetraction_coe (x : M) :
    (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x : M) =
      affineGradientFlow (I := I) g hEnorm b x (-b x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_coe ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_coe


theorem affineZeroLevelRetraction_inclusion (p : {q : M // b q = 0}) :
    affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH p.1 = p := by
  apply Subtype.ext
  change affineGradientFlow (I := I) g hEnorm b p.1 (-b p.1) = p.1
  rw [p.property, neg_zero, affineGradientFlow_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_inclusion ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_inclusion

theorem affineZeroLevelRetraction_contMDiff (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ContMDiff I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ContMDiff I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
    (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH)
  exact affineZeroLevel_corestrict_contMDiff (I := I) g hEnorm hb hunit hH p₀
    (fun x => affineGradientFlow (I := I) g hEnorm b x (-b x))
    ((affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).comp
      (hb.neg.prodMk contMDiff_id))
    (fun x => by
      rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, add_neg_cancel])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_contMDiff ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevelRetraction_contMDiff

def affineFunctionZeroLevelDiffeomorph (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ({p : M // b p = 0} × ℝ) ≃ₘ⟮
      𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ), I⟯ M := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ({p : M // b p = 0} × ℝ) ≃ₘ⟮
    𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ), I⟯ M
  refine
    { toEquiv := affineFunctionZeroLevelEquiv (I := I) g hEnorm hb hunit hH
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).comp
      (contMDiff_snd.prodMk
        ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).comp
          contMDiff_fst))
  · exact (affineZeroLevelRetraction_contMDiff (I := I) g hEnorm hb hunit hH p₀).prodMk hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph ``Submission.DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph


theorem affineFunctionZeroLevelDiffeomorph_apply
    (p₀ p : {q : M // b q = 0}) (t : ℝ) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀ (p, t) =
      affineGradientFlow (I := I) g hEnorm b p.1 t := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_apply


theorem affineFunctionZeroLevelDiffeomorph_symm_apply
    (p₀ : {q : M // b q = 0}) (x : M) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀).symm x =
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x, b x) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelDiffeomorph_symm_apply

theorem affineZeroLevel_inclusion_mfderiv_leftInverse (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ p : {q : M // b q = 0}, Function.LeftInverse
      (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) p.1)
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I
        (Subtype.val : {q : M // b q = 0} → M) p) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ p : {q : M // b q = 0}, Function.LeftInverse
    (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) p.1)
    (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p)
  intro p v
  have h := mfderiv_comp_apply p
    ((affineZeroLevelRetraction_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p.1)
    ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p) v
  have hid : affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH ∘
      (Subtype.val : {q : M // b q = 0} → M) = id :=
    funext (affineZeroLevelRetraction_inclusion (I := I) g hEnorm hb hunit hH)
  rw [hid, mfderiv_id] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_leftInverse ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_leftInverse


theorem affineZeroLevel_inclusion_mfderiv_injective (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ p : {q : M // b q = 0}, Function.Injective
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I
        (Subtype.val : {q : M // b q = 0} → M) p) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  exact fun p =>
    (affineZeroLevel_inclusion_mfderiv_leftInverse (I := I) g hEnorm hb hunit hH p₀ p).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_injective ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mfderiv_injective

theorem affineZeroLevel_inclusion_mvfderiv_eq_zero (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
      mvfderiv (I := I) b p.1
        (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) = 0 := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ (p : {q : M // b q = 0})
    (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
    mvfderiv (I := I) b p.1
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) = 0
  intro p v
  have h := mfderiv_comp_apply p (hb.mdifferentiable (by simp) p.1)
    ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p) v
  have hzero : b ∘ (Subtype.val : {q : M // b q = 0} → M) = fun _ => 0 :=
    funext Subtype.property
  rw [hzero, mfderiv_const, zero_apply] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mvfderiv_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mvfderiv_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mvfderiv_eq_zero ``Submission.DifferentialGeometry.Geometry.Topology.affineZeroLevel_inclusion_mvfderiv_eq_zero

end DifferentialGeometry.Geometry.Topology

end
