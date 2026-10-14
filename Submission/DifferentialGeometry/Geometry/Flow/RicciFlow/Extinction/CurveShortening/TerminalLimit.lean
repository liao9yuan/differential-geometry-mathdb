import Submission.DifferentialGeometry.Geometry.Metric.Family.DerivativeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import Submission.DifferentialGeometry.Analysis.Calculus.LipschitzFamily
import Submission.DifferentialGeometry.Topology.UniformConvergence
import Submission.DifferentialGeometry.Topology.LoopSpace.PeriodicDescent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_norm_mfderiv_curvatureVector_bound
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J K : Set ℝ} (hK : IsCompact K) (hJK : J ⊆ K)
    (hg : DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 K
      (fun t x => DifferentialGeometry.Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {B : ℝ}
    (hcurv : ∀ x t, t ∈ J → c.curvature g x t ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ J →
      ‖(mfderiv I 𝓘(ℝ, F) f (c.lift x t) (c.curvatureVector g x t) : F)‖ ≤ C := by
  obtain ⟨A, hA, hbound⟩ :=
    DifferentialGeometry.Geometry.exists_metric_mfderiv_bound_on_compact_time g hK hg hf
  refine ⟨A * _root_.Max.max B 0, mul_nonneg hA (le_max_right _ _), ?_⟩
  intro x t ht
  exact (hbound t (hJK ht) (c.lift x t) (c.curvatureVector g x t)).trans
    (mul_le_mul_of_nonneg_left ((hcurv x t ht).trans (le_max_left _ _)) hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.exists_norm_mfderiv_curvatureVector_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.exists_norm_mfderiv_curvatureVector_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.exists_norm_mfderiv_curvatureVector_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.exists_norm_mfderiv_curvatureVector_bound

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open scoped _root_.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem CurveMap.IsSolutionOn.hasDerivWithinAt_comp
    {J : Set ℝ} {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M}
    (hc : c.IsSolutionOn (I := I) g J) {f : M → F} {x t : ℝ} (ht : t ∈ J)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f (c.lift x t)) :
    HasDerivWithinAt (fun s : ℝ => f (c.lift x s))
      ((mfderiv I 𝓘(ℝ, F) f (c.lift x t)) (c.curvatureVector g x t)) J t := by
  have hγ := (c.time_slice_contMDiffWithinAt J hc.smooth x t ht).mdifferentiableWithinAt
    (by simp)
  have hcomp := hf.hasMFDerivAt.comp_hasMFDerivWithinAt t hγ.hasMFDerivWithinAt
  have hcompF : HasFDerivWithinAt (fun s : ℝ => f (c.lift x s))
      ((mfderiv I 𝓘(ℝ, F) f (c.lift x t)).comp
        (mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t)) J t :=
    hcomp.hasFDerivWithinAt
  have hderiv := @HasFDerivWithinAt.hasDerivWithinAt ℝ inferInstance F
    inferInstance inferInstance inferInstance (fun s : ℝ => f (c.lift x s)) t J
    inferInstance _ hcompF
  change HasDerivWithinAt (fun s => f (c.lift x s))
    ((mfderiv I 𝓘(ℝ, F) f (c.lift x t)) (c.velocity (I := I) J x t)) J t at hderiv
  rwa [hc.equation x t ht] at hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.hasDerivWithinAt_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.hasDerivWithinAt_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.hasDerivWithinAt_comp ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.hasDerivWithinAt_comp

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem IsSolutionOn.exists_tendstoUniformly_comp_at_terminal
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {a T : ℝ}
    (haT : a < T) (hc : c.IsSolutionOn g (_root_.Set.Ico a T))
    (hg : DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 (_root_.Set.Icc a T)
      (fun t x => DifferentialGeometry.Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {B : ℝ}
    (hcurv : ∀ x t, t ∈ _root_.Set.Ico a T → c.curvature g x t ≤ B) :
    ∃ fT : ℝ → F, TendstoUniformly (fun t x => f (c.lift x t)) fT (𝓝[<] T) := by
  obtain ⟨C, hC, hbound⟩ := c.exists_norm_mfderiv_curvatureVector_bound g
    _root_.CompactIccSpace.isCompact_Icc _root_.Set.Ico_subset_Icc_self hg hf hcurv
  let W : ℝ → ℝ → F := fun t x =>
    mfderiv I 𝓘(ℝ, F) f (c.lift x t) (c.curvatureVector g x t)
  apply exists_tendstoUniformly_nhdsLT_of_hasDerivAt_nnnorm_le haT
    (fun t x => f (c.lift x t)) W ⟨C, hC⟩
  · intro t ht x
    exact (hc.hasDerivWithinAt_comp ⟨ht.1.le, ht.2⟩ (hf.mdifferentiableAt (by norm_num))).hasDerivAt
      (Ico_mem_nhds ht.1 ht.2)
  · intro t ht x
    exact_mod_cast hbound x t ⟨ht.1.le, ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_tendstoUniformly_comp_at_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_tendstoUniformly_comp_at_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_tendstoUniformly_comp_at_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_tendstoUniformly_comp_at_terminal

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem CurveMap.IsSolutionOn.exists_continuous_terminal_curve
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {a T : ℝ}
    (haT : a < T) (hc : c.IsSolutionOn g (_root_.Set.Ico a T))
    (hg : DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 (_root_.Set.Icc a T)
      (fun t x => DifferentialGeometry.Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (hinj : Function.Injective f)
    {K : ℝ} (hcurv : ∀ x t, t ∈ _root_.Set.Ico a T → c.curvature g x t ≤ K) :
    ∃ cT : C(AddCircle (1 : ℝ), M),
      TendstoUniformly (fun t x => f (c.lift x t))
        (fun x : ℝ => f (cT (x : AddCircle (1 : ℝ)))) (𝓝[<] T) ∧
      ∀ θ, _root_.Filter.Tendsto (c θ) (𝓝[<] T) (𝓝 (cT θ)) := by
  have he : Topology.IsClosedEmbedding f := hf.continuous.isClosedEmbedding hinj
  let _ : T2Space M := he.isEmbedding.t2Space
  obtain ⟨fT, hfT⟩ := hc.exists_tendstoUniformly_comp_at_terminal haT hg hf hcurv
  have hcont : ∀ᶠ t in 𝓝[<] T, Continuous (fun x => c.lift x t) := by
    filter_upwards [Ico_mem_nhdsLT haT] with t ht
    exact continuousOn_univ.mp ((c.space_slice_contMDiffOn (_root_.Set.Ico a T) hc.smooth t ht).continuousOn)
  obtain ⟨yT, hyT, hytend⟩ := he.exists_continuousMap_of_tendstoUniformly hfT hcont.frequently
  have hper : Function.Periodic yT 1 := by
    intro x
    apply tendsto_nhds_unique (hytend (x + 1))
    simpa only [CurveMap.lift, AddCircle.coe_add_period] using hytend x
  let cT := DifferentialGeometry.Topology.periodicLoop yT hper yT.continuous
  have hcT : ∀ x : ℝ, cT (x : AddCircle (1 : ℝ)) = yT x := by
    intro x
    exact DifferentialGeometry.Topology.periodicLoop_coe yT hper yT.continuous x
  refine ⟨cT, ?_, ?_⟩
  · have heq : (fun x : ℝ => f (cT (x : AddCircle (1 : ℝ)))) = fT := by
      funext x
      rw [hcT, hyT]
    rwa [heq]
  · intro θ
    let x := AddCircle.equivIco (1 : ℝ) 0 θ
    have hθ : (x.1 : AddCircle (1 : ℝ)) = θ := AddCircle.coe_equivIco
    have ht := hytend x.1
    rw [← hcT, hθ] at ht
    simpa only [CurveMap.lift, hθ] using ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_continuous_terminal_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_continuous_terminal_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_continuous_terminal_curve ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.exists_continuous_terminal_curve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
