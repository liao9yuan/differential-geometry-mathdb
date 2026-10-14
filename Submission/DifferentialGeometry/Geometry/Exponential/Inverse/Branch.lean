import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import Submission.DifferentialGeometry.Geometry.Exponential.ConjugatePoint.Basic
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.IntrinsicDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

section ChartDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private def modelMFDerivAt (f : E → M) (u : E) : E →L[Real] E :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) (f u)).toContinuousLinearMap.comp
    ((mfderiv 𝓘(Real, E) I f u).comp
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) u).symm.toContinuousLinearMap)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.modelMFDerivAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.modelMFDerivAt target :: scope.openDecls } }

theorem hasFDerivAt_chart
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u) :
    HasFDerivAt
      ((extChartAt I (f u)) ∘ f)
      (modelMFDerivAt (I := I) f u)
      u := by
  have hf' : HasMFDerivAt 𝓘(Real, E) I f u
      (mfderiv 𝓘(Real, E) I f u) :=
    hf.hasMFDerivAt
  have hchart : HasMFDerivAt I 𝓘(Real, E) (extChartAt I (f u)) (f u)
      (ContinuousLinearMap.id Real E) := by
    have h :=
      (mdifferentiableAt_extChartAt (I := I)
        (mem_chart_source H (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := f u)] at h
    exact h
  have hcomp : HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E)
      ((extChartAt I (f u)) ∘ f) u
      ((ContinuousLinearMap.id Real E).comp
        (mfderiv 𝓘(Real, E) I f u)) :=
    hchart.comp u hf'
  have hcomp' := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  exact hcomp'.congr_fderiv (by
    ext v
    with_unfolding_all rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.hasFDerivAt_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.hasFDerivAt_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.hasFDerivAt_chart ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.hasFDerivAt_chart

end ChartDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [Module.Finite Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

structure ExponentialInverseBranch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) where
  hom : PartialDiffeomorph 𝓘(Real, E) I E M ∞
  hom_eq :
    _root_.Set.EqOn
      (fun u : E =>
        expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u))
      hom
      hom.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch

namespace ExponentialInverseBranch

def inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) : M → E :=
  B.hom.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv

def dom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) : Set M :=
  B.hom.target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.dom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.dom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.dom ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.dom

theorem right_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {y : M} (hy : y ∈ B.dom) :
    expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv y)) = y := by
  have hu : B.inv y ∈ B.hom.source := B.hom.map_target hy
  calc
    expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv y)) =
      B.hom (B.inv y) := B.hom_eq hu
    _ = y := B.hom.right_inv hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.right_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.right_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.right_inv ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.right_inv

theorem left_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : E} (hu : u ∈ B.hom.source) :
    B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)) = u := by
  calc
    B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)) =
      B.inv (B.hom u) := congrArg B.inv (B.hom_eq hu)
    _ = u := B.hom.left_inv hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.left_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.left_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.left_inv ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.left_inv

theorem inv_contMDiffOn
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    ContMDiffOn I 𝓘(Real, E) ∞ B.inv B.dom := by
  exact B.hom.contMDiffOn_invFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.inv_contMDiffOn

end ExponentialInverseBranch

private theorem branch_of_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {u : E}
    (hu : Function.Injective
      (modelMFDerivAt (I := I)
        (fun z : E =>
          expMapIntrinsic (I := I) g hEnorm p
            ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z))
        u)) :
    ∃ B : ExponentialInverseBranch (I := I) g hEnorm p, u ∈ B.hom.source := by
  classical
  let f : E → M := fun z : E =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z)
  have hf : ContMDiff 𝓘(Real, E) I ∞ f :=
    intrinsicFiber_smooth (I := I) g hEnorm p
  let A := modelMFDerivAt (I := I) f u
  have hAinj : Function.Injective A := by
    simpa only [f, A] using hu
  have hAsurj : Function.Surjective A :=
    LinearMap.surjective_of_injective hAinj
  let D : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hAinj)
      (LinearMap.range_eq_top.mpr hAsurj)
  have hAinv : A.IsInvertible := by
    refine ⟨D, ?_⟩
    rfl
  have hDinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible := by
    simpa only [A, modelMFDerivAt, ContinuousLinearMap.isInvertible_comp_equiv,
      ContinuousLinearMap.isInvertible_equiv_comp] using hAinv
  have hfu : MDifferentiableAt 𝓘(Real, E) I f u :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hfd_u : (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible :=
    hfu.isInvertible_mfderiv_iff.mp hDinv
  have hf1 : ContMDiffAt 𝓘(Real, E) I 1 f u :=
    hf.contMDiffAt.of_le (by exact_mod_cast le_top)
  obtain ⟨Ψ, huΨ, hEqΨ⟩ :=
    Coordinates.contMDiffAt_isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I)
      (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hf1 hfd_u
  have hinv_source : ∀ z ∈ Ψ.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I z f)
        (extChartAt 𝓘(Real, E) z z)).IsInvertible := by
    intro z hz
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f z :=
      ⟨Ψ, hz, hEqΨ⟩
    have hDzinv : (mfderiv 𝓘(Real, E) I f z).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    exact (hf.contMDiffAt.mdifferentiableAt (by simp)).isInvertible_mfderiv_iff.mp hDzinv
  obtain ⟨Φ, huΦ, -, hEqΦ⟩ :=
    Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty (I := 𝓘(Real, E)) (J := I)
      Ψ.open_source huΨ hf.contMDiffOn hinv_source
  exact ⟨⟨Φ, hEqΦ⟩, huΦ⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.branch_of_inj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.branch_of_inj target :: scope.openDecls } }

theorem branch_of_not_conj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {u : TangentSpace I p}
    (hu : ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u)) :
    ∃ B : ExponentialInverseBranch (I := I) g hEnorm p,
      tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source := by
  classical
  apply branch_of_inj (I := I) g hEnorm
  have hu' : Function.Injective fun w : E =>
      mfderiv 𝓘(Real, E) I
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm w) :=
    Classical.not_not.mp (by
      with_unfolding_all exact hu)
  intro v w hvw
  apply hu'
  exact (tangentSpaceModelContinuousLinearEquiv (I := I)
    (expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) p u)))).injective hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.branch_of_not_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.branch_of_not_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.branch_of_not_conj ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.branch_of_not_conj

namespace ExponentialInverseBranch

theorem not_conj
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source) :
    ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u) := by
  classical
  let f : E → M := fun z : E =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z)
  have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I ∞ f
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u) :=
    ⟨B.hom, hu, B.hom_eq⟩
  let D := hloc.mfderivToContinuousLinearEquiv (by simp)
  have hinj := D.injective
  intro hconj
  have hnotinj : ¬ Function.Injective fun w : E =>
      mfderiv 𝓘(Real, E) I f (tangentSpaceModelContinuousLinearEquiv (I := I) p u)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm w) := by
    with_unfolding_all exact hconj
  apply hnotinj
  intro v w hvw
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(Real, E))
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm.injective
  exact hinj hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.not_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.not_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.not_conj ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch.not_conj

end ExponentialInverseBranch

theorem exists_exponentialInverseBranch_zero_mem
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) :
    ∃ B : ExponentialInverseBranch g hEnorm p, (0 : E) ∈ B.hom.source := by
  have hzero : ¬ IsConjVec (I := I) g hEnorm p (0 : E) := by
    unfold IsConjVec
    simp only [_root_.Classical.not_not]
    have hfun : (fun b : E => expMapIntrinsic g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm b)) =
        fun b : E => expMapIntrinsic g hEnorm p (show TangentSpace I p from b) := by
      funext b
      rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    rw [hfun, mfderiv_expMapIntrinsic_at_zero g hEnorm p]
    intro a b hab
    have habModel := congrArg (tangentSpaceModelContinuousLinearEquiv (I := I)
      (expMapIntrinsic g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (0 : E)))) hab
    change a = b at habModel
    exact habModel
  obtain ⟨B, hB⟩ := branch_of_not_conj g hEnorm (u := (0 : TangentSpace I p))
    (by simpa only [map_zero] using hzero)
  exact ⟨B, by simpa only [map_zero] using hB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.exists_exponentialInverseBranch_zero_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.exists_exponentialInverseBranch_zero_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.exists_exponentialInverseBranch_zero_mem ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.exists_exponentialInverseBranch_zero_mem

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
