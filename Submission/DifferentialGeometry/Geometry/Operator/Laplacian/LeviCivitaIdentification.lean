import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Divergence.FrameInvariance
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Geometry.Operator

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem divergence_levi_eq
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence (I := I) (LeviCivita (I := I) g) Z.toFun x =
      divergenceG (I := I) g Z x := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
    let : Subsingleton (TangentSpace I x) :=
      Module.finrank_zero_iff.mp htang
    rw [divergence_eq]
    rw [Subsingleton.elim (LeviCivita (I := I) g Z.toFun x).toLinearMap 0]
    simp only [map_zero, divergence_g_def, localDivergence_def]
    change 0 = (∑ _i : Fin (Module.finrank Real E), _) / _
    have huniv : (Finset.univ : Finset (Fin (Module.finrank Real E))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i _
      have hi0 : i.val < 0 := by
        simpa only [hdim] using i.isLt
      exact (Nat.not_lt_zero _ hi0).elim
    rw [huniv]
    simp
  let : NeZero (Module.finrank Real E) := ⟨hdim⟩
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    have hob := ob.inner_eq_ite i j
    change g.inner x (ob.toBasis i) (ob.toBasis j) =
      if i = j then (1 : Real) else 0
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x)
      (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact hob
  have hinv : MetricInverseInBasis (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0) := by
    intro i j
    constructor <;> simp [hON]
  rw [divergence_eq]
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis
    (fun i j => if i = j then 1 else 0) hinv]
  rw [← metricTracePair0SAt_nablaCov_eq_divergence (I := I) g Z x]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    (fun i j => if i = j then 1 else 0) hinv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [nablaCovTensor_apply]
  simp only [vec2]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.divergence_levi_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.divergence_levi_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.divergence_levi_eq ``Submission.DifferentialGeometry.Geometry.Operator.divergence_levi_eq

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem laplacian_levi_eq
    (g : SmoothRiemannianMetric I M) {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ΔG (I := I) g ⟨_, hf⟩ x := by
  have hdiv := divergence_levi_eq (I := I) g (gradG (I := I) g ⟨_, hf⟩) x
  unfold laplacian ΔG
  have hgrad : gradientFun (I := I) g f = (gradG (I := I) g ⟨f, hf⟩).toFun := by
    funext y
    unfold gradientFun gradG gradFun mvfderiv
    rfl
  rw [hgrad]
  exact hdiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_levi_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_levi_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_levi_eq ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_levi_eq

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem Δ_g_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {f h : M → Real} {x : M}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h)
    (heq : f =ᶠ[nhds x] h) :
    ΔG (I := I) g ⟨f, hf⟩ x = ΔG (I := I) g ⟨h, hh⟩ x := by
  rw [← laplacian_levi_eq (I := I) g hf x]
  rw [← laplacian_levi_eq (I := I) g hh x]
  exact laplacian_congr_of_eventuallyEq (I := I)
    (LeviCivita (I := I) g) g hf.contMDiffAt hh.contMDiffAt heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.Δ_g_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.Δ_g_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.Δ_g_congr_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.Operator.Δ_g_congr_of_eventuallyEq

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
omit [T2Space M] in
theorem Δ_g_neg
    (g : SmoothRiemannianMetric I M) {f : M → Real} {x : M}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    ΔG (I := I) g ⟨fun y => -f y, hf.neg⟩ x =
      -ΔG (I := I) g ⟨f, hf⟩ x := by
  classical
  let F : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  have hadd := Δ_g_add (I := I) g F (-F) x
  have hcancel : ΔG (I := I) g (F + -F) x = 0 := by
    rw [add_neg_cancel]
    exact Δ_g_const (I := I) g (0 : Real) x
  change ΔG (I := I) g (-F) x = -ΔG (I := I) g F x
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.Δ_g_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.Δ_g_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.Δ_g_neg ``Submission.DifferentialGeometry.Geometry.Operator.Δ_g_neg

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem laplacianAt_eq_delta
    (G : MetricConnectionFamily (I := I) (M := M) Real) (t : Real)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (hconn : G.connection t = LeviCivita (I := I) (G.metric t)) (x : M) :
    laplacianAt (I := I) G t f x = ΔG (I := I) (G.metric t) ⟨_, hf⟩ x := by
  unfold laplacianAt
  rw [hconn]
  exact laplacian_levi_eq (I := I) (G.metric t) hf x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacianAt_eq_delta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacianAt_eq_delta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacianAt_eq_delta ``Submission.DifferentialGeometry.Geometry.Operator.laplacianAt_eq_delta

end DifferentialGeometry.Geometry.Operator

end
