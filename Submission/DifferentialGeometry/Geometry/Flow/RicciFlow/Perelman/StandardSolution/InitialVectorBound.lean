import Submission.DifferentialGeometry.Geometry.Metric.Family.TensorNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import Submission.DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow

section LocalHelpers

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lScalarGradient_bound_on_compact
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : ℝ} (hreg : _root_.Set.Icc a b ⊆ D.regular)
    {Cpt : Set M} (hCpt : IsCompact Cpt) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ y ∈ Cpt, ∀ v : TangentSpace I y,
        |(S.base.metric t).inner y
            (gradientFun (I := I) (S.base.metric t) (S.scalar t) y) v| ≤
          C * Real.sqrt ((S.base.metric t).inner y v v) := by
  classical
  let q : ℝ × M → ℝ := fun p ↦
    (S.base.metric p.1).inner p.2
      (gradientFun (I := I) (S.base.metric p.1) (S.scalar p.1) p.2)
      (gradientFun (I := I) (S.base.metric p.1) (S.scalar p.1) p.2)
  have hgram : ∀ (y₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1) y₀ p.2 i j)
        (D.regular ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) y₀).baseSet) := by
    intro y₀ i j
    let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) y₀
    let basis := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    let frame : Fin (Module.finrank ℝ E) → ∀ y, TangentSpace I y :=
      e.localFrame basis
    have hframe : IsLocalFrameOn I E ∞ frame e.baseSet := by
      simpa only [frame] using e.isLocalFrameOn_localFrame_baseSet I ∞ basis
    have hcomp := hS.smoothMetric.frameCompSmooth frame hframe i j
    refine hcomp.congr ?_
    intro p hp
    have hframe_eq (k : Fin (Module.finrank ℝ E)) :
        frame k p.2 = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) y₀ k p.2 := by
      dsimp only [frame]
      rw [e.localFrame_apply_of_mem_baseSet basis hp.2]
      change (e.linearEquivAt ℝ p.2 hp.2).symm (basis k) =
        e.symmL ℝ p.2 ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      dsimp only [basis]
      rw [e.linearEquivAt_symm_apply, e.symmL_apply hp.2]
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, SolutionOn.family_metric]
    rw [hframe_eq i, hframe_eq j]
  have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ q
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
    simpa only [q, SolutionOn.family_metric] using
      gradSq_joint (I := I) S.family.metric D.regular_isOpen hgram
        S.scalar (scalar_joint (I := I) S hS)
  let f : ℝ × M → ℝ := fun p ↦ Real.sqrt (q p)
  have hf : ContinuousOn f (_root_.Set.Icc a b ×ˢ Cpt) := by
    have hcomp := Real.continuous_sqrt.continuousOn.comp
      (hq.continuousOn.mono (Set.prod_mono hreg (_root_.Set.subset_univ Cpt)))
      (fun _ _ ↦ _root_.Set.mem_univ _)
    exact hcomp
  obtain ⟨C₀, hC₀⟩ :=
    bddAbove_def.mp ((isCompact_Icc.prod hCpt).bddAbove_image hf)
  refine ⟨max 0 C₀, le_max_left _ _, ?_⟩
  intro t ht y hy v
  have hgrad : Real.sqrt (q (t, y)) ≤ _root_.Max.max 0 C₀ :=
    (hC₀ (f (t, y)) ⟨(t, y), ⟨ht, hy⟩, rfl⟩).trans (le_max_right _ _)
  have hcs :=
    DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
      (I := I) (M := M) (S.base.metric t) y
      (gradientFun (I := I) (S.base.metric t) (S.scalar t) y) v
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (by simpa only [q] using hgrad) (Real.sqrt_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lScalarGradient_bound_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lScalarGradient_bound_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lScalarGradient_bound_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.lScalarGradient_bound_on_compact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegCurve_reference_integrable [I.Boundaryless]
    (gRef : SmoothRiemannianMetric I M)
    {S : SolutionOn (I := I) (M := M) D} {T : ℝ}
    {alpha : ℝ → M} {x : M} {Z : TangentSpace I x} {b : ℝ}
    (halpha : IsLRegularizedCurveOn S T alpha (_root_.Set.Icc (0 : ℝ) b) x Z) :
    _root_.MeasureTheory.IntegrableOn
      (fun s ↦ gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      (_root_.Set.Icc (0 : ℝ) b) := by
  have hstate : ContinuousOn
      (fun s ↦ (TotalSpace.mk' E (alpha s)
        (lVelocity (I := I) alpha s) : TangentBundle I M))
      (_root_.Set.Icc (0 : ℝ) b) := by
    apply sectionAlongCurve_continuousOn_totalSpace (I := I)
    · intro s hs
      exact (halpha.2.2 s hs).2.1.continuousAt.continuousWithinAt
    · intro s hs
      exact (halpha.2.2 s hs).2.2.1
  let cg : _root_.Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) := gRef.toContinuousRiemannianMetric
  let rb : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have hcont : ContinuousOn
      (fun s ↦ gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      (_root_.Set.Icc (0 : ℝ) b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hinner := Continuous.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _))
      (b := fun s : _root_.Set.Icc (0 : ℝ) b ↦ alpha s)
      (v := fun s : _root_.Set.Icc (0 : ℝ) b ↦ lVelocity (I := I) alpha s)
      (w := fun s : _root_.Set.Icc (0 : ℝ) b ↦ lVelocity (I := I) alpha s)
      hstate.domRestrict hstate.domRestrict
    exact hinner.congr fun _ ↦ rfl
  exact hcont.integrableOn_compact _root_.CompactIccSpace.isCompact_Icc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRegCurve_reference_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRegCurve_reference_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRegCurve_reference_integrable ``Submission.DifferentialGeometry.PDE.RicciFlow.lRegCurve_reference_integrable

end LocalHelpers

section InitialVectors

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lRegInit_bound_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (b A : ℝ) (hb : 0 < b)
    (hreg : _root_.Set.Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (Z : ℕ → TangentSpace I x)
    (hdom : ∀ n, b ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b ≤ A) :
    Bornology.IsBounded (_root_.Set.range Z) := by
  classical
  let alpha : ℕ → ℝ → M := fun n ↦ lRegularizedCurve S T x (Z n)
  have hback (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ _root_.Set.Icc (T - b ^ 2) T := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hclock (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ D.regular := hreg (hback s hs)
  have hcurve (n : ℕ) :
      IsLRegularizedCurveOn S T (alpha n) (_root_.Set.Icc (0 : ℝ) b) x (Z n) := by
    simpa only [alpha, _root_.Set.uIcc_of_le hb.le] using
      lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x (Z n) hb (hdom n)
  have hc1 (n : ℕ) :
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (alpha n) (_root_.Set.Icc (0 : ℝ) b) :=
    lRegularizedCurve_c1On (I := I) S hS T x (Z n) (hdom n)
  have hE (n : ℕ) : _root_.MeasureTheory.IntegrableOn
      (fun s ↦ (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (_root_.Set.Icc (0 : ℝ) b) :=
    lRegCurve_reference_integrable (S.base.metric T) (hcurve n)
  have hkin (n : ℕ) :
      IntervalIntegrable (lRegularizedSpeedSq S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume 0 b :=
    intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le (alpha n) (hc1 n) hclock
  have hLag (n : ℕ) :
      IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume 0 b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le (alpha n) (hc1 n) hclock
  obtain ⟨Cpt, hCpt, himage⟩ :=
    lRegularizedRanges_of_rm (I := I) S hS K T hg alpha x 0 b A
      (by norm_num) hb.le hreg hRm
      (fun n ↦ by simp only [alpha, lRegularizedCurve_zero])
      hc1 hE hkin hLag (fun n ↦ hact n)
  obtain ⟨Cg, hCg, hgrad⟩ :=
    lScalarGradient_bound_on_compact S hS hreg hCpt
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  let C : ℝ := _root_.Max.max Cg P
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg P)
  have hquad := twoTensorQuadBound_of_solutions (I := I)
    (fun _ : ℕ ↦ S) _root_.Set.univ (T - b ^ 2) T K
    (fun _ t ht y _ ↦ hRm t ht y)
  have hpot (n : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) :
      -2 * b ^ 2 * P ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s) :=
    lRegularizedPot_lower_rm (I := I) S K T b hb.le hRm s hs (alpha n s)
  let Bkin : ℝ := 2 * (A - (-2 * b ^ 2 * P) * b)
  have hkinBound (n : ℕ) :
      (∫ s in 0..b, lRegularizedSpeedSq S T (alpha n) s) ≤ Bkin := by
    have h := lRegularizedKinetic_le (I := I) S T (alpha n) 0 b A
      (-2 * b ^ 2 * P) hb.le (hpot n) (hkin n) (hLag n) (hact n)
    simpa only [sub_zero, Bkin] using h
  let Q : ℝ :=
    Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
      (Bkin + b * ((1 + 2 * C * b ^ 2) /
        (1 + 2 * C * b ^ 2 + 4 * C * b)))
  have hmetric (n : ℕ) :
      4 * b * (S.base.metric T).inner x (Z n) (Z n) ≤ Q := by
    apply lRegularizedInitialVector_inner_le_of_integral_speedSq_le (I := I) S hS T b b C b Bkin
      hb le_rfl le_rfl hC (hcurve n)
    · intro s hs
      have hy : alpha n s ∈ Cpt := himage n ⟨s, hs, rfl⟩
      have h := hgrad (T - s ^ 2) (hback s hs) (alpha n s) hy
        (lVelocity (I := I) (alpha n) s)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Cg P)
        (Real.sqrt_nonneg _))
    · intro s hs
      have h := hquad.2 0 (T - s ^ 2) (hback s hs)
        (alpha n s) (_root_.Set.mem_univ _) (lVelocity (I := I) (alpha n) s)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg P)
        (lRegularizedSpeedSq_nonneg (I := I) S T (alpha n) s))
    · exact hkinBound n
  let c : ℝ := metricCoerciveConst (I := I) (S.base.metric T) x
  have hc : 0 < c := metricCoerciveConst_pos (I := I) (S.base.metric T) x
  let d : ℝ := 4 * b * c
  have hd : 0 < d := mul_pos (mul_pos (by norm_num) hb) hc
  have hnorm (n : ℕ) : ‖(Z n : E)‖ ≤ Real.sqrt (Q / d) := by
    have hcoerc : c * ‖(Z n : E)‖ ^ 2 ≤
        (S.base.metric T).inner x (Z n) (Z n) :=
      metricCoerciveConst_le (I := I) (S.base.metric T) x (Z n)
    have hscaled : d * ‖(Z n : E)‖ ^ 2 ≤ Q := by
      calc
        d * ‖(Z n : E)‖ ^ 2 = (4 * b) * (c * ‖(Z n : E)‖ ^ 2) := by
          dsimp only [d]
          ring
        _ ≤ (4 * b) * (S.base.metric T).inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc (mul_nonneg (by norm_num) hb.le)
        _ ≤ Q := hmetric n
    have hsq : ‖(Z n : E)‖ ^ 2 ≤ Q / d := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hscaled
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (norm_nonneg (Z n : E))] using h
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨Real.sqrt (Q / d), ?_⟩
  rintro z ⟨n, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_rm

end InitialVectors

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [I.Boundaryless] in
private theorem l_regularized_potential_lower_on_set
    (S : SolutionOn (I := I) (M := M) D) (K T b : ℝ) (hb : 0 ≤ b)
    {Cpt : Set M}
    (hRm : ∀ t ∈ _root_.Set.Icc (T - b ^ 2) T, ∀ y ∈ Cpt,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) (y : M) (hy : y ∈ Cpt) :
    -2 * b ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) ≤
      2 * s ^ 2 * S.scalar (T - s ^ 2) y := by
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).2 hs.2
  have ht : T - s ^ 2 ∈ _root_.Set.Icc (T - b ^ 2) T :=
    ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hscalar := scalar_abs_le_rm (I := I) (S.base.metric (T - s ^ 2)) y
  have hscalar' : |S.scalar (T - s ^ 2) y| ≤ P := by
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
      metricRm04_apply, P,
      show Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E from rfl]
      using hscalar.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hRm _ ht y hy)) (sq_nonneg _))
  have hP : 0 ≤ P := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have hlow := neg_le_of_abs_le hscalar'
  have hmul := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg s))
  have hsqmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs2 (by norm_num : (0 : ℝ) ≤ 2)) hP
  change -2 * b ^ 2 * P ≤ _
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.l_regularized_potential_lower_on_set
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.l_regularized_potential_lower_on_set target :: scope.openDecls } }

omit [I.Boundaryless] [T2Space M] in
private theorem bounded_range_of_metric_quadratic_bound
    (g : SmoothRiemannianMetric I M) (x : M) {ι : Type*}
    (Z : ι → TangentSpace I x) {b Q : ℝ} (hb : 0 < b)
    (hmetric : ∀ n, 4 * b * g.inner x (Z n) (Z n) ≤ Q) :
    Bornology.IsBounded (_root_.Set.range Z) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).mp hdim
    have : Subsingleton (TangentSpace I x) := by unfold TangentSpace; infer_instance
    have hzero : _root_.Set.range Z ⊆ ({0} : Set (TangentSpace I x)) := by
      intro z hz
      exact Set.mem_singleton_iff.mpr (show (z : E) = 0 from Subsingleton.elim _ _)
    exact (Bornology.isBounded_singleton : Bornology.IsBounded ({0} : Set (TangentSpace I x))).subset hzero
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let c : ℝ := metricCoerciveConst (I := I) g x
  have hc : 0 < c := metricCoerciveConst_pos (I := I) g x
  let d : ℝ := 4 * b * c
  have hd : 0 < d := mul_pos (mul_pos (by norm_num) hb) hc
  have hnorm (n : ι) : ‖(Z n : E)‖ ≤ Real.sqrt (Q / d) := by
    have hcoerc : c * ‖(Z n : E)‖ ^ 2 ≤
        g.inner x (Z n) (Z n) :=
      metricCoerciveConst_le (I := I) g x (Z n)
    have hscaled : d * ‖(Z n : E)‖ ^ 2 ≤ Q := by
      calc
        d * ‖(Z n : E)‖ ^ 2 = (4 * b) * (c * ‖(Z n : E)‖ ^ 2) := by
          dsimp only [d]
          ring
        _ ≤ (4 * b) * g.inner x (Z n) (Z n) :=
          mul_le_mul_of_nonneg_left hcoerc (mul_nonneg (by norm_num) hb.le)
        _ ≤ Q := hmetric n
    have hsq : ‖(Z n : E)‖ ^ 2 ≤ Q / d := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hscaled
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (norm_nonneg (Z n : E))] using h
  refine (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).2
    ⟨Real.sqrt (Q / d), ?_⟩
  rintro z ⟨n, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.bounded_range_of_metric_quadratic_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.bounded_range_of_metric_quadratic_bound target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem l_regularized_potential_integrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b : ℝ) (alpha : ℝ → M)
    (hcarrier : ∀ s ∈ _root_.Set.uIcc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (halphac : ContinuousOn alpha (_root_.Set.uIcc (0 : ℝ) b)) :
    IntervalIntegrable (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) _root_.MeasureTheory.MeasureSpace.volume 0 b := by
  have hpair : ContinuousOn (fun s : ℝ ↦ (T - s ^ 2, alpha s)) (_root_.Set.uIcc (0 : ℝ) b) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk halphac
  have hmaps : _root_.Set.MapsTo (fun s : ℝ ↦ (T - s ^ 2, alpha s)) (_root_.Set.uIcc (0 : ℝ) b)
      (D.carrier ×ˢ (_root_.Set.univ : Set M)) := fun s hs ↦ ⟨hcarrier s hs, _root_.Set.mem_univ _⟩
  have hscalar : ContinuousOn (fun s : ℝ ↦ S.scalar (T - s ^ 2) (alpha s))
      (_root_.Set.uIcc (0 : ℝ) b) := by
    have hsc : ContinuousOn (fun p : ℝ × M ↦ S.scalar p.1 p.2)
        (D.carrier ×ˢ (_root_.Set.univ : Set M)) :=
      hS.scalarCont
    simpa only [Function.comp_def] using hsc.comp hpair hmaps
  exact ((continuous_const.mul (continuous_id.pow 2)).continuousOn.mul hscalar).intervalIntegrable

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.l_regularized_potential_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.l_regularized_potential_integrable target :: scope.openDecls } }

private theorem l_regularized_kinetic_le_on_set
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b A K : ℝ) (hb : 0 < b)
    (hreg : _root_.Set.Icc (T - b ^ 2) T ⊆ D.regular)
    {Cpt : Set M}
    (hRm : ∀ t ∈ _root_.Set.Icc (T - b ^ 2) T, ∀ y ∈ Cpt,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (alpha : ℝ → M) {x : M} {Z : TangentSpace I x}
    (halpha : IsLRegularizedCurveOn S T alpha (_root_.Set.Icc (0 : ℝ) b) x Z)
    (himage : alpha '' _root_.Set.Icc (0 : ℝ) b ⊆ Cpt)
    (hact : lRegularizedAction S T alpha 0 b ≤ A) :
    (∫ s in 0..b, lRegularizedSpeedSq S T alpha s) ≤
      2 * (A - (-2 * b ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K)) * b) := by
  have hclock (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) : T - s ^ 2 ∈ D.regular := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact hreg ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hscont : ContinuousOn (lRegularizedSpeedSq S T alpha) (_root_.Set.Icc (0 : ℝ) b) := by
    intro s hs
    exact (hasDerivAt_lRegularizedSpeedSq (I := I) S hS T halpha hs).continuousAt.continuousWithinAt
  have hkin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [_root_.Set.uIcc_of_le hb.le] using hscont
  have hcarrier : ∀ s ∈ _root_.Set.uIcc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hclock s (by simpa only [_root_.Set.uIcc_of_le hb.le] using hs))
  have halphac : ContinuousOn alpha (_root_.Set.uIcc (0 : ℝ) b) := by
    rw [_root_.Set.uIcc_of_le hb.le]
    intro s hs
    exact (halpha.2.2 s hs).2.1.continuousAt.continuousWithinAt
  have hpotential : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) _root_.MeasureTheory.MeasureSpace.volume 0 b :=
    l_regularized_potential_integrable S hS T b alpha hcarrier halphac
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume 0 b :=
    (hkin.const_mul (1 / 2 : ℝ)).add hpotential
  have hpot (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) :
      -2 * b ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) ≤
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) :=
    l_regularized_potential_lower_on_set S K T b hb.le hRm s hs
      (alpha s) (himage ⟨s, hs, rfl⟩)
  have h := lRegularizedKinetic_le (I := I) S T alpha 0 b A
    (-2 * b ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K))
    hb.le hpot hkin hLag hact
  simpa only [sub_zero] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.l_regularized_kinetic_le_on_set
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.l_regularized_kinetic_le_on_set target :: scope.openDecls } }

theorem lRegInit_bound_of_compact_range
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ)
    (x : M) (b A : ℝ) (hb : 0 < b)
    (hreg : _root_.Set.Icc (T - b ^ 2) T ⊆ D.regular)
    {Cpt : Set M} (hCpt : IsCompact Cpt)
    {ι : Type*} (Z : ι → TangentSpace I x)
    (hdom : ∀ n, b ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b ≤ A)
    (himage : ∀ n, lRegularizedCurve S T x (Z n) '' _root_.Set.Icc (0 : ℝ) b ⊆ Cpt) :
    Bornology.IsBounded (_root_.Set.range Z) := by
  classical
  let alpha : ι → ℝ → M := fun n ↦ lRegularizedCurve S T x (Z n)
  have hback (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ _root_.Set.Icc (T - b ^ 2) T := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hcurve (n : ι) :
      IsLRegularizedCurveOn S T (alpha n) (_root_.Set.Icc (0 : ℝ) b) x (Z n) := by
    simpa only [alpha, _root_.Set.uIcc_of_le hb.le] using
      lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x (Z n) hb (hdom n)
  have hcarrier : _root_.Set.Icc (T - b ^ 2) T ⊆ D.carrier := hreg.trans D.regular_subset
  obtain ⟨K, hRm⟩ := exists_normSq0S_le_of_isCompact
    S.base.metric (fun t y ↦ S.base.rm04 t y)
    (hS.smoothMetric.metricTensor_cont.mono hcarrier)
    (hS.rm04Cont.mono hcarrier) _root_.CompactIccSpace.isCompact_Icc hCpt
  obtain ⟨Cg, hCg, hgrad⟩ :=
    lScalarGradient_bound_on_compact S hS hreg hCpt
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  let C : ℝ := _root_.Max.max Cg P
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg P)
  have hquad := twoTensorQuadBound_of_solutions (I := I)
    (fun _ : ℕ ↦ S) Cpt (T - b ^ 2) T K
    (fun _ t ht y hy ↦ hRm t ht y hy)
  let Bkin : ℝ := 2 * (A - (-2 * b ^ 2 * P) * b)
  have hkinBound (n : ι) :
      (∫ s in 0..b, lRegularizedSpeedSq S T (alpha n) s) ≤ Bkin :=
    l_regularized_kinetic_le_on_set S hS T b A K hb hreg hRm (alpha n)
      (hcurve n) (himage n) (hact n)
  let Q : ℝ :=
    Real.exp ((1 + 2 * C * b ^ 2 + 4 * C * b) * b) *
      (Bkin + b * ((1 + 2 * C * b ^ 2) /
        (1 + 2 * C * b ^ 2 + 4 * C * b)))
  have hmetric (n : ι) :
      4 * b * (S.base.metric T).inner x (Z n) (Z n) ≤ Q := by
    apply lRegularizedInitialVector_inner_le_of_integral_speedSq_le (I := I) S hS T b b C b Bkin
      hb le_rfl le_rfl hC (hcurve n)
    · intro s hs
      have hy : alpha n s ∈ Cpt := himage n ⟨s, hs, rfl⟩
      have h := hgrad (T - s ^ 2) (hback s hs) (alpha n s) hy
        (lVelocity (I := I) (alpha n) s)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Cg P)
        (Real.sqrt_nonneg _))
    · intro s hs
      have h := hquad.2 0 (T - s ^ 2) (hback s hs)
        (alpha n s) (himage n ⟨s, hs, rfl⟩) (lVelocity (I := I) (alpha n) s)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg P)
        (lRegularizedSpeedSq_nonneg (I := I) S T (alpha n) s))
    · exact hkinBound n
  exact bounded_range_of_metric_quadratic_bound (S.base.metric T) x Z hb hmetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_compact_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_compact_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_compact_range ``Submission.DifferentialGeometry.PDE.RicciFlow.lRegInit_bound_of_compact_range

end DifferentialGeometry.PDE.RicciFlow

end
