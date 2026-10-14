import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Restart.SolutionBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Limit.Smooth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Limit.CurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.LinearAlgebra
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Product
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Calculus.CovariantDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [T2Space M]
variable [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]

def SolutionAgreesOn
    {D Dhat : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Shat : SolutionOn (I := I) (M := M) Dhat)
    (U : Set Real) : Prop :=
  forall t : Real, t ∈ U ->
    S.family.metric t = Shat.family.metric t ∧
      S.family.connection t = Shat.family.connection t ∧
        S.ricci t = Shat.ricci t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionAgreesOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionAgreesOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionAgreesOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionAgreesOn

def ExtendsPastEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)) :
        Prop :=
  ∃ eps : Real, 0 < eps ∧
    ∃ hwide : alpha < omega + eps,
      ∃ Shat : SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha (omega + eps)
          hwide),
        IsSolutionOn (I := I) Shat ∧
          SolutionAgreesOn (I := I) S Shat (Set.Ico alpha omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ExtendsPastEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ExtendsPastEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ExtendsPastEndpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.ExtendsPastEndpoint

def IsMaximalAtEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)) :
        Prop :=
  ¬ ExtendsPastEndpoint (I := I) hαω S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsMaximalAtEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsMaximalAtEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsMaximalAtEndpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.IsMaximalAtEndpoint

def Rm04RealizesSolutionConnectionOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)) :
      Prop :=
  forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D,
    DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection (I := I)
      (S.family.metric (t : Real)) (S.family.connection (t : Real))
      (Rm04 (t : Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04RealizesSolutionConnectionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04RealizesSolutionConnectionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04RealizesSolutionConnectionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04RealizesSolutionConnectionOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] in
theorem rm04Realizes_metric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Rm04RealizesSolutionConnectionOn (I := I) S S.base.rm04 := by
  intro t
  simpa [SolutionOn.family, SolutionFamily.rm04, SolutionFamily.connection,
    metricCov, metricRm04] using
    (DifferentialGeometry.Geometry.Curvature.rm04Section_realizes (I := I) (M := M)
      (S.base.metric (t : Real))
      (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
      (metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04Realizes_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04Realizes_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04Realizes_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04Realizes_metric

def curvatureNormSq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureNormSq

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [BoundarylessManifold I M] [I.Boundaryless] in
@[simp] theorem curvatureNormSq_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (t : Real) (x : M) :
    curvatureNormSq (I := I) S Rm04 t x =
      Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureNormSq_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureNormSq_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureNormSq_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureNormSq_apply

def Rm04NormSqUnboundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)) :
      Prop :=
  forall K : Real, ∃ t : Real, ∃ x : M,
    alpha <= t ∧ t < omega ∧ K < curvatureNormSq (I := I) S Rm04 t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormSqUnboundedAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormSqUnboundedAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormSqUnboundedAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormSqUnboundedAt

def Rm04NormSqBoundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)) :
      Prop :=
  ∃ K : Real, forall t : Real, forall x : M,
    alpha <= t -> t < omega ->
      curvatureNormSq (I := I) S Rm04 t x <= K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormSqBoundedAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormSqBoundedAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormSqBoundedAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormSqBoundedAt

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [BoundarylessManifold I M] [I.Boundaryless] in
theorem rmBounded_of_not_unbounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)}
    (hnot : ¬ Rm04NormSqUnboundedAt (I := I) S Rm04) :
    Rm04NormSqBoundedAt (I := I) S Rm04 := by
  classical
  unfold Rm04NormSqUnboundedAt at hnot
  simp only [_root_.Classical.not_forall, not_exists, not_and, not_lt] at hnot
  rcases hnot with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro t x ht hT
  exact hK t x ht hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmBounded_of_not_unbounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmBounded_of_not_unbounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmBounded_of_not_unbounded ``Submission.DifferentialGeometry.PDE.RicciFlow.rmBounded_of_not_unbounded

theorem extends_of_rmBounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank ℝ E = 3)
    (_hS : IsSolutionOn (I := I) S)
    (_hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    (_hbound : Rm04NormSqBoundedAt (I := I) S Rm04) :
    ExtendsPastEndpoint (I := I) hαω S := by
  let g_fam := S.base.metric
  have hleft := ricciFlowPDE_Ici_of_solution (I := I) _hS
  obtain ⟨K', hK'bound⟩ := _hbound
  have hbound_raw : ∀ t : ℝ, ∀ x : M, alpha ≤ t → t < omega →
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 ((Rm04 t) x) ≤ K' := by
    intro t x ht1 ht2
    have h := hK'bound t x ht1 ht2
    simpa [curvatureNormSq, SolutionOn.family] using h
  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    have h := _hRm ⟨t, ht⟩
    simpa [SolutionOn.family, SolutionFamily.connection, metricCov] using h
  have hric := ric_quad_le_of_solution (I := I) hRmRaw hbound_raw
  have hbound_can := canonical_curvature_norm_sq_bounded_of_realization
    (I := I) Rm04 hRmRaw ⟨K', hbound_raw⟩
  obtain ⟨hell, hcov⟩ := exists_metric_equivalence_and_covariant_derivative_bounds_of_solution (I := I) hdim _hS
    (K := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K') (by positivity) hric hbound_can
  obtain ⟨t_star, ht_star, TT, hreach, rr, hrr0, hrr_smooth, hrr_cont, hrr_pde⟩ :=
    ricci_flow_interior_restart (I := I) hdim g_fam hαω hell hcov
  have ht0 : alpha < t_star := ht_star.1
  have ht1 : alpha ≤ t_star := ht_star.1.le
  have ht2 : t_star < omega := ht_star.2
  have hsmooth_left := fun (x₀ : M) (i j : Fin (Module.finrank ℝ E)) =>
    chartGram_smooth_of_solution (I := I) _hS x₀ i j
  have hcont_left := fun (x₀ : M) (i j : Fin (Module.finrank ℝ E)) =>
    chartGram_cont_of_solution (I := I) _hS x₀ i j
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => ((p.1 - t_star, p.2) : ℝ × M)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  have h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (rr (p.1 - t_star)) x₀ p.2 i j)
        (Set.Ico t_star omega ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun q : ℝ × M => ((q.1 - t_star, q.2) : ℝ × M))
        (Set.Ico t_star omega ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ico (0 : ℝ) TT ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :=
      fun q hq => ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2, hreach]⟩, hq.2⟩
    have h := (hrr_smooth x₀ i j).comp hshift.contMDiffOn hmaps
    exact h
  have h2pde : ∀ t ∈ Set.Ico t_star omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (rr (s - t_star)).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (rr (t - t_star)) x v w) (Set.Ici t_star) t := by
    intro t ht x v w
    have hmem : t - t_star ∈ Set.Ico (0 : ℝ) TT :=
      ⟨by linarith [ht.1], by linarith [ht.2, hreach]⟩
    have hd := hrr_pde (t - t_star) hmem x v w
    have hφ : HasDerivWithinAt (fun s : ℝ => s - t_star) 1 (Set.Ici t_star) t :=
      (hasDerivWithinAt_id t (Set.Ici t_star)).sub_const t_star
    have hmapsφ : Set.MapsTo (fun s : ℝ => s - t_star) (Set.Ici t_star) (Set.Ici 0) :=
      fun s hs => by simp only [Set.mem_Ici] at hs ⊢; linarith
    have hchain := hd.comp t hφ hmapsφ
    change HasDerivWithinAt
      ((fun u : ℝ => (rr u).inner x v w) ∘ fun s : ℝ => s - t_star)
      ((-2 : ℝ) * ricciTensor (I := I) (rr (t - t_star)) x v w)
      (Set.Ici t_star) t
    simpa only [mul_one] using hchain
  have h1pde : ∀ t ∈ Set.Ico t_star omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici t_star) t :=
    fun t ht x v w =>
      (hleft t ⟨le_trans ht1 ht.1, ht.2⟩ x v w).mono (Set.Ici_subset_Ici.mpr ht1)
  have h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ico t_star omega ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hsmooth_left x₀ i j).mono
      (Set.prod_mono (fun s hs => ⟨lt_of_lt_of_le ht0 hs.1, hs.2⟩) (le_refl _))
  have h0 : g_fam t_star = (fun t : ℝ => rr (t - t_star)) t_star := by
    simp only [sub_self]; exact hrr0.symm
  have hagree_overlap : ∀ s ∈ Set.Ico t_star omega, rr (s - t_star) = g_fam s :=
    fun s hs =>
      (ricci_flow_forward_unique (I := I) g_fam (fun t => rr (t - t_star)) ht2
        h1smooth h2smooth h1pde h2pde h0 s hs).symm
  obtain ⟨ε, hε, g_ext, hagree, _hsmooth, _hcont, hpde⟩ :=
    extend_construction_of_restart (I := I) g_fam hleft hsmooth_left hcont_left
      ht1 ht2 hreach rr
      (fun x₀ i j => (hrr_smooth x₀ i j).mono
        (Set.prod_mono Set.Ioo_subset_Ico_self (le_refl _)))
      hrr_cont hrr_pde hagree_overlap
  have hwide : alpha < omega + ε := by linarith
  let Shat : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha (omega + ε)
        hwide) :=
    { base := { metric := g_ext } }
  refine ⟨ε, hε, hwide, Shat, ?_, ?_⟩
  · exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_metric_extension
      hwide hαω g_ext S _hS hagree _hsmooth _hcont hpde
  · intro t ht
    have htlt : t < omega := ht.2
    have hteq : g_ext t = g_fam t := hagree t htlt
    refine ⟨?_, ?_, ?_⟩
    · show S.family.metric t = Shat.family.metric t
      change S.base.metric t = g_ext t
      exact hteq.symm
    · change S.family.connection t = Shat.family.connection t
      change S.base.connection t = (SolutionFamily.connection { metric := g_ext }) t
      simp only [SolutionFamily.connection]
      congr 1; exact hteq.symm
    · show S.ricci t = Shat.ricci t
      change S.base.ricci t = SolutionFamily.ricci { metric := g_ext } t
      simp only [SolutionFamily.ricci]
      congr 1; exact hteq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.extends_of_rmBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.extends_of_rmBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.extends_of_rmBounded ``Submission.DifferentialGeometry.PDE.RicciFlow.extends_of_rmBounded

theorem rmUnbounded_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    Rm04NormSqUnboundedAt (I := I) S Rm04 := by
  by_contra hnot
  exact hmax (extends_of_rmBounded (I := I) hdim hS hRm
    (rmBounded_of_not_unbounded (I := I) hnot))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmUnbounded_of_maximal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmUnbounded_of_maximal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmUnbounded_of_maximal ``Submission.DifferentialGeometry.PDE.RicciFlow.rmUnbounded_of_maximal

def FormsSingularityAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)) :
        Prop :=
  ∃ Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M),
    Rm04RealizesSolutionConnectionOn (I := I) S Rm04 ∧
      Rm04NormSqUnboundedAt (I := I) S Rm04

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FormsSingularityAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FormsSingularityAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FormsSingularityAt ``Submission.DifferentialGeometry.PDE.RicciFlow.FormsSingularityAt

theorem formsSing_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRmEx :
      ∃ Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M),
        Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    FormsSingularityAt (I := I) S := by
  rcases hRmEx with ⟨Rm04, hRm⟩
  exact ⟨Rm04, hRm, rmUnbounded_of_maximal (I := I) hdim hS hmax hRm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal ``Submission.DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal

theorem formsSing_of_maximal_metric
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S) :
    FormsSingularityAt (I := I) S := by
  exact formsSing_of_maximal (I := I) hdim hS hmax
    ⟨S.base.rm04, rm04Realizes_metric (I := I) S⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.formsSing_of_maximal_metric

def SingularIffMaximalAtEndpoint
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hαω)) :
        Prop :=
  FormsSingularityAt (I := I) S ↔
    IsMaximalAtEndpoint (I := I) hαω S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SingularIffMaximalAtEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SingularIffMaximalAtEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SingularIffMaximalAtEndpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.SingularIffMaximalAtEndpoint

end DifferentialGeometry.PDE.RicciFlow
