import Submission.DifferentialGeometry.Analysis.Calculus.ContinuousMapDerivative
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.TimeLaplacian
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private theorem smoothToH1ComplDirichlet_time_regular
    (q : SmoothRiemannianMetric I_hs M) (v v' : ℝ → SmoothScalarDirichlet q)
    {J : Set ℝ} (hJ : IsOpen J)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t)
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ (I_hs).interior M)
    (hv'K : ∀ t ∈ J, tsupport (v' t).toFun ⊆ K) :
    ContDiffOn ℝ 1 (fun t => smoothToH1ComplDirichlet q (v t)) J ∧
      ∀ t ∈ J, HasDerivAt (fun s => smoothToH1ComplDirichlet q (v s))
        (smoothToH1ComplDirichlet q (v' t)) t := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I_hs) (M := M) q
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I_hs) (M := M) q
  let F : ℝ → C(M, ℝ) := fun t =>
    ⟨(v t).oneSubLaplacian.toFun, (v t).oneSubLaplacian.smooth.continuous⟩
  let F' : ℝ → C(M, ℝ) := fun t =>
    ⟨(v' t).oneSubLaplacian.toFun, (v' t).oneSubLaplacian.smooth.continuous⟩
  have hF' : ContinuousOn (fun p : ℝ × M => F' p.1 p.2) (J ×ˢ _root_.Set.univ) :=
    hv'.continuousOn.sub (continuousOn_Δ_g_with_boundary_prod q
      (fun t => (v' t).toFun) (fun t => (v' t).smooth)
      (fun t => (v' t).interior_support) hJ hv' hK hKi hv'K)
  have hFd (t : ℝ) (ht : t ∈ J) (x : M) :
      HasDerivAt (fun s => F s x) (F' t x) t :=
    (hd t ht x).fun_sub (hasDerivAt_Δ_g_with_boundary q (fun s => (v s).toFun)
      (fun s => (v s).smooth) (fun s => (v s).interior_support) hJ hv ht
      (v' t).smooth (v' t).interior_support (hd t ht) x)
  have hFC1 := ContinuousMap.contDiffOn_one_of_hasDerivAt_apply hJ hF' hFd
  let L : C(M, ℝ) →L[ℝ] H1ComplDirichlet q :=
    (resolventDirichlet q).comp (ContinuousMap.toLp 2 μ ℝ)
  have hLeq (t : ℝ) : L (F t) = smoothToH1ComplDirichlet q (v t) := by
    rw [smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap]
    apply congrArg (resolventDirichlet q)
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp μ (F t)).trans
      (MemLp.coeFn_toLp (v t).oneSubLap_memLp).symm
  have hLeq' (t : ℝ) : L (F' t) = smoothToH1ComplDirichlet q (v' t) := by
    rw [smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap]
    apply congrArg (resolventDirichlet q)
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp μ (F' t)).trans
      (MemLp.coeFn_toLp (v' t).oneSubLap_memLp).symm
  constructor
  · exact (L.contDiff.comp_contDiffOn hFC1).congr fun t _ => (hLeq t).symm
  · intro t ht
    have hFder : HasDerivAt F (F' t) t :=
      ContinuousMap.hasDerivAt_of_hasDerivAt_apply
        ((ContinuousMap.continuousOn_of_continuousOn_uncurry F' hF').continuousAt
          (hJ.mem_nhds ht))
        (Filter.eventually_of_mem (hJ.mem_nhds ht) fun s hs => hFd s hs)
    have h := L.hasFDerivAt.comp_hasDerivAt t hFder
    rw [hLeq'] at h
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s => (hLeq s).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothToH1ComplDirichlet_time_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothToH1ComplDirichlet_time_regular target :: scope.openDecls } }

theorem contDiffOn_one_smoothToH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (v v' : ℝ → SmoothScalarDirichlet q)
    {J : Set ℝ} (hJ : IsOpen J)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t)
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ (I_hs).interior M)
    (hv'K : ∀ t ∈ J, tsupport (v' t).toFun ⊆ K) :
    ContDiffOn ℝ 1 (fun t => smoothToH1ComplDirichlet q (v t)) J :=
  (smoothToH1ComplDirichlet_time_regular q v v' hJ hv hv' hd hK hKi hv'K).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.contDiffOn_one_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.contDiffOn_one_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.contDiffOn_one_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.contDiffOn_one_smoothToH1ComplDirichlet

theorem hasDerivAt_smoothToH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (v v' : ℝ → SmoothScalarDirichlet q)
    {J : Set ℝ} (hJ : IsOpen J)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t)
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ (I_hs).interior M)
    (hv'K : ∀ t ∈ J, tsupport (v' t).toFun ⊆ K)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => smoothToH1ComplDirichlet q (v s))
      (smoothToH1ComplDirichlet q (v' t)) t :=
  (smoothToH1ComplDirichlet_time_regular q v v' hJ hv hv' hd hK hKi hv'K).2 t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.hasDerivAt_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.hasDerivAt_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.hasDerivAt_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.hasDerivAt_smoothToH1ComplDirichlet

theorem exists_timeH1_smoothToH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (v v' : ℝ → SmoothScalarDirichlet q)
    {J : Set ℝ} (hJ : IsOpen J)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (J ×ˢ _root_.Set.univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t)
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ (I_hs).interior M)
    (hv'K : ∀ t ∈ J, tsupport (v' t).toFun ⊆ K)
    {T : ℝ} (hT : 0 ≤ T) (hTJ : _root_.Set.Icc (0 : ℝ) T ⊆ J) (hvT : v T = 0) :
    ∃ w : timeH1 (H1ComplDirichlet q) T,
      _root_.Set.EqOn w.toFun (fun t => smoothToH1ComplDirichlet q (v t)) (_root_.Set.Icc (0 : ℝ) T) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => smoothToH1ComplDirichlet q (v' t)) ∧
      w.initial = smoothToH1ComplDirichlet q (v 0) ∧ w.toFun T = 0 := by
  obtain ⟨hC1, hder⟩ := smoothToH1ComplDirichlet_time_regular q v v' hJ hv hv' hd hK hKi hv'K
  let w := timeH1.ofContDiffOn hT (fun t => smoothToH1ComplDirichlet q (v t))
    (hC1.mono hTJ)
  have hw : _root_.Set.EqOn w.toFun (fun t => smoothToH1ComplDirichlet q (v t))
      (_root_.Set.Icc (0 : ℝ) T) := timeH1.toFun_ofContDiffOn hT _ (hC1.mono hTJ)
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ _root_.Set.Icc (0 : ℝ) T :=
      _root_.MeasureTheory.self_mem_ae_restrict measurableSet_Icc
    filter_upwards [timeH1.deriv_ofContDiffOn hT
      (fun t => smoothToH1ComplDirichlet q (v t)) (hC1.mono hTJ), hmem] with t ht htJ
    exact ht.trans (hder t (hTJ htJ)).deriv
  · exact (timeH1.toFun_zero w).symm.trans (hw ⟨le_rfl, hT⟩)
  · rw [hw ⟨hT, le_rfl⟩]
    change smoothToH1ComplDirichlet q (v T) = 0
    rw [hvT, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_smoothToH1ComplDirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem exists_timeH1_chartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {φ : ℝ × EuStd → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ _root_.Set.univ ×ˢ
      (toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target))
    {T : ℝ} (hT : 0 ≤ T) (hφT : ∀ y, φ (T, y) = 0) :
    let μ := riemannianVolumeMeasure (I := I_hs) (M := M) q
    ∃ w : timeH1 (H1ComplDirichlet q) T,
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) T, H1ComplDirichletToLp q (w.toFun t) =ᵐ[μ]
        chartPullback I_hs α (fun y => φ (t, y))) ∧
      (∀ᵐ t ∂timeMeasure T, H1ComplDirichletToLp q (w.deriv t) =ᵐ[μ]
        chartPullback I_hs α (fun y => fderiv ℝ φ (t, y) (1, 0))) ∧
      (H1ComplDirichletToLp q w.initial =ᵐ[μ]
        chartPullback I_hs α (fun y => φ (0, y))) ∧ w.toFun T = 0 := by
  let e := toEuclidean (E := EuN)
  let K := Prod.snd '' tsupport φ
  have hK : IsCompact K := hφc.image continuous_snd
  have hKi : K ⊆ e '' interior (extChartAt I_hs α).target := by
    rintro y ⟨p, hp, rfl⟩
    exact (hφi hp).2
  have hKt : K ⊆ chartTargetEuclid (I := I_hs) (M := M) α :=
    hKi.trans (Set.image_mono interior_subset)
  have hs {ψ : ℝ × EuStd → ℝ} (hψ : tsupport ψ ⊆ tsupport φ) (t : ℝ) :
      tsupport (fun y => ψ (t, y)) ⊆ K := by
    have h := tsupport_comp_subset_preimage ψ (f := fun y : EuStd => (t, y))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun y hy => ⟨(t, y), hψ hy, rfl⟩
  let pull (ψ : ℝ × EuStd → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hψs : tsupport ψ ⊆ tsupport φ) (t : ℝ) : SmoothScalarDirichlet q :=
    ⟨chartPullback I_hs α (fun y => ψ (t, y)),
      chartPullback_contMDiff α (hψ.comp (contDiff_const.prodMk contDiff_id))
        (hK.of_isClosed_subset (isClosed_tsupport _) (hs hψs t)) ((hs hψs t).trans hKt),
      tsupport_chartPullback_subset_interior α
        (hK.of_isClosed_subset (isClosed_tsupport _) (hs hψs t)) ((hs hψs t).trans hKi)⟩
  let φ' : ℝ × EuStd → ℝ := fun p => fderiv ℝ φ p (1, 0)
  have hφ' : ContDiff ℝ ∞ φ' :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hφ's : tsupport φ' ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ (1, 0)
  let v := pull φ hφ Subset.rfl
  let v' := pull φ' hφ' hφ's
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (_root_.Set.univ ×ˢ _root_.Set.univ) :=
    (chartPullback_contMDiff_prod_of_hasCompactSupport α hφ hφc
      (hφi.trans (Set.prod_mono Subset.rfl (Set.image_mono interior_subset)))).contMDiffOn
  have hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (_root_.Set.univ ×ˢ _root_.Set.univ) :=
    (chartPullback_contMDiff_prod_of_hasCompactSupport α hφ'
      (hφc.fderiv_apply ℝ (1, 0))
      (hφ's.trans (hφi.trans (Set.prod_mono Subset.rfl (Set.image_mono interior_subset))))).contMDiffOn
  have hd : ∀ t ∈ (_root_.Set.univ : Set ℝ), ∀ x,
      HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t := by
    intro t _ x
    change HasDerivAt
      (fun s => chartPullback I_hs α (fun y => φ (s, y)) x)
      (chartPullback I_hs α (fun y => φ' (t, y)) x) t
    by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
    · simp_rw [chartPullback_apply_of_mem (I := I_hs) (M := M) α _ hx]
      exact (hφ.differentiable (by simp) (t, toEuclidean (extChartAt I_hs α x))).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t (toEuclidean (extChartAt I_hs α x))))
    · simp_rw [chartPullback_apply_of_notMem (I := I_hs) (M := M) α _ hx]
      exact hasDerivAt_const t 0
  let K_M := (extChartAt I_hs α).symm '' (e.symm '' K)
  have hEt : e.symm '' K ⊆ (extChartAt I_hs α).target := by
    rintro z ⟨y, hy, rfl⟩
    have hy' := hKt hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I_hs) (M := M)] at hy'
    exact hy'
  have hKM : IsCompact K_M :=
    (hK.image e.symm.continuous).image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I_hs) α).mono hEt)
  have hKMi : K_M ⊆ (I_hs).interior M := by
    rintro x ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hKi hy
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    have hsrc := (extChartAt I_hs α).map_target (interior_subset hz)
    rw [extChartAt_source] at hsrc
    apply ((I_hs).isInteriorPoint_iff_of_mem_atlas (M := M) (n := 1)
      (by simp) (chart_mem_atlas (EuclideanHalfSpace n) α) hsrc).2
    change extChartAt I_hs α ((extChartAt I_hs α).symm z) ∈
      interior (extChartAt I_hs α).target
    rwa [(extChartAt I_hs α).right_inv (interior_subset hz)]
  have hv'K : ∀ t ∈ (_root_.Set.univ : Set ℝ), tsupport (v' t).toFun ⊆ K_M := by
    intro t _
    exact (tsupport_chartPullback_subset α
      (hK.of_isClosed_subset (isClosed_tsupport _) (hs hφ's t)) ((hs hφ's t).trans hKt)).trans
        (Set.image_mono (Set.image_mono (hs hφ's t)))
  have hvT : v T = 0 := by
    apply InteriorSmoothScalar.toFun_injective
    funext x
    change chartPullback I_hs α (fun y => φ (T, y)) x = 0
    by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
    · rw [chartPullback_apply_of_mem (I := I_hs) (M := M) α _ hx]
      exact hφT _
    · exact chartPullback_apply_of_notMem (I := I_hs) (M := M) α _ hx
  obtain ⟨w, hw, hwd, hwi, hwT⟩ := exists_timeH1_smoothToH1ComplDirichlet q v v'
    isOpen_univ hv hv' hd hKM.isClosed hKMi hv'K hT (_root_.Set.subset_univ _) hvT
  refine ⟨w, ?_, ?_, ?_, hwT⟩
  · intro t ht
    rw [hw ht, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v t).memLp_two
  · filter_upwards [hwd] with t ht
    rw [ht, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v' t).memLp_two
  · rw [hwi, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v 0).memLp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback

theorem exists_timeH1_chartPullback_of_tsupport_subset
    (q : SmoothRiemannianMetric I_hs M) (α : M) {φ : ℝ × EuStd → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {T : ℝ} (hT : 0 ≤ T)
    (hφi : tsupport φ ⊆ _root_.Set.Iio T ×ˢ
      (toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)) :
    let μ := riemannianVolumeMeasure (I := I_hs) (M := M) q
    ∃ w : timeH1 (H1ComplDirichlet q) T,
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) T, H1ComplDirichletToLp q (w.toFun t) =ᵐ[μ]
        chartPullback I_hs α (fun y => φ (t, y))) ∧
      (∀ᵐ t ∂timeMeasure T, H1ComplDirichletToLp q (w.deriv t) =ᵐ[μ]
        chartPullback I_hs α (fun y => fderiv ℝ φ (t, y) (1, 0))) ∧
      (H1ComplDirichletToLp q w.initial =ᵐ[μ]
        chartPullback I_hs α (fun y => φ (0, y))) ∧ w.toFun T = 0 := by
  apply exists_timeH1_chartPullback q α hφ hφc
    (hφi.trans (Set.prod_mono (_root_.Set.subset_univ _) Subset.rfl)) hT
  intro y
  by_contra hne
  exact lt_irrefl T (hφi (subset_tsupport φ hne)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback_of_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_chartPullback_of_tsupport_subset

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private theorem exists_smooth_dirichlet_time_test
    (q : SmoothRiemannianMetric I_hs M) {φ : ℝ × M → ℝ}
    (hφ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ _root_.Set.univ ×ˢ (I_hs).interior M)
    {T : ℝ} (hT : 0 ≤ T) (hφT : ∀ x, φ (T, x) = 0) :
    ∃ (v v' : ℝ → SmoothScalarDirichlet q) (w : timeH1 (H1ComplDirichlet q) T),
      (∀ t x, (v t).toFun x = φ (t, x)) ∧
      (∀ t x, (v' t).toFun x = deriv (fun s => φ (s, x)) t) ∧
      _root_.Set.EqOn w.toFun (fun t => smoothToH1ComplDirichlet q (v t)) (_root_.Set.Icc (0 : ℝ) T) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => smoothToH1ComplDirichlet q (v' t)) ∧
      w.toFun T = 0 := by
  let K := Prod.snd '' tsupport φ
  have hK : IsCompact K := hφc.image continuous_snd
  have hKi : K ⊆ (I_hs).interior M := by
    rintro x ⟨p, hp, rfl⟩
    exact (hφi hp).2
  have hφK (t : ℝ) : tsupport (fun x => φ (t, x)) ⊆ K := by
    have h := tsupport_comp_subset_preimage φ (f := fun x : M => (t, x))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun x hx => ⟨(t, x), hx, rfl⟩
  let ψ : ℝ × M → ℝ := fun p => deriv (fun s => φ (s, p.2)) p.1
  have hψ : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ ψ := by
    intro p
    exact timeDeriv_smoothAt (hφ p) (by simp)
  have hψK (t : ℝ) : tsupport (fun x => ψ (t, x)) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hnot
    have hz : (fun s => φ (s, x)) = fun _ => 0 := by
      funext s
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact hnot ⟨(s, x), hs, rfl⟩
    have : ψ (t, x) = 0 := by
      dsimp only [ψ]
      rw [hz, deriv_const]
    exact hx this
  let v : ℝ → SmoothScalarDirichlet q := fun t =>
    ⟨fun x => φ (t, x), hφ.comp (contMDiff_const.prodMk contMDiff_id), (hφK t).trans hKi⟩
  let v' : ℝ → SmoothScalarDirichlet q := fun t =>
    ⟨fun x => ψ (t, x), hψ.comp (contMDiff_const.prodMk contMDiff_id), (hψK t).trans hKi⟩
  have hd (t : ℝ) (_ht : t ∈ (_root_.Set.univ : Set ℝ)) (x : M) :
      HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t := by
    exact ((hφ.comp (contMDiff_id.prodMk contMDiff_const)).contDiff.differentiable
      (by simp) t).hasDerivAt
  have hvT : v T = 0 := by
    ext x
    exact hφT x
  obtain ⟨w, hw, hwd, _, hwT⟩ := exists_timeH1_smoothToH1ComplDirichlet q v v'
    isOpen_univ hφ.contMDiffOn hψ.contMDiffOn hd hK.isClosed hKi
    (fun t _ => hψK t) hT (_root_.Set.subset_univ _) hvT
  exact ⟨v, v', w, fun _ _ => rfl, fun _ _ => rfl, hw, hwd, hwT⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_smooth_dirichlet_time_test
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_smooth_dirichlet_time_test target :: scope.openDecls } }

theorem integral_smooth_test_of_timeH1_mass_dual
    (q : SmoothRiemannianMetric I_hs M) {T : ℝ} (hT : 0 ≤ T)
    (U : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = _root_.Inner.inner ℝ (U t) (H1ComplDirichletToLp q z))
    (v : ℝ → SmoothScalarDirichlet q)
    (hv : ContMDiff (𝓘(ℝ).prod I_hs) 𝓘(ℝ) ∞ (fun p : ℝ × M => (v p.1).toFun p.2))
    (hvc : HasCompactSupport (fun p : ℝ × M => (v p.1).toFun p.2))
    (hvi : tsupport (fun p : ℝ × M => (v p.1).toFun p.2) ⊆ _root_.Set.univ ×ˢ (I_hs).interior M)
    (hvT : v T = 0) :
    (∫ t, ∫ x, U t x * deriv (fun s => (v s).toFun x) t
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) q ∂timeMeasure T) +
      (∫ t, w.deriv t (smoothToH1ComplDirichlet q (v t)) ∂timeMeasure T) =
        -w.toFun 0 (smoothToH1ComplDirichlet q (v 0)) := by
  obtain ⟨v₁, v₂, z, hv₁, hv₂, hz, hzd, hzT⟩ :=
    exists_smooth_dirichlet_time_test q hv hvc hvi hT (by intro x; simp [hvT])
  have hv₁eq (t) : v₁ t = v t := by ext x; exact hv₁ t x
  have h := timeH1.integral_dual_deriv_add_deriv_dual hT w z
  rw [hzT, map_zero, hz ⟨le_rfl, hT⟩] at h
  simp only [hv₁eq, zero_sub] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hzd, hmass] with t hzt hmt
    rw [hzt, hmt, H1ComplDirichletToLp_smoothToH1ComplDirichlet, L2.inner_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (v₂ t).memLp_two] with x hx
    change (smoothToLpDirichlet q (v₂ t) : M → ℝ) x = (v₂ t).toFun x at hx
    rw [hx, hv₂]
    simp only [Real.inner_apply, mul_comm]
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [hv₁eq] using congrArg (w.deriv t) (hz ht).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.integral_smooth_test_of_timeH1_mass_dual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.integral_smooth_test_of_timeH1_mass_dual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.integral_smooth_test_of_timeH1_mass_dual ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.integral_smooth_test_of_timeH1_mass_dual

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
