import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.UniformSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Topology
open scoped _root_.Topology _root_.Convolution _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

section BanachConvolution

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem convolution_tendstoUniformlyOn_compact_family_banach
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : E))
    (hφ : _root_.Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : K → E → F) (hf : Continuous (Function.uncurry f))
    {s : Set E} (hs : IsCompact s) :
    TendstoUniformlyOn
      (fun i (p : K × E) =>
        ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f p.1) p.2)
      (Function.uncurry f) l (_root_.Set.univ ×ˢ s) := by
  have hlocal : TendstoLocallyUniformly
      (fun i (p : K × E) =>
        ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f p.1) p.2)
      (Function.uncurry f) l := by
    apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
    intro p
    have hparam : _root_.Filter.Tendsto (fun q : (ι × (K × E)) × E => (q.1.2.1, q.2))
        ((l ×ˢ 𝓝 p) ×ˢ 𝓝 p.2) (𝓝 (p.1, p.2)) :=
      ((continuous_fst.tendsto p).comp (tendsto_snd.comp _root_.Filter.tendsto_fst)).prodMk_nhds
        _root_.Filter.tendsto_snd
    have hconv : _root_.Filter.Tendsto
        (fun q : ι × (K × E) =>
          ((φ q.1).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume]
            f q.2.1) q.2.2)
        (l ×ˢ 𝓝 p) (𝓝 (f p.1 p.2)) := by
      apply ContDiffBump.convolution_tendsto_right
        (φ := fun q : ι × (K × E) => φ q.1)
        (g := fun q : ι × (K × E) => f q.2.1)
        (k := fun q : ι × (K × E) => q.2.2)
      · exact hφ.comp _root_.Filter.tendsto_fst
      · exact Eventually.of_forall fun q =>
          (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact (hf.tendsto p).comp hparam
      · exact (continuous_snd.tendsto p).comp _root_.Filter.tendsto_snd
    exact (((hf.tendsto p).comp _root_.Filter.tendsto_snd).prodMk_nhds hconv).mono_right
      (nhds_le_uniformity _)
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_univ.prod hs)).mp hlocal.tendstoLocallyUniformlyOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_tendstoUniformlyOn_compact_family_banach
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_tendstoUniformlyOn_compact_family_banach target :: scope.openDecls } }

end BanachConvolution

section DerivativeConvolution

open _root_.Metric

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [CompleteSpace F] in
private theorem hasFDerivAt_convolution_of_compact_left
    (κ : E → ℝ) (hκ : HasCompactSupport κ) (hκint : _root_.MeasureTheory.LocallyIntegrable κ)
    (f : E → F) (hf : ContDiff ℝ 1 f) (x₀ : E) :
    HasFDerivAt (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f)
      ((κ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] F →L[ℝ] F).precompR E, _root_.MeasureTheory.MeasureSpace.volume] fderiv ℝ f) x₀) x₀ := by
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  obtain ⟨B, hB⟩ := (hκ.isCompact.image continuous_norm).bddAbove
  let R : ℝ := _root_.Max.max 1 (‖x₀‖ + B + 2)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, lt_add_one _⟩
  let g : E → F := fun x => χ x • f x
  have hg : ContDiff ℝ 1 g := χ.contDiff.smul hf
  have hgcomp : HasCompactSupport g := χ.hasCompactSupport.smul_right
  have hgf (y : E) (hy : y ∈ _root_.Metric.ball x₀ 1) (t : E) (ht : t ∈ tsupport κ) :
      g =ᶠ[𝓝 (y - t)] f := by
    have htB : ‖t‖ ≤ B := hB ⟨t, ht, rfl⟩
    have hy1 : ‖y - x₀‖ < 1 := by simpa only [_root_.Metric.mem_ball, dist_eq_norm] using hy
    have hsmall : ‖y - t‖ < R := calc
      _ ≤ ‖y‖ + ‖t‖ := norm_sub_le y t
      _ ≤ (‖y - x₀‖ + ‖x₀‖) + B :=
        add_le_add (norm_le_norm_sub_add y x₀) htB
      _ < ‖x₀‖ + B + 2 := by linarith
      _ ≤ R := le_max_right _ _
    have hball : y - t ∈ _root_.Metric.ball (0 : E) χ.rIn := by
      simpa only [_root_.Metric.mem_ball, dist_zero_right, χ] using hsmall
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hball] with z hz
    change χ z • f z = f z
    simp only [hz, Pi.one_apply, one_smul]
  have hconv : (κ ⋆[L, _root_.MeasureTheory.MeasureSpace.volume] g) =ᶠ[𝓝 x₀] (κ ⋆[L, _root_.MeasureTheory.MeasureSpace.volume] f) := by
    filter_upwards [_root_.Metric.ball_mem_nhds x₀ zero_lt_one] with y hy
    simp only [_root_.MeasureTheory.convolution_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with t
    by_cases ht : κ t = 0
    · simp [ht]
    · exact congrArg (L (κ t))
        ((hgf y hy t (subset_tsupport κ (Function.mem_support.mpr ht))).eq_of_nhds)
  have hdfconv : (κ ⋆[L.precompR E, _root_.MeasureTheory.MeasureSpace.volume] fderiv ℝ g) x₀ =
      (κ ⋆[L.precompR E, _root_.MeasureTheory.MeasureSpace.volume] fderiv ℝ f) x₀ := by
    simp only [_root_.MeasureTheory.convolution_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with t
    by_cases ht : κ t = 0
    · simp [ht]
    · exact congrArg ((L.precompR E) (κ t))
        ((hgf x₀ (_root_.Metric.mem_ball_self zero_lt_one) t
          (subset_tsupport κ (Function.mem_support.mpr ht))).fderiv_eq)
  have hd := hgcomp.hasFDerivAt_convolution_right L hκint hg x₀
  rw [hdfconv] at hd
  exact hd.congr_of_eventuallyEq hconv.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.hasFDerivAt_convolution_of_compact_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.hasFDerivAt_convolution_of_compact_left target :: scope.openDecls } }

omit [CompleteSpace F] in
private theorem fderiv_convolution_of_compact_left
    (κ : E → ℝ) (hκ : HasCompactSupport κ) (hκint : _root_.MeasureTheory.LocallyIntegrable κ)
    (f : E → F) (hf : ContDiff ℝ 1 f) (x : E) :
    fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f) x =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] fderiv ℝ f) x := by
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR E =
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F)) := by
    ext a D
    rfl
  have h := (hasFDerivAt_convolution_of_compact_left κ hκ hκint f hf x).fderiv
  rw [hL] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.fderiv_convolution_of_compact_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.fderiv_convolution_of_compact_left target :: scope.openDecls } }

end DerivativeConvolution

variable {d m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin m)

private theorem lipschitz_lineDeriv_weak
    {g : E → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => lineDeriv ℝ g x (EuclideanSpace.single i 1)) g univ := by
  intro φ hφ hsupp _
  simp only [_root_.MeasureTheory.setIntegral_univ]
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hφ (by simp)
  have h := hg.integral_lineDeriv_mul_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) hD hsupp
    (EuclideanSpace.single i 1)
  simp_rw [(hφ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    map_neg, neg_mul, _root_.MeasureTheory.integral_neg] at h
  have hcomm : (∫ x : E, (fderiv ℝ φ x) (EuclideanSpace.single i 1) * g x) =
      ∫ x : E, g x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x using mul_comm _ _
  rw [hcomm] at h
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitz_lineDeriv_weak
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitz_lineDeriv_weak target :: scope.openDecls } }

theorem lipschitzOn_hasWeakPartialDeriv
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} {L : ℝ≥0}
    (hf : LipschitzOnWith L f Ω) (i : Fin d) (j : Fin m) :
    _root_.MeasureTheory.LocallyIntegrableOn
      (fun x => (fderiv ℝ f x (EuclideanSpace.single i 1)) j) Ω ∧
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ f x (EuclideanSpace.single i 1)) j)
      (fun x => f x j) Ω := by
  let P : F →L[ℝ] ℝ := EuclideanSpace.proj j
  have hscalar := P.lipschitz.comp_lipschitzOnWith hf
  obtain ⟨g, hg, heq⟩ := hscalar.extend_real
  have heq' : _root_.Set.EqOn (fun x => f x j) g Ω := heq
  have hderiv : (fun x => lineDeriv ℝ g x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      (fun x => (fderiv ℝ f x (EuclideanSpace.single i 1)) j) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (hg.ae_differentiableAt (μ := _root_.MeasureTheory.MeasureSpace.volume)),
      hf.ae_differentiableWithinAt hΩ.measurableSet,
      _root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with x hxg hxf hx
    have hfg : (fun y => f y j) =ᶠ[𝓝 x] g := by
      filter_upwards [hΩ.mem_nhds hx] with y hy using heq' hy
    have hdf := P.hasFDerivAt.comp x
      (hxf.differentiableAt (hΩ.mem_nhds hx)).hasFDerivAt
    calc
      lineDeriv ℝ g x (EuclideanSpace.single i 1) =
          fderiv ℝ g x (EuclideanSpace.single i 1) := hxg.lineDeriv_eq_fderiv
      _ = fderiv ℝ (fun y => f y j) x (EuclideanSpace.single i 1) :=
        congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1))
          hfg.fderiv_eq.symm
      _ = (fderiv ℝ f x (EuclideanSpace.single i 1)) j :=
        congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hdf.fderiv
  refine ⟨((hg.locallyIntegrable_lineDeriv (μ := _root_.MeasureTheory.MeasureSpace.volume)
    (EuclideanSpace.single i 1)).locallyIntegrableOn Ω).congr hderiv, ?_⟩
  have hweak := DeGiorgi.HasWeakPartialDeriv.restrict hΩ (_root_.Set.subset_univ Ω)
    (lipschitz_lineDeriv_weak hg i)
  intro φ hφ hsupp hsub
  have h := hweak φ hφ hsupp hsub
  calc
    (∫ x in Ω, f x j * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
        ∫ x in Ω, g x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with x hx
      exact congrArg (fun a : ℝ => a * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (heq' hx)
    _ = -∫ x in Ω, lineDeriv ℝ g x (EuclideanSpace.single i 1) * φ x := h
    _ = -∫ x in Ω, (fderiv ℝ f x (EuclideanSpace.single i 1)) j * φ x := by
      congr 1
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hderiv] with x hx
      rw [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_hasWeakPartialDeriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_hasWeakPartialDeriv

theorem lipschitzOn_ae_fderiv_smooth_comp
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} {L : ℝ≥0}
    (hf : LipschitzOnWith L f Ω) (G : F → EuclideanSpace ℝ (Fin n))
    (hG : ContDiff ℝ 1 G) :
    ∀ᵐ x ∂volume.restrict Ω,
      fderiv ℝ (G ∘ f) x = (fderiv ℝ G (f x)).comp (fderiv ℝ f x) := by
  filter_upwards [hf.ae_differentiableWithinAt hΩ.measurableSet,
    _root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with x hx hxs
  exact fderiv_comp x (hG.differentiable_one (f x))
    (hx.differentiableAt (hΩ.mem_nhds hxs))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_ae_fderiv_smooth_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_ae_fderiv_smooth_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_ae_fderiv_smooth_comp ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_ae_fderiv_smooth_comp

theorem convolution_weakPartial
    {u g : E → ℝ} {i : Fin d}
    (hweak : DeGiorgi.HasWeakPartialDeriv i g u _root_.Set.univ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (x : E) :
    ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] u) x =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] g) x :=
  DifferentialGeometry.Analysis.Sobolev.convolution_fderiv_eq_convolution_weakPartial_univ
    hweak hφ hsupp x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_weakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_weakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_weakPartial ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_weakPartial

theorem convolution_tendstoUniformlyOn_compact_family
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : E))
    (hφ : _root_.Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : K → E → F) (hf : Continuous (Function.uncurry f))
    {s : Set E} (hs : IsCompact s) :
    TendstoUniformlyOn
      (fun i (p : K × E) =>
        ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f p.1) p.2)
      (Function.uncurry f) l (_root_.Set.univ ×ˢ s) := by
  exact convolution_tendstoUniformlyOn_compact_family_banach φ hφ f hf hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_tendstoUniformlyOn_compact_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_tendstoUniformlyOn_compact_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_tendstoUniformlyOn_compact_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_tendstoUniformlyOn_compact_family

theorem convolution_fderiv_tendstoUniformlyOn_compact_family
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : E))
    (hφ : _root_.Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : K → E → F) (hf : Continuous (Function.uncurry f))
    (hf1 : ∀ k, ContDiff ℝ 1 (f k))
    (hdf : Continuous (fun p : K × E => fderiv ℝ (f p.1) p.2))
    {s : Set E} (hs : IsCompact s) :
    TendstoUniformlyOn
      (fun i (p : K × E) => fderiv ℝ
        ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f p.1) p.2)
      (fun p : K × E => fderiv ℝ (f p.1) p.2) l (_root_.Set.univ ×ˢ s) := by
  let _ := hf
  have hmaps :
      (fun i (p : K × E) => fderiv ℝ
        ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f p.1) p.2) =
      (fun i (p : K × E) =>
        ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume]
          fderiv ℝ (f p.1)) p.2) := by
    funext i p
    exact fderiv_convolution_of_compact_left ((φ i).normed _root_.MeasureTheory.MeasureSpace.volume)
      (φ i).hasCompactSupport_normed (φ i).integrable_normed.locallyIntegrable
      (f p.1) (hf1 p.1) p.2
  rw [hmaps]
  exact convolution_tendstoUniformlyOn_compact_family_banach φ hφ
    (fun k x => fderiv ℝ (f k) x) hdf hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_fderiv_tendstoUniformlyOn_compact_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_fderiv_tendstoUniformlyOn_compact_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_fderiv_tendstoUniformlyOn_compact_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.convolution_fderiv_tendstoUniformlyOn_compact_family

open _root_.Metric in
private theorem tangentConeAt_eq_univ_of_differentiableAt_infDist
    {s : Set E} {x : E} (hx : x ∈ s)
    (hdiff : DifferentiableAt ℝ (fun y => _root_.Metric.infDist y s) x) :
    tangentConeAt ℝ s x = univ := by
  have hmin : IsLocalMin (fun y => _root_.Metric.infDist y s) x := by
    change ∀ᶠ y in 𝓝 x, _root_.Metric.infDist x s ≤ _root_.Metric.infDist y s
    exact Eventually.of_forall fun y => by
      rw [_root_.Metric.infDist_zero_of_mem hx]
      exact _root_.Metric.infDist_nonneg
  have hd : HasFDerivAt (fun y => _root_.Metric.infDist y s) (0 : E →L[ℝ] ℝ) x := by
    simpa only [hmin.fderiv_eq_zero] using hdiff.hasFDerivAt
  apply _root_.Set.eq_univ_of_forall
  intro v
  have hsl : _root_.Filter.Tendsto (fun t : ℝ => t⁻¹ * _root_.Metric.infDist (x + t • v) s)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_apply, _root_.Metric.infDist_zero_of_mem hx,
      sub_zero, smul_eq_mul] using (hd.hasLineDerivAt v).tendsto_slope_zero_right
  choose p hps hpd using fun t : ℝ =>
    _root_.Metric.exists_mem_closure_infDist_eq_dist (show s.Nonempty from ⟨x, hx⟩) (x + t • v)
  let e : ℝ → E := fun t => t⁻¹ • (p t - (x + t • v))
  have he : _root_.Filter.Tendsto e (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hsl
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    apply le_of_eq
    dsimp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
      ← dist_eq_norm, dist_comm, ← hpd t]
  have halg : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ • (p t - x) = e t + v := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hsplit : p t - x = (p t - (x + t • v)) + t • v := by abel
    rw [hsplit, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hc : _root_.Filter.Tendsto (fun t : ℝ => t⁻¹ • (p t - x)) (𝓝[>] 0) (𝓝 v) := by
    have h := he.add (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℝ => v) (𝓝[>] 0) (𝓝 v))
    have halg' : (fun t : ℝ => t⁻¹ • (p t - x)) =ᶠ[𝓝[>] 0]
        (fun t => e t + v) := halg
    simpa only [zero_add] using h.congr' halg'.symm
  have hz : _root_.Filter.Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp0 : _root_.Filter.Tendsto (fun t : ℝ => p t - x) (𝓝[>] 0) (𝓝 0) := by
    have h := hz.smul hc
    simp only [zero_smul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hcone : v ∈ tangentConeAt ℝ (closure s) x := by
    apply mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => t⁻¹)
      (fun t => p t - x) hp0 _ hc
    exact Eventually.of_forall fun t => by
      convert hps t using 1; abel
  simpa only [tangentConeAt_closure] using hcone

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.tangentConeAt_eq_univ_of_differentiableAt_infDist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.tangentConeAt_eq_univ_of_differentiableAt_infDist target :: scope.openDecls } }

open _root_.Metric in
theorem ae_uniqueDiffWithinAt_of_measurableSet {s : Set E} (hs : MeasurableSet s) :
    ∀ᵐ x ∂volume.restrict s, UniqueDiffWithinAt ℝ s x := by
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae
    ((_root_.Metric.lipschitz_infDist_pt s).ae_differentiableAt (μ := _root_.MeasureTheory.MeasureSpace.volume)),
    _root_.MeasureTheory.ae_restrict_mem hs] with x hdiff hx
  rw [uniqueDiffWithinAt_iff,
    tangentConeAt_eq_univ_of_differentiableAt_infDist hx hdiff]
  exact ⟨by simp, subset_closure hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.ae_uniqueDiffWithinAt_of_measurableSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.ae_uniqueDiffWithinAt_of_measurableSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.ae_uniqueDiffWithinAt_of_measurableSet ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.ae_uniqueDiffWithinAt_of_measurableSet

private theorem lipschitzOn_image_volume_zero
    {s : Set E} {f : E → E} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) (hs : _root_.MeasureTheory.MeasureSpace.volume s = 0) : _root_.MeasureTheory.MeasureSpace.volume (f '' s) = 0 := by
  let μ : _root_.MeasureTheory.Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hμs : μ s = 0 :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ _root_.MeasureTheory.MeasureSpace.volume hs
  have hμimage : μ (f '' s) = 0 := by
    apply le_antisymm _ (by positivity)
    calc
      μ (f '' s) ≤ (L : ENNReal) ^ (Module.finrank ℝ E : ℝ) * μ s :=
        hf.hausdorffMeasure_image_le (by positivity)
      _ = 0 := by rw [hμs, _root_.MulZeroClass.mul_zero]
  exact Measure.absolutelyContinuous_isAddHaarMeasure _root_.MeasureTheory.MeasureSpace.volume μ hμimage

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_image_volume_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_image_volume_zero target :: scope.openDecls } }

private theorem lipschitzOn_measurable_differentiability_subset
    {s : Set E} (hs : MeasurableSet s) {f : E → E} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) :
    ∃ t : Set E, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] s ∧
      f '' t =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] f '' s ∧
      ∀ x ∈ t, HasFDerivWithinAt f (fderivWithin ℝ f s x) t x := by
  have hae := (_root_.MeasureTheory.ae_restrict_iff' hs).mp (hf.ae_differentiableWithinAt (μ := _root_.MeasureTheory.MeasureSpace.volume) hs)
  obtain ⟨n, hbn, hn, hn0⟩ := _root_.MeasureTheory.exists_measurable_superset_of_null (ae_iff.mp hae)
  let t := s \ n
  have hts : t ⊆ s := _root_.Set.sdiff_subset
  have htd : ∀ x ∈ t, DifferentiableWithinAt ℝ f s x := by
    intro x hx
    by_contra h
    exact hx.2 (hbn (Classical.not_imp.mpr ⟨hx.1, h⟩))
  have himg0 : _root_.MeasureTheory.MeasureSpace.volume (f '' (s ∩ n)) = 0 :=
    lipschitzOn_image_volume_zero (hf.mono _root_.Set.inter_subset_left)
      (_root_.MeasureTheory.measure_mono_null _root_.Set.inter_subset_right hn0)
  have himg : f '' t =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] f '' s := by
    apply ae_eq_set.mpr
    constructor
    · rw [sdiff_eq_empty.mpr (_root_.Set.image_mono hts), _root_.MeasureTheory.measure_empty]
    · apply _root_.MeasureTheory.measure_mono_null _ himg0
      rintro y ⟨⟨x, hx, rfl⟩, hyt⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      by_contra hxn
      exact hyt ⟨x, ⟨hx, hxn⟩, rfl⟩
  exact ⟨t, hts, hs.diff hn, _root_.MeasureTheory.sdiff_null_ae_eq_self hn0, himg,
    fun x hx => (htd x hx).hasFDerivWithinAt.mono hts⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_measurable_differentiability_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.lipschitzOn_measurable_differentiability_subset target :: scope.openDecls } }

theorem biLipschitz_integrableOn_image_iff
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {s : Set E} (hs : MeasurableSet s) {f : E → E} {L A : ℝ≥0}
    (hf : LipschitzOnWith L f s)
    (hinv : AntilipschitzWith A (fun x : s => f x)) (h : E → B) :
    _root_.MeasureTheory.IntegrableOn h (f '' s) ↔
      IntegrableOn (fun x => |(fderivWithin ℝ f s x).det| • h (f x)) s := by
  obtain ⟨t, hts, ht, hteq, himg, hd⟩ :=
    lipschitzOn_measurable_differentiability_subset hs hf
  have hinj : _root_.Set.InjOn f t := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (hinv.injective (show f (⟨x, hts hx⟩ : s) = f (⟨y, hts hy⟩ : s) from hxy))
  have hnative := _root_.MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    _root_.MeasureTheory.MeasureSpace.volume ht hd hinj h
  simpa only [_root_.MeasureTheory.IntegrableOn, Measure.restrict_congr_set hteq,
    Measure.restrict_congr_set himg] using hnative

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integrableOn_image_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integrableOn_image_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integrableOn_image_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integrableOn_image_iff

theorem biLipschitz_integral_image
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {s : Set E} (hs : MeasurableSet s) {f : E → E} {L A : ℝ≥0}
    (hf : LipschitzOnWith L f s)
    (hinv : AntilipschitzWith A (fun x : s => f x)) (h : E → B)
    (hh : _root_.MeasureTheory.IntegrableOn h (f '' s)) :
    ∫ x in f '' s, h x =
      ∫ x in s, |(fderivWithin ℝ f s x).det| • h (f x) := by
  let _ := hh
  obtain ⟨t, hts, ht, hteq, himg, hd⟩ :=
    lipschitzOn_measurable_differentiability_subset hs hf
  have hinj : _root_.Set.InjOn f t := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (hinv.injective (show f (⟨x, hts hx⟩ : s) = f (⟨y, hts hy⟩ : s) from hxy))
  calc
    (∫ x in f '' s, h x) = ∫ x in f '' t, h x := _root_.MeasureTheory.setIntegral_congr_set himg.symm
    _ = ∫ x in t, |(fderivWithin ℝ f s x).det| • h (f x) :=
      _root_.MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul _root_.MeasureTheory.MeasureSpace.volume ht hd hinj h
    _ = ∫ x in s, |(fderivWithin ℝ f s x).det| • h (f x) := _root_.MeasureTheory.setIntegral_congr_set hteq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integral_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integral_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integral_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.biLipschitz_integral_image

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
