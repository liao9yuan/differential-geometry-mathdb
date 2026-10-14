import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartPullback
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartPullbackLp
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSobolev

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Integral.Measure

private theorem wkpNorm_sub_comm {d k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemWkp k p f Ω) (hg : MemWkp k p g Ω) :
    iteratedWeakSobolevNorm k p (fun x => f x - g x) Ω =
      iteratedWeakSobolevNorm k p (fun x => g x - f x) Ω := by
  simpa only [neg_one_mul, neg_sub, enorm_neg, enorm_one, one_mul] using
    wkpNorm_const_smul hp hΩ (hg.sub hp hΩ hf) (-1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.wkpNorm_sub_comm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.wkpNorm_sub_comm target :: scope.openDecls } }

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

omit [CompactSpace M] in
private theorem smoothScalarDirichletChartPullback_sub
    (q : SmoothRiemannianMetric I_hs M) (α : M) {f g : EuStd → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    smoothScalarDirichletChartPullback q α (hf.sub hg) (hfc.sub hgc)
      ((tsupport_sub f g).trans (_root_.Set.union_subset hfs hgs)) =
      smoothScalarDirichletChartPullback q α hf hfc hfs -
        smoothScalarDirichletChartPullback q α hg hgc hgs := by
  apply InteriorSmoothScalar.ext
  funext x
  change chartPullback I_hs α (fun z => f z - g z) x =
    chartPullback I_hs α f x - chartPullback I_hs α g x
  simp only [chartPullback]
  split_ifs <;> simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothScalarDirichletChartPullback_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothScalarDirichletChartPullback_sub target :: scope.openDecls } }

private theorem cauchySeq_smoothScalarDirichletChartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω)
    (φ : ℕ → EuStd → ℝ) (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j))
    (hφc : ∀ j, HasCompactSupport (φ j)) (hφs : ∀ j, tsupport (φ j) ⊆ Ω)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 ≤ ε j) (hεt : _root_.Filter.Tendsto ε _root_.Filter.atTop (𝓝 0))
    (herr : ∀ j, iteratedWeakSobolevNorm 1 2 (fun x => f x - φ j x) Ω ≤ ENNReal.ofReal (ε j)) :
    CauchySeq (fun j => smoothToH1ComplDirichlet q
      (smoothScalarDirichletChartPullback q α (hφ j) (hφc j)
        ((hφs j).trans (subset_closure.trans hΩs)))) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_smoothScalarDirichletChartPullback_le_wkpNorm q α hΩc hΩs
  let v := fun j => smoothScalarDirichletChartPullback q α (hφ j) (hφc j)
    ((hφs j).trans (subset_closure.trans hΩs))
  have hφW : ∀ j, MemWkp 1 2 (φ j) Ω := fun j =>
    MemWkp_of_smooth_compactSupport hΩ (hφ j) (hφc j) (hφs j) (by norm_num) 1
  have hdist (j k : ℕ) : _root_.Dist.dist (smoothToH1ComplDirichlet q (v j))
      (smoothToH1ComplDirichlet q (v k)) ≤ C * (ε j + ε k) := by
    have hs : tsupport (fun x => φ j x - φ k x) ⊆ Ω :=
      (tsupport_sub _ _).trans (_root_.Set.union_subset (hφs j) (hφs k))
    have hb := hbound hΩ _ ((hφ j).sub (hφ k)) ((hφc j).sub (hφc k))
      (hs.trans subset_closure) hs
    have hdiff : iteratedWeakSobolevNorm 1 2 (fun x => φ j x - φ k x) Ω ≤
        ENNReal.ofReal (ε j + ε k) := by
      have ht := wkpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
        ((hφW j).sub (by norm_num) hΩ hf) (hf.sub (by norm_num) hΩ (hφW k))
      simp only [sub_add_sub_cancel] at ht
      rw [wkpNorm_sub_comm (by norm_num) hΩ (hφW j) hf] at ht
      exact ht.trans ((add_le_add (herr j) (herr k)).trans_eq (ENNReal.ofReal_add (hε j) (hε k)).symm)
    have hr := ENNReal.toReal_mono (by simp : ENNReal.ofReal (ε j + ε k) ≠ (⊤ : ℝ≥0∞)) hdiff
    rw [ENNReal.toReal_ofReal (add_nonneg (hε j) (hε k))] at hr
    have hb' : ‖v j - v k‖ ≤ C * (ε j + ε k) := by
      rw [← smoothScalarDirichletChartPullback_sub]
      exact hb.trans (mul_le_mul_of_nonneg_left hr hC)
    rw [dist_eq_norm, ← map_sub]
    change ‖((v j - v k : SmoothScalarDirichlet q) :
      UniformSpace.Completion (SmoothScalarDirichlet q))‖ ≤ _
    rwa [UniformSpace.Completion.norm_coe]
  apply Metric.cauchySeq_iff.mpr
  intro δ hδ
  have ht : _root_.Filter.Tendsto (fun j => C * (ε j + ε j)) _root_.Filter.atTop (𝓝 0) := by
    simpa only [zero_add, _root_.MulZeroClass.mul_zero] using (hεt.add hεt).const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro j hj k hk
  have hj' := hN j hj
  have hk' := hN k hk
  exact (hdist j k).trans_lt (by nlinarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.cauchySeq_smoothScalarDirichletChartPullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.cauchySeq_smoothScalarDirichletChartPullback target :: scope.openDecls } }

private theorem exists_h1ComplDirichlet_chartPullback_of_measurable
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuStd → ℝ), Measurable f → MemWkp 1 2 f Ω →
      tsupport f ⊆ Ω → ∃ w : H1ComplDirichlet q,
        (H1ComplDirichletToLp q w : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
          chartPullback I_hs α f ∧
        ‖w‖ ≤ C * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_norm_smoothScalarDirichletChartPullback_le_wkpNorm q α hΩc hΩs
  obtain ⟨D, hD, hLp⟩ := exists_eLpNorm_chartPullback_le q α hΩc
    (hΩs.trans (_root_.Set.image_mono interior_subset)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro f hfm hf hfs
  have hfc : HasCompactSupport f := hΩc.of_isClosed_subset (isClosed_tsupport _) (hfs.trans subset_closure)
  let ε := fun j : ℕ => (1 : ℝ) / (j + 1)
  have hε : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have hεt : _root_.Filter.Tendsto ε _root_.Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose φ hφ hφc hφs herr using fun j =>
    hf.exists_smooth_compactSupport_approx hΩ 1 2 (by norm_num) (by norm_num) hfc hfs (ε j) (hε j)
  let v := fun j => smoothScalarDirichletChartPullback q α (hφ j) (hφc j)
    ((hφs j).trans (subset_closure.trans hΩs))
  have hφW : ∀ j, MemWkp 1 2 (φ j) Ω := fun j =>
    MemWkp_of_smooth_compactSupport hΩ (hφ j) (hφc j) (hφs j) (by norm_num) 1
  have hcauchy := cauchySeq_smoothScalarDirichletChartPullback q α hΩ hΩc hΩs hf
    φ hφ hφc hφs (fun j => (hε j).le) hεt herr
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hfLp : _root_.MeasureTheory.MemLp f 2 volume := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [← _root_.MeasureTheory.eLpNorm_restrict_eq_of_support_subset ((subset_tsupport f).trans hfs)]
    exact hf.memLp.2
  have hpb : _root_.MeasureTheory.MemLp (chartPullback I_hs α f) 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q) := by
    refine ⟨(measurable_chartPullback α hfm).aestronglyMeasurable, ?_⟩
    exact (hLp f hfm (hfs.trans subset_closure)).trans_lt
      (ENNReal.mul_lt_top (by simp) hfLp.2)
  let F := hpb.toLp (chartPullback I_hs α f)
  have hLpt : _root_.Filter.Tendsto (fun j => smoothToLpDirichlet q (v j)) _root_.Filter.atTop (𝓝 F) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    have ht : _root_.Filter.Tendsto (fun j => D * ε j) _root_.Filter.atTop (𝓝 0) := by
      simpa only [_root_.MulZeroClass.mul_zero] using hεt.const_mul D
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
    refine ⟨N, ?_⟩
    intro j hj
    have hdiffs : tsupport (fun x => f x - φ j x) ⊆ Ω :=
      (tsupport_sub _ _).trans (_root_.Set.union_subset hfs (hφs j))
    have hdiff := hLp (fun x => f x - φ j x) (hfm.sub (hφ j).continuous.measurable)
      (hdiffs.trans subset_closure)
    have hE : _root_.MeasureTheory.eLpNorm (fun x => f x - φ j x) 2 _root_.MeasureTheory.MeasureSpace.volume ≤ ENNReal.ofReal (ε j) := by
      rw [← _root_.MeasureTheory.eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans hdiffs)]
      exact (eLpNorm_le_wkpNorm 1 2 Ω _).trans (herr j)
    have hEt := hdiff.trans (mul_le_mul' le_rfl hE)
    have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by simp)) hEt
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le, ENNReal.toReal_ofReal (hε j).le] at hR
    have heq : chartPullback I_hs α (fun x => f x - φ j x) =
        chartPullback I_hs α f - (v j).toFun := by
      funext x
      change chartPullback I_hs α (fun z => f z - φ j z) x =
        chartPullback I_hs α f x - chartPullback I_hs α (φ j) x
      simp only [chartPullback]
      split_ifs <;> simp
    have hdist : _root_.Dist.dist (smoothToLpDirichlet q (v j)) F ≤ D * ε j := by
      rw [dist_comm, dist_eq_norm]
      change ‖hpb.toLp (chartPullback I_hs α f) - (v j).memLp_two.toLp (v j).toFun‖ ≤ _
      rw [← MemLp.toLp_sub, Lp.norm_toLp, ← heq]
      exact hR
    exact hdist.trans_lt (hN j hj)
  have hweq : H1ComplDirichletToLp q w = F := by
    apply tendsto_nhds_unique _ hLpt
    simpa only [Function.comp_def, H1ComplDirichletToLp_smoothToH1ComplDirichlet] using
      (H1ComplDirichletToLp q).continuous.tendsto w |>.comp hw
  refine ⟨w, ?_, ?_⟩
  · rw [hweq]
    exact hpb.coeFn_toLp
  · have hn (j : ℕ) : ‖smoothToH1ComplDirichlet q (v j)‖ ≤
        C * ((iteratedWeakSobolevNorm 1 2 f Ω).toReal + ε j) := by
      have ht := wkpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hf
        ((hφW j).sub (by norm_num) hΩ hf)
      simp only [add_sub_cancel] at ht
      rw [wkpNorm_sub_comm (by norm_num) hΩ (hφW j) hf] at ht
      have he := ht.trans (add_le_add le_rfl (herr j))
      have hr := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(wkpNorm_lt_top_of_memWkp hf).ne, by simp⟩) he
      rw [ENNReal.toReal_add (wkpNorm_lt_top_of_memWkp hf).ne (by simp),
        ENNReal.toReal_ofReal (hε j).le] at hr
      have hb := hbound hΩ (φ j) (hφ j) (hφc j) ((hφs j).trans subset_closure) (hφs j)
      change ‖((v j : SmoothScalarDirichlet q) : UniformSpace.Completion (SmoothScalarDirichlet q))‖ ≤ _
      rw [UniformSpace.Completion.norm_coe]
      exact hb.trans (mul_le_mul_of_nonneg_left hr hC)
    have hright : _root_.Filter.Tendsto (fun j => C * ((iteratedWeakSobolevNorm 1 2 f Ω).toReal + ε j))
        atTop (𝓝 (C * (iteratedWeakSobolevNorm 1 2 f Ω).toReal)) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hεt).const_mul C
    exact le_of_tendsto_of_tendsto' (continuous_norm.tendsto w |>.comp hw) hright hn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_chartPullback_of_measurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_chartPullback_of_measurable target :: scope.openDecls } }

theorem exists_h1ComplDirichlet_chartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuStd → ℝ), MemWkp 1 2 f Ω →
      tsupport f ⊆ Ω → ∃ w : H1ComplDirichlet q,
        (H1ComplDirichletToLp q w : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
          chartPullback I_hs α f ∧
        ‖w‖ ≤ C * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_h1ComplDirichlet_chartPullback_of_measurable q α hΩ hΩc hΩs
  refine ⟨C, hC, ?_⟩
  intro f hf hfs
  let g := (tsupport f).indicator (hf.memLp.1.mk f)
  have hgm : Measurable g := hf.memLp.1.measurable_mk.indicator (isClosed_tsupport f).measurableSet
  have hgsub : tsupport g ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra hxs
    exact hx (_root_.Set.indicator_of_notMem hxs _)
  have hgs := hgsub.trans hfs
  have hfgΩ : f =ᵐ[volume.restrict Ω] g := by
    filter_upwards [hf.memLp.1.ae_eq_mk] with x hx
    by_cases hxs : x ∈ tsupport f
    · simpa only [g, _root_.Set.indicator_of_mem hxs] using hx
    · change f x = (tsupport f).indicator (hf.memLp.1.mk f) x
      rw [_root_.Set.indicator_of_notMem hxs]
      exact image_eq_zero_of_notMem_tsupport hxs
  have hfg : f =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] g := by
    filter_upwards [(_root_.MeasureTheory.ae_restrict_iff' hΩ.measurableSet).mp hfgΩ] with x hx
    by_cases hxΩ : x ∈ Ω
    · exact hx hxΩ
    · rw [image_eq_zero_of_notMem_tsupport (fun hs => hxΩ (hfs hs)),
        image_eq_zero_of_notMem_tsupport (fun hs => hxΩ (hgs hs))]
  have hg : MemWkp 1 2 g Ω := (MemWkp_congr_ae (by norm_num) hΩ hfgΩ).mp hf
  obtain ⟨w, hw, hn⟩ := hbound g hgm hg hgs
  refine ⟨w, hw.trans (chartPullback_ae_eq_of_ae_eq q α hfg).symm, ?_⟩
  rwa [wkpNorm_congr_ae (by norm_num) hΩ hfgΩ] at ⊢

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_chartPullback ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_chartPullback

def h1ComplDirichletChartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) : H1ComplDirichlet q :=
  ((exists_h1ComplDirichlet_chartPullback q α hΩ hΩc hΩs).choose_spec.2 f hf hfs).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback

theorem h1ComplDirichletChartPullback_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    (H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q] chartPullback I_hs α f :=
  ((exists_h1ComplDirichlet_chartPullback q α hΩ hΩc hΩs).choose_spec.2 f hf hfs).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_coeFn

theorem exists_norm_h1ComplDirichletChartPullback_le_wkpNorm
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuStd → ℝ) (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω),
      ‖h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs‖ ≤
        C * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  let h := exists_h1ComplDirichlet_chartPullback q α hΩ hΩc hΩs
  exact ⟨h.choose, h.choose_spec.1, fun f hf hfs => (h.choose_spec.2 f hf hfs).choose_spec.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_norm_h1ComplDirichletChartPullback_le_wkpNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_norm_h1ComplDirichletChartPullback_le_wkpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_norm_h1ComplDirichletChartPullback_le_wkpNorm ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_norm_h1ComplDirichletChartPullback_le_wkpNorm

theorem eq_h1ComplDirichletChartPullback_of_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω)
    {w : H1ComplDirichlet q}
    (hw : (H1ComplDirichletToLp q w : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q] chartPullback I_hs α f) :
    w = h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs := by
  apply H1ComplDirichletToLp_injective q
  apply Lp.ext
  exact hw.trans (h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.eq_h1ComplDirichletChartPullback_of_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.eq_h1ComplDirichletChartPullback_of_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.eq_h1ComplDirichletChartPullback_of_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.eq_h1ComplDirichletChartPullback_of_coeFn

theorem h1ComplDirichletChartPullback_add
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f g : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω)
    (hg : MemWkp 1 2 g Ω) (hgs : tsupport g ⊆ Ω) :
    h1ComplDirichletChartPullback q α hΩ hΩc hΩs (hf.add (by norm_num) hΩ hg)
      ((tsupport_add f g).trans (_root_.Set.union_subset hfs hgs)) =
      h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs +
        h1ComplDirichletChartPullback q α hΩ hΩc hΩs hg hgs := by
  symm
  apply eq_h1ComplDirichletChartPullback_of_coeFn
  rw [map_add]
  filter_upwards [Lp.coeFn_add
    (H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs))
    (H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hg hgs)),
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs,
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hg hgs] with x hx hfx hgx
  rw [hx, Pi.add_apply, hfx, hgx, chartPullback_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_add ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_add

theorem h1ComplDirichletChartPullback_sub
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f g : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω)
    (hg : MemWkp 1 2 g Ω) (hgs : tsupport g ⊆ Ω) :
    h1ComplDirichletChartPullback q α hΩ hΩc hΩs (hf.sub (by norm_num) hΩ hg)
      ((tsupport_sub f g).trans (_root_.Set.union_subset hfs hgs)) =
      h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs -
        h1ComplDirichletChartPullback q α hΩ hΩc hΩs hg hgs := by
  symm
  apply eq_h1ComplDirichletChartPullback_of_coeFn
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub
    (H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs))
    (H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hg hgs)),
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs,
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hg hgs] with x hx hfx hgx
  rw [hx, Pi.sub_apply, hfx, hgx]
  simp only [chartPullback]
  split_ifs <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_sub ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_sub

theorem h1ComplDirichletChartPullback_smul
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (c : ℝ) {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    h1ComplDirichletChartPullback q α hΩ hΩc hΩs (hf.const_smul (by norm_num) hΩ c)
      ((tsupport_mul_subset_right (f := fun _ => c) (g := f)).trans hfs) =
      c • h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs := by
  symm
  apply eq_h1ComplDirichletChartPullback_of_coeFn
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul c
    (H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs)),
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs] with x hx hfx
  rw [hx, Pi.smul_apply, hfx, chartPullback_const_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_smul

theorem h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ω) :
    h1ComplDirichletChartPullback q α hΩ hΩc hΩs
      (MemWkp_of_smooth_compactSupport hΩ hf hfc hfs (by norm_num) 1) hfs =
      smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α hf hfc
        (hfs.trans (subset_closure.trans hΩs))) := by
  symm
  apply eq_h1ComplDirichletChartPullback_of_coeFn
  rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  exact (smoothScalarDirichletChartPullback q α hf hfc
    (hfs.trans (subset_closure.trans hΩs))).memLp_two.coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet

theorem chartInverse_h1ComplDirichletChartPullback_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    (fun z => H1ComplDirichletToLp q (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω] f := by
  exact ae_chartInverse_eq_of_chartPullback q α hΩ.measurableSet hΩc
    (hΩs.trans (_root_.Set.image_mono interior_subset))
    (h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.chartInverse_h1ComplDirichletChartPullback_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.chartInverse_h1ComplDirichletChartPullback_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.chartInverse_h1ComplDirichletChartPullback_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.chartInverse_h1ComplDirichletChartPullback_coeFn


theorem dirichletLocalWeakPartialLp_eq_ae_of_coeFn_eq_chartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {f : EuStd → ℝ}
    (hv : (H1ComplDirichletToLp q v : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α f)
    (j : Fin (Module.finrank ℝ EuN)) {g : EuStd → ℝ}
    (hg : _root_.MeasureTheory.LocallyIntegrable g (volume.restrict Ω))
    (hweak : DeGiorgi.HasWeakPartialDeriv j g f Ω) :
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v : EuStd → ℝ)
      =ᵐ[volume.restrict Ω] g := by
  have hval : (fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[
      volume.restrict Ω] f := by
    exact ae_chartInverse_eq_of_chartPullback q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) hv
  have hvweak : DeGiorgi.HasWeakPartialDeriv j
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v) f Ω := by
    intro ψ hψ hψc hψs
    have hw := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v
      ψ hψ hψc hψs
    rw [← hw]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hval] with z hz
    rw [hz]
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hvweak hweak
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_coeFn_eq_chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_coeFn_eq_chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_coeFn_eq_chartPullback ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_coeFn_eq_chartPullback


theorem dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω)
    (i : Fin (Module.finrank ℝ EuN)) {v : EuStd → ℝ}
    (hv : _root_.MeasureTheory.LocallyIntegrable v (volume.restrict Ω))
    (hweak : DeGiorgi.HasWeakPartialDeriv i v f Ω) :
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
      (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs) : EuStd → ℝ)
      =ᵐ[volume.restrict Ω] v := by
  let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs
  have hval := chartInverse_h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs
  have hw : DeGiorgi.HasWeakPartialDeriv i
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i w) f Ω := by
    intro ψ hψ hψc hψs
    have hw := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i w ψ hψ hψc hψs
    rw [← hw]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hval] with z hz
    rw [hz]
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hw hweak
    (Lp.memLp _ |>.locallyIntegrable (by norm_num)) hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae

theorem tendsto_h1ComplDirichletChartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} {l : Filter Z} {f : Z → EuStd → ℝ} {g : EuStd → ℝ}
    (hf : ∀ z, MemWkp 1 2 (f z) Ω) (hfs : ∀ z, tsupport (f z) ⊆ Ω)
    (hg : MemWkp 1 2 g Ω) (hgs : tsupport g ⊆ Ω)
    (hfg : _root_.Filter.Tendsto (fun z => iteratedWeakSobolevNorm 1 2 (fun x => f z x - g x) Ω)
      l (𝓝 0)) :
    _root_.Filter.Tendsto (fun z => h1ComplDirichletChartPullback q α hΩ hΩc hΩs (hf z) (hfs z)) l
      (𝓝 (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hg hgs)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_h1ComplDirichletChartPullback_le_wkpNorm q α hΩ hΩc hΩs
  have ht : _root_.Filter.Tendsto (fun z => C * (iteratedWeakSobolevNorm 1 2
      (fun x => f z x - g x) Ω).toReal) l (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, _root_.MulZeroClass.mul_zero, Function.comp_apply] using
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hfg).const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro z
  rw [← h1ComplDirichletChartPullback_sub q α hΩ hΩc hΩs (hf z) (hfs z) hg hgs]
  exact hbound _ ((hf z).sub (by norm_num) hΩ hg)
    ((tsupport_sub _ _).trans (_root_.Set.union_subset (hfs z) hgs))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.tendsto_h1ComplDirichletChartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.tendsto_h1ComplDirichletChartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.tendsto_h1ComplDirichletChartPullback ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.tendsto_h1ComplDirichletChartPullback

theorem exists_smooth_tendsto_h1ComplDirichletChartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    ∃ (φ : ℕ → EuStd → ℝ) (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j))
      (hφc : ∀ j, HasCompactSupport (φ j)) (hφs : ∀ j, tsupport (φ j) ⊆ Ω),
      _root_.Filter.Tendsto (fun j => iteratedWeakSobolevNorm 1 2 (fun x => f x - φ j x) Ω)
        _root_.Filter.atTop (𝓝 0) ∧
      _root_.Filter.Tendsto (fun j => smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α
        (hφ j) (hφc j) ((hφs j).trans (subset_closure.trans hΩs)))) _root_.Filter.atTop
        (𝓝 (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs)) := by
  have hfc : HasCompactSupport f :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) (hfs.trans subset_closure)
  let ε := fun j : ℕ => (1 : ℝ) / (j + 1)
  have hε : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have hεt : _root_.Filter.Tendsto ε _root_.Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose φ hφ hφc hφs herr using fun j =>
    hf.exists_smooth_compactSupport_approx hΩ 1 2 (by norm_num) (by norm_num) hfc hfs (ε j) (hε j)
  have hφW : ∀ j, MemWkp 1 2 (φ j) Ω := fun j =>
    MemWkp_of_smooth_compactSupport hΩ (hφ j) (hφc j) (hφs j) (by norm_num) 1
  have hnorm : _root_.Filter.Tendsto (fun j => iteratedWeakSobolevNorm 1 2 (fun x => f x - φ j x) Ω)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hεt)
      (fun _ => zero_le) herr
  refine ⟨φ, hφ, hφc, hφs, hnorm, ?_⟩
  have hcomm (j : ℕ) : iteratedWeakSobolevNorm 1 2 (fun x => φ j x - f x) Ω =
      iteratedWeakSobolevNorm 1 2 (fun x => f x - φ j x) Ω := by
    simpa only [neg_one_mul, neg_sub, enorm_neg, enorm_one, one_mul] using
      wkpNorm_const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
        (hf.sub (by norm_num) hΩ (hφW j)) (-1)
  have ht := tendsto_h1ComplDirichletChartPullback q α hΩ hΩc hΩs hφW hφs hf hfs
    (by simpa only [hcomm] using hnorm)
  have heq (j : ℕ) : h1ComplDirichletChartPullback q α hΩ hΩc hΩs (hφW j) (hφs j) =
      smoothToH1ComplDirichlet q (smoothScalarDirichletChartPullback q α
        (hφ j) (hφc j) ((hφs j).trans (subset_closure.trans hΩs))) :=
    h1ComplDirichletChartPullback_eq_smoothToH1ComplDirichlet q α hΩ hΩc hΩs
      (hφ j) (hφc j) (hφs j)
  simpa only [heq] using ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smooth_tendsto_h1ComplDirichletChartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smooth_tendsto_h1ComplDirichletChartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smooth_tendsto_h1ComplDirichletChartPullback ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smooth_tendsto_h1ComplDirichletChartPullback


open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
theorem dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {P H η : EuStd → ℝ}
    (hv : (H1ComplDirichletToLp q v : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun z => η z * P z))
    (hP : _root_.MeasureTheory.MemLp P 2 (volume.restrict Ω)) (hH : _root_.MeasureTheory.MemLp H 2 (volume.restrict Ω))
    (j : Fin (Module.finrank ℝ EuN))
    (hweak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ EuN) j H P Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      (fun z => η z * H z + fderiv ℝ η z (EuclideanSpace.single j 1) * P z) := by
  have hP' : _root_.MeasureTheory.LocallyIntegrable P (volume.restrict Ω) := hP.locallyIntegrable (by norm_num)
  have hH' : _root_.MeasureTheory.LocallyIntegrable H (volume.restrict Ω) := hH.locallyIntegrable (by norm_num)
  have hpj : DeGiorgi.HasWeakPartialDeriv j H P Ω := hweak
  have hmul := hpj.mul_smooth hΩ hη hP' hH'
  have hloc : _root_.MeasureTheory.LocallyIntegrable
      (fun z => η z * H z + fderiv ℝ η z (EuclideanSpace.single j 1) * P z)
      (volume.restrict Ω) := by
    have hηm : _root_.MeasureTheory.MemLp η ∞ (volume.restrict Ω) :=
      (hη.continuous.memLp_of_hasCompactSupport hηc).restrict Ω
    have hdη : _root_.MeasureTheory.MemLp (fun z => fderiv ℝ η z (EuclideanSpace.single j 1)) ∞
        (volume.restrict Ω) :=
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const
        |>.memLp_of_hasCompactSupport (hηc.fderiv_apply (𝕜 := ℝ)
          (EuclideanSpace.single j 1)) : _root_.MeasureTheory.MemLp _ ∞ _root_.MeasureTheory.MeasureSpace.volume).restrict Ω
    have hG : _root_.MeasureTheory.MemLp (fun z => η z * H z + fderiv ℝ η z (EuclideanSpace.single j 1) * P z) 2 (volume.restrict Ω) := (hH.mul' hηm).add (hP.mul' hdη)
    exact hG.locallyIntegrable (by norm_num)
  exact dirichletLocalWeakPartialLp_eq_ae_of_coeFn_eq_chartPullback q α hΩ hΩc hΩs v hv j hloc hmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul


theorem dirichletLocalWeakPartialLp_restrict_ae
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) (k : Fin (Module.finrank ℝ EuN)) (u : H1ComplDirichlet q) :
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k u := by
  have ho := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u)
  have hi := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k u
  have hLo := ((Lp.memLp (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u)).mono_measure
    (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLi := (Lp.memLp (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k u)).locallyIntegrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀ ho hi hLo hLi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_restrict_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_restrict_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_restrict_ae ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_restrict_ae

theorem dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul_localWeakPartial
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) (u v : H1ComplDirichlet q)
    (k j : Fin (Module.finrank ℝ EuN)) {H η : EuStd → ℝ}
    (hv : (H1ComplDirichletToLp q v : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α
        (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k u z))
    (hH : _root_.MeasureTheory.MemLp H 2 (volume.restrict Ω₀))
    (hweak : DeGiorgi.HasWeakPartialDeriv j H
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u) Ω₀)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j v : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      (fun z => η z * H z + fderiv ℝ η z (EuclideanSpace.single j 1) *
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u z) := by
  have hgrad := dirichletLocalWeakPartialLp_restrict_ae q α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub k u
  have hw := hasWeakPartialDeriv_congr_ae hΩ₀ j hgrad hweak
  have heq := dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul q α hΩ₀ hΩ₀c hΩ₀s v hv
    (Lp.memLp _) hH j hw hη hηc
  apply heq.trans
  filter_upwards [hgrad] with z hz
  exact congrArg (fun p : ℝ => η z * H z + fderiv ℝ η z (EuclideanSpace.single j 1) * p) hz.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul_localWeakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul_localWeakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul_localWeakPartial ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul_localWeakPartial

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
