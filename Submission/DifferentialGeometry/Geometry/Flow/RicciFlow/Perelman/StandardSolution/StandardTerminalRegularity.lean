import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.ClosedJetEvolution
import Submission.DifferentialGeometry.Geometry.Metric.TerminalFamily
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialExistence
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Pi
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.Curvature
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

private theorem pi_jet_continuous {E F A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype A] (f : A → ℝ → E → F) (J : Set ℝ) (V : Set E) (hV : IsOpen V)
    (hs : ∀ i, ∀ t ∈ J, ContDiffOn ℝ ∞ (f i t) V)
    (hj : ∀ i, ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (f i p.1) p.2) (J ×ˢ V)) (r : ℕ) :
    ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (fun x i => f i p.1 x) p.2) (J ×ˢ V) := by
  let L : (A → E [×r]→L[ℝ] F) ≃ₗᵢ[ℝ] (E [×r]→L[ℝ] (A → F)) :=
    ContinuousMultilinearMap.piₗᵢ _ _
  have hh := L.continuous.comp_continuousOn (continuousOn_pi.mpr fun i => hj i r)
  apply hh.congr
  intro p hp
  exact iteratedFDeriv_pi (fun i => (hs i p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2))
    (by exact_mod_cast le_top)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.pi_jet_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.pi_jet_continuous target :: scope.openDecls } }

private theorem closed_metric_gram (g : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (T : ℝ) (hT : 0 < T)
    (hjets : ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContinuousOn (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (_root_.Set.Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target))
    (hpde : ∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (_root_.Set.Ici 0) t) :
    ∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet) := by
  intro x₀ i j
  let V := interior (extChartAt (𝓡 3) x₀).target
  let G := fun t => chartGramPi (g t) x₀
  have hs (a b : Fin (Module.finrank ℝ E3)) (t : ℝ) (_ht : t ∈ _root_.Set.Icc 0 T) :
      ContDiffOn ℝ ∞ (chartGramOnE (g t) x₀ a b) V :=
    (chartGramOnE_contDiffOn (g t) x₀ a b).mono interior_subset
  have hGs (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) : ContDiffOn ℝ ∞ (G t) V :=
    contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hs a b t ht))
  have hGjets (r : ℕ) : ContinuousOn
      (fun p : ℝ × E3 => iteratedFDeriv ℝ r (G p.1) p.2) (_root_.Set.Icc 0 T ×ˢ V) := by
    apply pi_jet_continuous (fun a t x b => chartGramOnE (g t) x₀ a b x) (_root_.Set.Icc 0 T) V isOpen_interior
    · intro a t ht
      exact contDiffOn_pi.mpr (fun b => hs a b t ht)
    · intro a k
      exact pi_jet_continuous (fun b t => chartGramOnE (g t) x₀ a b) (_root_.Set.Icc 0 T) V
        isOpen_interior (hs a) (fun b k => hjets k x₀ a b) k
  let Ω : Set (MatJet E3 (Module.finrank ℝ E3)) := {p | (Matrix.of p.1).det ≠ 0}
  have hΩ : IsOpen Ω := isOpen_ne_fun
    ((contDiff_det_of_entries (fun p : MatJet E3 (Module.finrank ℝ E3) => Matrix.of p.1)
      (fun a b => contDiff_jetVal a b)).continuous) continuous_const
  have hΦ : ContDiffOn ℝ ∞ (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3)) Ω :=
    fun p hp => (contDiffAt_jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3) hp).contDiffWithinAt
  have hmap : _root_.Set.MapsTo (Function.uncurry (fun t y => jet2 (G t) y)) (_root_.Set.Icc 0 T ×ˢ V) Ω := by
    intro p _
    change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt (𝓡 3) x₀).symm p.2)).det ≠ 0
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g p.1) x₀ (by change _ ∈ (_root_.Set.univ : Set E3); trivial)).ne'
  have hGPDE (t : ℝ) (ht : t ∈ _root_.Set.Ioo 0 T) (y : E3) (hy : y ∈ V) :
      HasDerivAt (fun s => G s y) (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3) (jet2 (G t) y)) t := by
    have hAt := (hGs t (_root_.Set.Ioo_subset_Icc_self ht) y hy).contDiffAt (isOpen_interior.mem_nhds hy)
    have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (G t) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact ((hGs t (_root_.Set.Ioo_subset_Icc_self ht) z hz).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hG2 := (hAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hyT : y ∈ (extChartAt (𝓡 3) x₀).target := interior_subset hy
    have hgs : (extChartAt (𝓡 3) x₀).symm y ∈ chartLeviCivitaGoodSet (I := 𝓡 3) x₀ := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
      exact (extChartAt (𝓡 3) x₀).map_target hyT
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    change HasDerivAt (fun s => chartGramOnE (g s) x₀ a b y)
      (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3) (jet2 (G t) y) a b) t
    rw [jetRicciFlow_chartGram (g t) x₀ hy (hAt.differentiableAt (by simp)) hG1 hG2]
    have hmetric := (hpde t ⟨ht.1.le, ht.2⟩ ((extChartAt (𝓡 3) x₀).symm y)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓡 3) x₀ a ((extChartAt (𝓡 3) x₀).symm y))
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓡 3) x₀ b ((extChartAt (𝓡 3) x₀).symm y))).hasDerivAt
        (Ici_mem_nhds ht.1)
    exact (chartGramEntryPDE_of_metricPDE g x₀ (sL := _root_.Set.univ) hgs
      ((extChartAt (𝓡 3) x₀).right_inv hyT) a b hmetric.hasDerivWithinAt).hasDerivAt _root_.Filter.univ_mem
  have hSmooth := (contDiffOn_and_equation_Icc_of_spatial_jets G 0 T hT V isOpen_interior
    (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3)) Ω hΩ hΦ hmap hGs hGjets hGPDE).1
  have hentry := (contDiffOn_pi.mp (contDiffOn_pi.mp hSmooth i)) j
  have hnative : ContDiffOn ℝ ∞ (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (_root_.Set.Icc 0 T ×ˢ (_root_.Set.univ : Set E3)) := by
    change ContDiffOn ℝ ∞
      (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt (𝓡 3) x₀).symm p.2) i j)
      (_root_.Set.Icc 0 T ×ˢ V) at hentry
    simpa only [V, extChartAt_model_space_eq_id, PartialEquiv.refl_target, interior_univ,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq] using hentry
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (hnative.mono (_root_.Set.prod_mono subset_rfl (_root_.Set.subset_univ _))).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.closed_metric_gram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.closed_metric_gram target :: scope.openDecls } }

private theorem equation_closed (g : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (T : ℝ) (hT : 0 < T)
    (hgram : ∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet))
    (hpde : ∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (_root_.Set.Ici 0) t) :
    ∀ t ∈ _root_.Set.Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (_root_.Set.Icc 0 T) t := by
  have hCartesian := cartesian_contDiffOn_of_chartGram g (_root_.Set.Icc 0 T) hgram
  have hRicField := ricciCont_of_joint g (_root_.Set.Icc 0 T) (uniqueDiffOn_Icc hT) hgram
  intro t ht x v w
  have hg : ContinuousOn (fun s => (g s).inner x v w) (_root_.Set.Icc 0 T) := by
    have hh := hCartesian.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs => ⟨hs, _root_.Set.mem_univ x⟩)
    exact (hh.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hRic : ContinuousOn (fun s => ricciTensor (g s) x v w) (_root_.Set.Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun s : _root_.Set.Icc 0 T => ricciTensor (g s.val) x v w)
    have hh := hRicField.eval_continuous
      (P := _root_.Set.Icc 0 T) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun s => s.property) continuous_const
      (v := fun i _ => vec2 v w i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using hh
  exact hasDerivIcc_of_int hT hg (continuousOn_const.mul hRic)
    (fun s hs => (hpde s ⟨hs.1.le, hs.2⟩ x v w).hasDerivAt (Ici_mem_nhds hs.1)) ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.equation_closed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.equation_closed target :: scope.openDecls } }

private theorem closed_seed :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ _root_.Set.Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ _root_.Set.Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ _root_.Set.Icc 0 T, MetricUniformEquivalentOn _root_.Set.univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ _root_.Set.Icc 0 T, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (_root_.Set.Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          ∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (_root_.Set.Ici 0) t := by
  obtain ⟨α, hα, Λ, hΛ, C, L, hC, hL, hb⟩ := standard_uniform_fixed_cap_metric_bounds
  refine ⟨α, hα, Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S T hT hTα hTS
  have hw (θ : ℝ) (hθ : θ ∈ _root_.Set.Ico 0 T) := hb S θ hθ.1 (hθ.2.le.trans hTα)
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hθ.1).mpr hθ.2 |>.trans_le hTS)
  have he (t : ℝ) (ht : t ∈ _root_.Set.Ico 0 T) := (hw t ht).1 t ⟨ht.1, le_rfl⟩
  have hc (N : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Ico 0 T) (x : E3) := (hw t ht).2.1 N t ⟨ht.1, le_rfl⟩ x
  have hl (N : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Ico 0 T) (t : ℝ) (ht : t ∈ _root_.Set.Ico 0 T) (x : E3) :=
    (hw (_root_.Max.max s t) ⟨hs.1.trans (le_max_left _ _), max_lt hs.2 ht.2⟩).2.2 N
      s ⟨hs.1, le_max_left _ _⟩ t ⟨ht.1, le_max_right _ _⟩ x
  obtain ⟨G, hEq, hComp, hEquiv, hCov, hLip, hJets⟩ :=
    exists_closed_terminal_family_of_reference_bounds (I := 𝓡 3) (M := E3)
      inferInstance DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete
      S.metric T Λ hT hΛ C L hL he hc hl
  refine ⟨G, hEq, (hEq 0 ⟨le_rfl, hT⟩).trans S.initial, hComp, hEquiv, hCov, hLip, hJets, ?_⟩
  intro t ht x v w
  have hdom : t ∈ S.domain := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr
    ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).mpr ht.2 |>.trans_le hTS⟩
  have hgerm : (fun s => (G s).inner x v w) =ᶠ[𝓝[_root_.Set.Ici 0] t]
      (fun s => (S.metric s).inner x v w) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsT
    rw [hEq s ⟨hs, hsT⟩]
  rw [hEq t ht]
  exact (S.equation t hdom x v w).congr_of_eventuallyEq hgerm (by rw [hEq t ht])

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.closed_seed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.closed_seed target :: scope.openDecls } }

theorem standard_uniform_smooth_terminal_families :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ _root_.Set.Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ _root_.Set.Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ _root_.Set.Icc 0 T, MetricUniformEquivalentOn _root_.Set.univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ _root_.Set.Icc 0 T, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (_root_.Set.Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          (∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (_root_.Set.Ici 0) t) ∧
          (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (G p.1) x₀ p.2 i j)
              (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          ∀ t ∈ _root_.Set.Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (_root_.Set.Icc 0 T) t := by
  obtain ⟨α, hα, Λ, hΛ, C, L, hC, hL, hs⟩ := closed_seed
  refine ⟨α, hα, Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S T hT hTα hTS
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde⟩ := hs S T hT hTα hTS
  have hgram := closed_metric_gram G T hT hj hpde
  exact ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, equation_closed G T hT hgram hpde⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_smooth_terminal_families then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_smooth_terminal_families"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_smooth_terminal_families ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_smooth_terminal_families
end DifferentialGeometry.PDE.RicciFlow
