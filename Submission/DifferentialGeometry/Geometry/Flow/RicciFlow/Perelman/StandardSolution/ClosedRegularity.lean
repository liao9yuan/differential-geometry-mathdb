import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.ClosedJetEvolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz
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
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

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

private theorem closed_metric_gram (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (α β : ℝ) (hab : α < β)
    (hjets : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (_root_.Set.Icc α β ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hpde : ∀ t ∈ _root_.Set.Ioo α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    ∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc α β ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet) := by
  intro x₀ i j
  let V := interior (extChartAt 𝓘(ℝ, E) x₀).target
  let G := fun t => chartGramPi (g t) x₀
  have hs (i₁ i₂ : Fin (Module.finrank ℝ E)) (t : ℝ) (_ht : t ∈ _root_.Set.Icc α β) :
      ContDiffOn ℝ ∞ (chartGramOnE (g t) x₀ i₁ i₂) V :=
    (chartGramOnE_contDiffOn (g t) x₀ i₁ i₂).mono interior_subset
  have hGs (t : ℝ) (ht : t ∈ _root_.Set.Icc α β) : ContDiffOn ℝ ∞ (G t) V :=
    contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hs a b t ht))
  have hGjets (r : ℕ) : ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2) (_root_.Set.Icc α β ×ˢ V) := by
    apply pi_jet_continuous (fun a t x b => chartGramOnE (g t) x₀ a b x) (_root_.Set.Icc α β) V isOpen_interior
    · intro a t ht
      exact contDiffOn_pi.mpr (fun b => hs a b t ht)
    · intro a k
      exact pi_jet_continuous (fun b t => chartGramOnE (g t) x₀ a b) (_root_.Set.Icc α β) V
        isOpen_interior (hs a) (fun b k => hjets k x₀ a b) k
  let Ω : Set (MatJet E (Module.finrank ℝ E)) := {p | (Matrix.of p.1).det ≠ 0}
  have hΩ : IsOpen Ω := isOpen_ne_fun
    ((contDiff_det_of_entries (fun p : MatJet E (Module.finrank ℝ E) => Matrix.of p.1)
      (fun a b => contDiff_jetVal a b)).continuous) continuous_const
  have hΦ : ContDiffOn ℝ ∞ (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) Ω :=
    fun p hp => (contDiffAt_jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) hp).contDiffWithinAt
  have hmap : _root_.Set.MapsTo (Function.uncurry (fun t y => jet2 (G t) y)) (_root_.Set.Icc α β ×ˢ V) Ω := by
    intro p _
    change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt 𝓘(ℝ, E) x₀).symm p.2)).det ≠ 0
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g p.1) x₀ (by change _ ∈ (_root_.Set.univ : Set E); trivial)).ne'
  have hGPDE (t : ℝ) (ht : t ∈ _root_.Set.Ioo α β) (y : E) (hy : y ∈ V) :
      HasDerivAt (fun s => G s y) (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (jet2 (G t) y)) t := by
    have hAt := (hGs t (_root_.Set.Ioo_subset_Icc_self ht) y hy).contDiffAt (isOpen_interior.mem_nhds hy)
    have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (G t) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact ((hGs t (_root_.Set.Ioo_subset_Icc_self ht) z hz).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hG2 := (hAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hyT : y ∈ (extChartAt 𝓘(ℝ, E) x₀).target := interior_subset hy
    have hgs : (extChartAt 𝓘(ℝ, E) x₀).symm y ∈ chartLeviCivitaGoodSet (I := 𝓘(ℝ, E)) x₀ := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
      exact (extChartAt 𝓘(ℝ, E) x₀).map_target hyT
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    change HasDerivAt (fun s => chartGramOnE (g s) x₀ a b y)
      (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (jet2 (G t) y) a b) t
    rw [jetRicciFlow_chartGram (g t) x₀ hy (hAt.differentiableAt (by simp)) hG1 hG2]
    have hmetric := (hpde t ht ((extChartAt 𝓘(ℝ, E) x₀).symm y)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x₀ a ((extChartAt 𝓘(ℝ, E) x₀).symm y))
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x₀ b ((extChartAt 𝓘(ℝ, E) x₀).symm y)))
    exact (chartGramEntryPDE_of_metricPDE g x₀ (sL := _root_.Set.univ) hgs
      ((extChartAt 𝓘(ℝ, E) x₀).right_inv hyT) a b hmetric.hasDerivWithinAt).hasDerivAt _root_.Filter.univ_mem
  have hSmooth := (contDiffOn_and_equation_Icc_of_spatial_jets G α β hab V isOpen_interior
    (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) Ω hΩ hΦ hmap hGs hGjets hGPDE).1
  have hentry := (contDiffOn_pi.mp (contDiffOn_pi.mp hSmooth i)) j
  have hnative : ContDiffOn ℝ ∞ (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (_root_.Set.Icc α β ×ˢ (_root_.Set.univ : Set E)) := by
    change ContDiffOn ℝ ∞
      (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt 𝓘(ℝ, E) x₀).symm p.2) i j)
      (_root_.Set.Icc α β ×ˢ V) at hentry
    simpa only [V, extChartAt_model_space_eq_id, PartialEquiv.refl_target, interior_univ,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq] using hentry
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (hnative.mono (_root_.Set.prod_mono subset_rfl (_root_.Set.subset_univ _))).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.closed_metric_gram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.closed_metric_gram target :: scope.openDecls } }

private theorem equation_closed (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (α β : ℝ) (hab : α < β)
    (hgram : ∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc α β ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet))
    (hpde : ∀ t ∈ _root_.Set.Ioo α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    ∀ t ∈ _root_.Set.Icc α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (_root_.Set.Icc α β) t := by
  have hRicField := ricciCont_of_joint g (_root_.Set.Icc α β) (uniqueDiffOn_Icc hab) hgram
  intro t ht x v w
  have hg : ContinuousOn (fun s => (g s).inner x v w) (_root_.Set.Icc α β) := by
    exact (tensor0SEvalCLM (I := 𝓘(ℝ, E)) (vec2 v w)).continuous.comp_continuousOn
      (metricCovDeriv_contDiffOn_time g (_root_.Set.Icc α β) hgram (g α) 0 x).continuousOn
  have hRic : ContinuousOn (fun s => ricciTensor (g s) x v w) (_root_.Set.Icc α β) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun s : _root_.Set.Icc α β => ricciTensor (g s.val) x v w)
    have hh := hRicField.eval_continuous
      (P := _root_.Set.Icc α β) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun s => s.property) continuous_const
      (v := fun i _ => vec2 v w i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using hh
  exact hasDerivIcc_of_int hab hg (continuousOn_const.mul hRic)
    (fun s hs => hpde s hs x v w) ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.equation_closed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.equation_closed target :: scope.openDecls } }

theorem contMDiffOn_and_equation_Icc_of_spatial_jets
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (α β : ℝ) (hab : α < β)
    (hjets : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (_root_.Set.Icc α β ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hpde : ∀ t ∈ _root_.Set.Ioo α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    (∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc α β ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet)) ∧
      ∀ t ∈ _root_.Set.Icc α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (g s).inner x v w)
          (-2 * ricciTensor (g t) x v w) (_root_.Set.Icc α β) t := by
  have hgram := closed_metric_gram g α β hab hjets hpde
  exact ⟨hgram, equation_closed g α β hab hgram hpde⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.contMDiffOn_and_equation_Icc_of_spatial_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.contMDiffOn_and_equation_Icc_of_spatial_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.contMDiffOn_and_equation_Icc_of_spatial_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.contMDiffOn_and_equation_Icc_of_spatial_jets

end DifferentialGeometry.PDE.RicciFlow
