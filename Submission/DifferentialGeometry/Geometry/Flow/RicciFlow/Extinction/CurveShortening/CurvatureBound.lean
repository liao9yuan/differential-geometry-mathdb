import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductEmbedding
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureBootstrap
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Bootstrap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

omit [CompactSpace M] in
private theorem curvatureSq_continuousOn_and_periodic
    (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : ProductCurve M) (J : Set ℝ)
    (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (s u : ℝ) (hsu : s < u) (hsub : _root_.Set.Icc s u ⊆ J) (hwindow : _root_.Set.Icc s u ⊆ _root_.Set.Icc a b) :
    ContinuousOn (fun p : ℝ × ℝ => c.curvatureSq B.family.metric lambda p.1 p.2)
      (_root_.Set.univ ×ˢ _root_.Set.Icc s u) ∧
    ∀ τ ∈ _root_.Set.Icc s u, Function.Periodic (fun x => c.curvatureSq B.family.metric lambda x τ) 1 := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hBG⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hfamily, _, _, _, _⟩ := hBG lambda hlambda
  have hm : Bhat.family.metric = fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun G => G.metric) hfamily
  have hsol : c.map.IsSolutionOn Bhat.family.metric (_root_.Set.Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map A B.family.metric lambda hlambda hJ hc).mono hsub
      (fun t ht => (uniqueDiffOn_Icc hsu t ht).uniqueMDiffWithinAt)
  have hsq (x τ : ℝ) (hτ : τ ∈ _root_.Set.Icc s u) :
      c.map.curvatureSq Bhat.family.metric x τ = c.curvatureSq B.family.metric lambda x τ := by
    rw [hm]
    exact c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x τ (hsub hτ)
  have hk : ContinuousOn (fun p : ℝ × ℝ => c.curvatureSq B.family.metric lambda p.1 p.2)
      (_root_.Set.univ ×ˢ _root_.Set.Icc s u) := by
    have hh := CurveMap.Field.smoothOn_curvatureSq Bhat.family.metric Bhat.smooth
      (fun τ hτ => Bhat.regular (hwindow hτ)) (uniqueDiffOn_Icc hsu) c.map hsol.smooth hsol.immersed
    apply hh.continuousOn.congr
    intro p hp
    exact (hsq p.1 p.2 hp.2).symm
  have hper (τ : ℝ) (hτ : τ ∈ _root_.Set.Icc s u) :
      Function.Periodic (fun x => c.curvatureSq B.family.metric lambda x τ) 1 := by
    intro x
    have hh := c.map.curvatureSq_speed_periodic Bhat.family.metric (_root_.Set.Icc s u) hsol.smooth hsol.immersed τ hτ x
    dsimp only at hh
    rw [hsq (x + 1) τ hτ, hsq x τ hτ, hm,
      c.map_speed_eq A B.family.metric lambda hlambda hc.smooth (x + 1) τ (hsub hτ),
      c.map_speed_eq A B.family.metric lambda hlambda hc.smooth x τ (hsub hτ),
      c.speed_add_period B.family.metric lambda hc.smooth τ (hsub hτ) x] at hh
    exact mul_right_cancel₀ (c.speed_pos_of_immersedOn B.family.metric lambda hlambda hc.immersed x τ (hsub hτ)).ne' hh
  exact ⟨hk, hper⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_continuousOn_and_periodic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_continuousOn_and_periodic target :: scope.openDecls } }

theorem exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M, ∀ J : Set ℝ,
      UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s u r : ℝ, a ≤ s → s < u → u ≤ b → _root_.Set.Icc a u ⊆ J →
      0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s → u ≤ s + δ * r ^ 2 →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      ∀ x : ℝ, c.curvatureSq B.family.metric lambda x u ≤ 4 / (u - s) := by
  obtain ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, himprove⟩ := exists_uniform_curvatureSq_improvement B L₀ Θ₀ hL₀ hΘ₀
  refine ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, ?_⟩
  intro lambda hlambda c J hJ hc hlen₀ htotal₀ s u r has hsu hub hinterval hr hrr₀ hlen htime hsmall
  have hsub : _root_.Set.Icc s u ⊆ J := (_root_.Set.Icc_subset_Icc has le_rfl).trans hinterval
  have hwindow : _root_.Set.Icc s u ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc has hub
  obtain ⟨hk, hper⟩ := curvatureSq_continuousOn_and_periodic B lambda hlambda c J hJ hc s u hsu hsub hwindow
  intro x
  apply periodic_le_div_time_of_strict_improvement hsu (by norm_num : (0 : ℝ) < 4) zero_lt_one hk hper
  intro v hv hprior y
  have hh := himprove lambda hlambda c J hJ hc hlen₀ htotal₀ s v r has hv.1 (hv.2.trans hub)
    ((_root_.Set.Icc_subset_Icc le_rfl hv.2).trans hinterval) hr hrr₀ hlen (hv.2.trans htime) hsmall hprior y
  exact hh.trans (div_lt_div_of_pos_right (by norm_num : (2 : ℝ) < 4) (sub_pos.mpr hv.1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature

theorem exists_uniform_curvatureSq_bound_on_solution_interval
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda →
      ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = _root_.Set.Ico a T ∨ J = _root_.Set.Icc a T) →
      ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s ∈ _root_.Set.Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      ∀ x u, u ∈ J → s < u → u ≤ s + δ * r ^ 2 →
      c.curvatureSq B.family.metric lambda x u ≤ 4 / (u - s) := by
  obtain ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, hbound⟩ :=
    exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature B L₀ Θ₀ hL₀ hΘ₀
  refine ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, ?_⟩
  intro lambda hlambda T haT hTb J hJ c hc hlen₀ htotal₀ s hs r hr hrr₀ hlen hsmall x u hu hsu htime
  have hdiff : UniqueDiffOn ℝ J := by
    rcases hJ with rfl | rfl
    · exact uniqueDiffOn_Ico a T
    · exact uniqueDiffOn_Icc haT
  have hub : u ≤ b := by
    rcases hJ with rfl | rfl
    · exact hu.2.le.trans hTb
    · exact hu.2.trans hTb
  have hinterval : _root_.Set.Icc a u ⊆ J := by
    rcases hJ with rfl | rfl
    · intro v hv
      exact ⟨hv.1, hv.2.trans_lt hu.2⟩
    · exact _root_.Set.Icc_subset_Icc le_rfl hu.2
  exact hbound lambda hlambda c J hdiff hc hlen₀ htotal₀ s u r hs.1 hsu hub hinterval
    hr hrr₀ hlen htime hsmall x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_on_solution_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_on_solution_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_on_solution_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_uniform_curvatureSq_bound_on_solution_interval


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem rfs_csf_curvature_bound
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      (∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = _root_.Set.Ico a T ∨ J = _root_.Set.Icc a T) →
      ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
      c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
      ∀ s ∈ _root_.Set.Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ → r ≤ c.length B.family.metric s →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric p q s = r →
        c.arcTotalCurvature B.family.metric p q s ≤ δ) →
      ∀ x u, u ∈ J → s < u → u ≤ s + δ * r ^ 2 →
      c.curvatureSq B.family.metric x u ≤ 4 / (u - s)) ∧
      (∀ lambda : ℝ, 0 < lambda →
      ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = _root_.Set.Ico a T ∨ J = _root_.Set.Icc a T) →
      ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s ∈ _root_.Set.Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      ∀ x u, u ∈ J → s < u → u ≤ s + δ * r ^ 2 →
      c.curvatureSq B.family.metric lambda x u ≤ 4 / (u - s)) := by
  obtain ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, hbound⟩ :=
    ProductCurve.exists_uniform_curvatureSq_bound_on_solution_interval B L₀ Θ₀ hL₀ hΘ₀
  refine ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, ?_, hbound⟩
  intro T haT hTb J hJ c hc hlen₀ htotal₀ s hs r hr hrr₀ hlen hsmall x u hu hsu htime
  have hsol : c.toProductCurve.IsSolutionOn B.family.metric 1 J :=
    (c.toProductCurve_isSolutionOn_iff B.family.metric 1 J).mpr hc
  have hlen₀' : c.toProductCurve.length B.family.metric 1 a ≤ L₀ := by
    rwa [c.toProductCurve_length]
  have htotal₀' : c.toProductCurve.totalCurvature B.family.metric 1 a ≤ Θ₀ := by
    rwa [c.toProductCurve_totalCurvature]
  have hlen' : r ≤ c.toProductCurve.length B.family.metric 1 s := by
    rwa [c.toProductCurve_length]
  have hsmall' : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
      c.toProductCurve.arcLength B.family.metric 1 p q s = r →
      c.toProductCurve.arcTotalCurvature B.family.metric 1 p q s ≤ δ := by
    simpa only [c.toProductCurve_arcLength, c.toProductCurve_arcTotalCurvature] using hsmall
  have hh := hbound 1 zero_lt_one T haT hTb J hJ c.toProductCurve hsol hlen₀' htotal₀'
    s hs r hr hrr₀ hlen' hsmall' x u hu hsu htime
  rwa [c.toProductCurve_curvatureSq] at hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_curvature_bound

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
