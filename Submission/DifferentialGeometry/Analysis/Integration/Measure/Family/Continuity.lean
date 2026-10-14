import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Matrix _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.Matrix _root_.BigOperators

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private lemma density_cont
    {g : Real → SmoothRiemannianMetric I M} {K : Set Real}
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦ DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (x₀ : M) :
    ContinuousOn
      (fun p : Real × M ↦ chartDensity (I := I) (g p.1) x₀ p.2)
      (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  let n := Fin (Module.finrank Real E)
  have hdet : ContinuousOn
      (fun p : Real × M ↦
        (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det)
      (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) := by
    have hexp :
        (fun p : Real × M ↦
          (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2).det) =
        fun p : Real × M ↦
          ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : Int) : Real) *
            ∏ i, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 (σ i) i := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finsetSum _ (fun σ _ ↦ ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetProd _ (fun i _ ↦ ?_)
    exact hg x₀ (σ i) i
  exact Real.continuous_sqrt.comp_continuousOn hdet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.density_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.density_cont target :: scope.openDecls } }

private theorem chart_int_cont
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : Real → SmoothRiemannianMetric I M}
    {f : Real → M → Real} {K : Set Real}
    (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦ DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hf : ContinuousOn (fun p : Real × M ↦ f p.1 p.2)
      (K ×ˢ (Set.univ : Set M)))
    (α : M) :
    ContinuousOn
      (fun t : Real ↦
        ∫ y in (extChartAt I α).target,
          f t ((extChartAt I α).symm y) *
            (chartAtlasPOU I M α : M → Real) ((extChartAt I α).symm y) *
            chartDensity (I := I) (g t) α ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) K := by
  classical
  let ρ : M → Real := fun x ↦ (chartAtlasPOU I M α : M → Real) x
  let T : Set M := tsupport ρ
  let target : Set E := (extChartAt I α).target
  let symm : E → M := (extChartAt I α).symm
  let F : Real → E → Real := fun t y ↦
    f t (symm y) * ρ (symm y) *
      chartDensity (I := I) (g t) α (symm y)
  let T' : Set E := (extChartAt I α) '' T
  let μ : _root_.MeasureTheory.Measure E := (modelHaar (E := E)).restrict target
  have htarget_meas : MeasurableSet target := by
    simpa only [target] using measurableSet_extChartAt_target (I := I) α
  have hρ_cont : Continuous ρ := by
    simpa only [ρ] using (chartAtlasPOU I M α).contMDiff.continuous
  have hT_compact : IsCompact T := (isClosed_tsupport ρ).isCompact
  have hT_source : T ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact (chartAtlasPOU_isSubordinate I M α) hx
  have hT'_compact : IsCompact T' := by
    exact hT_compact.image_of_continuousOn
      ((continuousOn_extChartAt (I := I) α).mono hT_source)
  have hT'_target : T' ⊆ target := by
    rintro y ⟨x, hx, rfl⟩
    exact (extChartAt I α).map_source (hT_source hx)
  have hsymm_cont : ContinuousOn symm target := by
    simpa only [symm, target] using continuousOn_extChartAt_symm (I := I) α
  have hsymm_base : ∀ y ∈ target,
      symm y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hs := (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hs
    exact hs
  have hpair : ContinuousOn (fun p : Real × E ↦ (p.1, symm p.2))
      (K ×ˢ target) := by
    refine ContinuousOn.prodMk continuousOn_fst ?_
    exact hsymm_cont.comp continuousOn_snd (fun p hp ↦ hp.2)
  have hF_cont : ContinuousOn (fun p : Real × E ↦ F p.1 p.2)
      (K ×ˢ target) := by
    have hfc : ContinuousOn (fun p : Real × E ↦ f p.1 (symm p.2))
        (K ×ˢ target) := by
      have h := hf.comp hpair (fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩)
      exact h
    have hρc : ContinuousOn (fun p : Real × E ↦ ρ (symm p.2))
        (K ×ˢ target) := by
      exact hρ_cont.continuousOn.comp
        (hsymm_cont.comp continuousOn_snd (fun p hp ↦ hp.2))
        (fun _ _ ↦ Set.mem_univ _)
    have hdc : ContinuousOn
        (fun p : Real × E ↦
          chartDensity (I := I) (g p.1) α (symm p.2))
        (K ×ˢ target) := by
      have h := (density_cont (I := I) hg α).comp hpair
        (fun p hp ↦ ⟨hp.1, hsymm_base p.2 hp.2⟩)
      exact h
    exact (hfc.mul hρc).mul hdc
  have hF_zero : ∀ t ∈ K, ∀ y ∈ target, y ∉ T' → F t y = 0 := by
    intro t _ y hy hyT'
    have hsymm_not : symm y ∉ T := by
      intro hmem
      apply hyT'
      exact ⟨symm y, hmem, (extChartAt I α).right_inv hy⟩
    have hρ_zero : ρ (symm y) = 0 := by
      by_contra hne
      exact hsymm_not (subset_tsupport ρ (Function.mem_support.mpr hne))
    simp only [F, hρ_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul]
  obtain ⟨C, hC⟩ : ∃ C : Real, ∀ p ∈ K ×ˢ T', ‖F p.1 p.2‖ ≤ C := by
    by_cases hne : (K ×ˢ T' : Set (Real × E)).Nonempty
    · have hc : ContinuousOn (fun p : Real × E ↦ ‖F p.1 p.2‖)
          (K ×ˢ T') :=
        (hF_cont.mono (Set.prod_mono_right hT'_target)).norm
      obtain ⟨C, hC⟩ := (hK.prod hT'_compact).bddAbove_image hc
      exact ⟨C, fun p hp ↦ hC ⟨p, hp, rfl⟩⟩
    · exact ⟨0, fun p hp ↦ (hne ⟨p, hp⟩).elim⟩
  let C₀ : Real := _root_.Max.max C 0
  let b : E → Real := fun y ↦ C₀ * T'.indicator (fun _ ↦ (1 : Real)) y
  have hb_int : _root_.MeasureTheory.Integrable b μ := by
    have hT'_meas : MeasurableSet T' := hT'_compact.measurableSet
    have hind : _root_.MeasureTheory.Integrable (T'.indicator (fun _ : E ↦ (1 : Real)))
        (modelHaar (E := E)) := by
      rw [_root_.MeasureTheory.integrable_indicator_iff hT'_meas]
      exact _root_.MeasureTheory.integrableOn_const hT'_compact.measure_ne_top
    have := (hind.restrict (s := target)).const_mul C₀
    simpa only [b, μ, smul_eq_mul] using this
  have hmeas : ∀ t ∈ K, _root_.MeasureTheory.AEStronglyMeasurable (F t) μ := by
    intro t ht
    have hslice : ContinuousOn (F t) target := by
      exact hF_cont.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨ht, hy⟩)
    exact hslice.aestronglyMeasurable htarget_meas
  have hbound : ∀ t ∈ K, ∀ᵐ y ∂μ, ‖F t y‖ ≤ b y := by
    intro t ht
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy ↦ ?_)
    by_cases hyT' : y ∈ T'
    · rw [show b y = C₀ by simp only [b, Set.indicator_of_mem hyT', mul_one]]
      exact (hC (t, y) ⟨ht, hyT'⟩).trans (le_max_left _ _)
    · rw [hF_zero t ht y hy hyT']
      simp only [b, Set.indicator_of_notMem hyT', _root_.MulZeroClass.mul_zero, norm_zero]
      exact le_rfl
  intro t ht
  have hlim : ∀ᵐ y ∂μ,
      Tendsto (fun s ↦ F s y) (𝓝[K] t) (𝓝 (F t y)) := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy ↦ ?_)
    have htime : ContinuousOn (fun s : Real ↦ F s y) K := by
      exact hF_cont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun s hs ↦ ⟨hs, hy⟩)
    exact htime t ht
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[K] t) (μ := μ) (F := F) (f := F t) (bound := b)
    (by filter_upwards [self_mem_nhdsWithin] with s hs; exact hmeas s hs)
    (by filter_upwards [self_mem_nhdsWithin] with s hs; exact hbound s hs)
    hb_int hlim
  change _root_.Filter.Tendsto
    (fun s ↦ ∫ y in (extChartAt I α).target,
      f s ((extChartAt I α).symm y) * chartAtlasPOU I M α ((extChartAt I α).symm y) *
        chartDensity (I := I) (g s) α ((extChartAt I α).symm y) ∂modelHaar)
    (𝓝[K] t)
    (𝓝 (∫ y in (extChartAt I α).target,
      f t ((extChartAt I α).symm y) * chartAtlasPOU I M α ((extChartAt I α).symm y) *
        chartDensity (I := I) (g t) α ((extChartAt I α).symm y) ∂modelHaar))
  exact hdct

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.chart_int_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.chart_int_cont target :: scope.openDecls } }

theorem integral_family_cont
    [T2Space M] [CompactSpace M]
    {g : Real → SmoothRiemannianMetric I M}
    {f : Real → M → Real} {K : Set Real}
    (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦ DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hf : ContinuousOn (fun p : Real × M ↦ f p.1 p.2)
      (K ×ˢ (Set.univ : Set M))) :
    ContinuousOn
      (fun t : Real ↦
        ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g t)) K := by
  classical
  have hf_slice (t : Real) (ht : t ∈ K) : Continuous (f t) := by
    rw [← continuousOn_univ]
    exact hf.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨ht, Set.mem_univ x⟩)
  let S : Finset M := chartAtlasPOUFinset (I := I) (M := M)
  let J : M → Real → Real := fun α t ↦
    ∫ y in (extChartAt I α).target,
      f t ((extChartAt I α).symm y) *
        (chartAtlasPOU I M α : M → Real) ((extChartAt I α).symm y) *
        chartDensity (I := I) (g t) α ((extChartAt I α).symm y)
      ∂(modelHaar (E := E))
  have hJ (α : M) : ContinuousOn (J α) K := by
    simpa only [J] using
      chart_int_cont (I := I) (M := M) hK hg hf α
  have hsum : ContinuousOn (fun t ↦ ∑ α ∈ S, J α t) K := by
    exact continuousOn_finsetSum S (fun α _ ↦ hJ α)
  refine hsum.congr ?_
  intro t ht
  change (∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g t)) =
    ∑ α ∈ S, J α t
  rw [integral_riemannianMeasureFamily_eq_finset_sum
    (I := I) (M := M) g f t (hf_slice t ht)]
  apply Finset.sum_congr rfl
  intro α hα
  let ρ : M → Real := fun x ↦ (chartAtlasPOU I M α : M → Real) x
  have hρ_cont : Continuous ρ := by
    simpa only [ρ] using (chartAtlasPOU I M α).contMDiff.continuous
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x ↦ (chartAtlasPOU I M).nonneg α x
  have hρ_meas : AEMeasurable (fun x : M ↦ ENNReal.ofReal (ρ x))
      (chartLocalMeasure (I := I) (g t) α) :=
    (ENNReal.measurable_ofReal.comp hρ_cont.measurable).aemeasurable
  have hρ_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) (g t) α),
      ENNReal.ofReal (ρ x) < ⊤ := Filter.Eventually.of_forall (fun _ ↦ by simp)
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (f := fun x : M ↦ ENNReal.ofReal (ρ x)) hρ_meas hρ_top]
  have hsmul : (fun x : M ↦ (ENNReal.ofReal (ρ x)).toReal • f t x) =
      fun x : M ↦ f t x * ρ x := by
    funext x
    rw [ENNReal.toReal_ofReal (hρ_nonneg x), smul_eq_mul, mul_comm]
  rw [hsmul, integral_chartLocalMeasure (I := I) (M := M) (g t) α]
  · change _ = J α t
    simp only [J, ρ]
    apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α)
    intro y _
    ring
  · exact ((hf_slice t ht).mul hρ_cont).measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_family_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_family_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_family_cont ``Submission.DifferentialGeometry.Integral.Measure.integral_family_cont

end DifferentialGeometry.Integral.Measure
