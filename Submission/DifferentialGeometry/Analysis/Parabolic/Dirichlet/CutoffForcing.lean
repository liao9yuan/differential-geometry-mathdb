import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

private theorem ae_eq_add_of_ae_ae_eq_sub
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : _root_.MeasureTheory.Measure A} {ν : _root_.MeasureTheory.Measure B} [_root_.MeasureTheory.SFinite ν]
    (P : _root_.MeasureTheory.Lp ℝ 2 (μ.prod ν)) {Q E R : A × B → ℝ}
    (hQ : _root_.MeasureTheory.MemLp Q 2 (μ.prod ν)) (hE : _root_.MeasureTheory.MemLp E 2 (μ.prod ν))
    (hP : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, P (t, x) = R (t, x))
    (hR : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, Q (t, x) = R (t, x) - E (t, x)) :
    P =ᵐ[μ.prod ν] fun p => Q p + E p := by
  let Q' := hQ.toLp Q
  let E' := hE.toLp E
  have hmeas : MeasurableSet {p | P p = Q' p + E' p} :=
    (Lp.stronglyMeasurable P).measurableSet_eq_fun
      ((Lp.stronglyMeasurable Q').add (Lp.stronglyMeasurable E'))
  have heq : P =ᵐ[μ.prod ν] fun p => Q' p + E' p := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [hP, hR, Measure.ae_ae_of_ae_prod hQ.coeFn_toLp,
      Measure.ae_ae_of_ae_prod hE.coeFn_toLp] with t hPt hRt hQt hEt
    filter_upwards [hPt, hRt, hQt, hEt] with x hPx hRx hQx hEx
    change P (t, x) = hQ.toLp Q (t, x) + hE.toLp E (t, x)
    rw [hQx, hEx, hRx]
    linarith
  filter_upwards [heq, hQ.coeFn_toLp, hE.coeFn_toLp] with p hp hQp hEp
  change P p = hQ.toLp Q p + hE.toLp E p at hp
  rwa [hQp, hEp] at hp

run_cmd do
  let target := ``Submission.ae_eq_add_of_ae_ae_eq_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ae_eq_add_of_ae_ae_eq_sub target :: scope.openDecls } }

section

variable {A B X ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite ν]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

private theorem integral_dual_add_eq_source_add
    (D : ι → X →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 ν) {Q Mx Ex : ι → A × B → ℝ}
    (hQ : ∀ j, _root_.MeasureTheory.MemLp (Q j) 2 (μ.prod ν))
    (hE : ∀ j, _root_.MeasureTheory.MemLp (Ex j) 2 (μ.prod ν))
    (hME : ∀ j, Mx j =ᵐ[μ.prod ν] fun p => Q j p + Ex j p)
    (ℓ Lm : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) 2 μ) (S : _root_.MeasureTheory.Lp ℝ 2 μ → X → ℝ)
    (hℓ : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (v : X), (∫ t, τ t * ℓ t v ∂μ) = S τ v -
      ∑ j, ∫ p, τ p.1 * Q j p * D j v p.2 ∂μ.prod ν)
    (hLm : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (v : X), (∫ t, τ t * Lm t v ∂μ) =
      ∑ j, ∫ p, τ p.1 * Mx j p * D j v p.2 ∂μ.prod ν)
    (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (v : X) :
    (∫ t, τ t * (ℓ + Lm) t v ∂μ) = S τ v +
      ∑ j, ∫ p, τ p.1 * Ex j p * D j v p.2 ∂μ.prod ν := by
  have h1 : _root_.MeasureTheory.Integrable (fun t => τ t * ℓ t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp ℓ)
  have h2 : _root_.MeasureTheory.Integrable (fun t => τ t * Lm t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Lm)
  have hparts (j) : (∫ p, τ p.1 * Mx j p * D j v p.2 ∂μ.prod ν) =
      (∫ p, τ p.1 * Q j p * D j v p.2 ∂μ.prod ν) +
      ∫ p, τ p.1 * Ex j p * D j v p.2 ∂μ.prod ν := by
    rw [← _root_.MeasureTheory.integral_add (MemLp.integrable_mul_tensor (hQ j) τ (D j v))
      (MemLp.integrable_mul_tensor (hE j) τ (D j v))]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hME j] with p hp
    rw [hp]
    ring
  have hadd : (∫ t, τ t * (ℓ + Lm) t v ∂μ) =
      (∫ t, τ t * ℓ t v ∂μ) + ∫ t, τ t * Lm t v ∂μ := by
    rw [← _root_.MeasureTheory.integral_add h1 h2]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_add ℓ Lm] with t ht
    rw [ht]
    change τ t * (ℓ t v + Lm t v) = _
    ring
  rw [hadd, hℓ, hLm]
  simp_rw [hparts, Finset.sum_add_distrib]
  ring

run_cmd do
  let target := ``Submission.integral_dual_add_eq_source_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `integral_dual_add_eq_source_add target :: scope.openDecls } }

end

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric I_hs M} :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.h1ComplDirichletBilinearSeminormed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.h1ComplDirichletBilinearSeminormed target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private theorem memLp_cutoff_gradient_flux_error
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} (hμ : μ ≤ volume.restrict J)
    {V : ℝ × EuStd → ℝ} (hV : _root_.MeasureTheory.MemLp V 2 (μ.prod (volume.restrict Ω)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∀ j, _root_.MeasureTheory.MemLp (fun p : ℝ × EuStd => ∑ i,
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p) 2 (μ.prod (volume.restrict Ω)) := by
  have htarget : closure Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (_root_.Set.image_mono interior_subset)
  have hcjoint (i j) : ContinuousOn (fun p : ℝ × EuStd =>
      MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2)
        (J ×ˢ closure Ω) :=
    (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => htarget hp.2)).mul
        (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
  have hcoeff (i j) : _root_.MeasureTheory.MemLp (fun p : ℝ × EuStd =>
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1)) ∞ (μ.prod (volume.restrict Ω)) := by
    have hdiff : Continuous (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_snd
    have h := ((hcjoint i j).mul hdiff.continuousOn).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure)
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod _root_.MeasureTheory.MeasureSpace.volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  intro j
  exact _root_.MeasureTheory.memLp_finsetSum Finset.univ fun i _ => hV.mul (r := 2) (hcoeff i j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.memLp_cutoff_gradient_flux_error
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.memLp_cutoff_gradient_flux_error target :: scope.openDecls } }

private theorem exists_local_dirichlet_main_flux_dual
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hF : ∀ t u v, F t u v = ∑ i, ∑ j, ∫ x,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u x *
        (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v x ∂volume.restrict Ω)
    {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.SFinite μ] (hμ : μ ≤ volume.restrict J)
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ) :
    ∃ P : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ j, ∀ᵐ t ∂μ, (fun x => P j (t, x)) =ᵐ[volume.restrict Ω]
        fun x => ∑ i, (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) ∧
      (∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * ℓ t z ∂μ) =
          ∑ j, ∫ p, τ p.1 * P j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        _root_.MeasureTheory.Integrable (fun t => F t (v t) (z t)) μ ∧
        (∫ t, ℓ t (z t) ∂μ) = ∫ t, F t (v t) (z t) ∂μ := by
  let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
    MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
  have hc (i j) : _root_.MeasureTheory.MemLp (c i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have hcont : ContinuousOn (c i j) (J ×ˢ closure Ω) :=
      (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => (hΩs.trans (_root_.Set.image_mono interior_subset)) hp.2)).mul
        (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
    have h := hcont.memLp_top_of_subset_isCompact (hJc.prod hΩc)
      (hJc.measurableSet.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure)
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod _root_.MeasureTheory.MeasureSpace.volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  obtain ⟨P, hP, hp⟩ := MeasureTheory.exists_lp_flux_of_bilinear_integral
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs) c hc F hF v
  obtain ⟨ℓ, hℓ, _, hℓv⟩ := exists_lp_chart_divergence_dual_integral_integral α hΩ hΩc hΩs P
  exact ⟨P, ℓ, hP, hℓ, fun z => ⟨(hp z).1, (hℓv z).trans (hp z).2.symm⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_main_flux_dual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_main_flux_dual target :: scope.openDecls } }

theorem exists_cutoff_forcing_dual
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} (hμ : μ ≤ volume.restrict J)
    (V : ℝ × EuStd → ℝ) (hV : _root_.MeasureTheory.MemLp V 2 (μ.prod (volume.restrict Ω)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hF : ∀ t u z, F t u z = ∑ i, ∑ j, ∫ x in Ω,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u x *
        (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z x)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hQ : ∀ j, _root_.MeasureTheory.MemLp (Q j) 2 (μ.prod (volume.restrict Ω)))
    (hℓ : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
      MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
    let E := fun j (p : ℝ × EuStd) => ∑ i, c i j p * fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
    (∀ j, ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω,
      Q j (t, x) = (∑ i, c i j (t, x) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) - E j (t, x)) →
    ∃ Lm : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * (ℓ + Lm) t z ∂μ) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
              ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, Lm t (z t) ∂μ) = ∫ t, F t (v t) (z t) ∂μ := by
  let : _root_.MeasureTheory.IsLocallyFiniteMeasure μ := Measure.isLocallyFiniteMeasure_of_le hμ
  intro c E hflux
  have hE : ∀ j, _root_.MeasureTheory.MemLp (E j) 2 (μ.prod (volume.restrict Ω)) :=
    memLp_cutoff_gradient_flux_error q hG hJc hJ α hΩ hΩc hΩs hμ hV hη
  obtain ⟨P, Lm, hP, hLm, hpair⟩ := exists_local_dirichlet_main_flux_dual q hG hJc hJ α hΩ hΩc hΩs F hF hμ v
  have hPE (j) : P j =ᵐ[μ.prod (volume.restrict Ω)] fun p => Q j p + E j p :=
    ae_eq_add_of_ae_ae_eq_sub (μ := μ) (ν := volume.restrict Ω) (P j)
      (Q := Q j) (E := E j)
      (R := fun p => ∑ i, c i j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v p.1) p.2)
      (hQ j) (hE j) (hP j) (hflux j)
  exact ⟨Lm, integral_dual_add_eq_source_add
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs) hQ hE hPE ℓ Lm _ hℓ hLm,
    fun z => (hpair z).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_cutoff_forcing_dual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_cutoff_forcing_dual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_cutoff_forcing_dual ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_cutoff_forcing_dual

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
