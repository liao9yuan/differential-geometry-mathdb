import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquationDensity
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffWeakEquation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

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

theorem exists_lp_dual_of_cutoff_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    (q : SmoothRiemannianMetric I_hs M) (α : M)
    {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {μ₀ : _root_.MeasureTheory.Measure ℝ} {a b : ℝ} [_root_.MeasureTheory.IsFiniteMeasure (μ₀.restrict (_root_.Set.Icc a b))]
    (hreg : _root_.Set.Icc a b ⊆ D.regular)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω₀) :
    let μ := μ₀.restrict (_root_.Set.Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let σ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ {U S : ℝ × EuStd → ℝ} {K : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ},
      _root_.MeasureTheory.MemLp U 2 ν → _root_.MeasureTheory.MemLp S 2 ν → (∀ i, _root_.MeasureTheory.MemLp (K i) 2 ν) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S p * φ p ∂ν) →
      let C := fun p => (r p)⁻¹ * S p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)
      let Q := fun j p => ∑ i, (η p.2 / r p) * A i j p * K i p
      let B := fun p => η p.2 * C p -
        ∑ i, ∑ j, A i j p * K i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      (∀ j, _root_.MeasureTheory.MemLp (Q j) 2 ν) ∧ _root_.MeasureTheory.MemLp B 2 ν ∧
      (∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∀ τ : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t v ∂μ) =
            (∫ p, τ p.1 * B p * H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q j p *
              dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c (hΩ₀Ω.trans hΩs) j v p.2 ∂ν) ∧
      ∀ (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ _root_.Set.Ioo a b →
        let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (∫ p, deriv τ p.1 * (η p.2 * (σ p * U p)) * ψ p.2 ∂ν) =
          (∑ j, ∫ p, τ p.1 * Q j p *
            fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
          ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
  intro μ ν ρ σ r A U S K hU hS hK hweak C Q B
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (_root_.Set.image_mono interior_subset)
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hchart)
  have hσall : ContDiffOn ℝ (⊤ : ℕ∞) σ (D.regular ×ˢ Ω) :=
    (densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => hchart hp.2)
  have hσne (p : ℝ × EuStd) (hp : p.2 ∈ Ω) : σ p ≠ 0 :=
    (densityOnEuclid_pos q α (hchart hp)).ne'
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ Ω) : ρ p ≠ 0 :=
    (densityOnEuclid_pos (g p.1) α (hchart hp)).ne'
  have hrall : ContDiffOn ℝ (⊤ : ℕ∞) r (D.regular ×ˢ Ω) :=
    hρall.div hσall (fun p hp => hσne p hp.2)
  have hrne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ Ω) : r p ≠ 0 :=
    div_ne_zero (hρne p hp.2) (hσne p hp.2)
  have hAall (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ Ω) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α
      hΩs i j
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : _root_.MeasureTheory.MemLp f ∞ ν := by
    have hb := (hc.mono (_root_.Set.prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (_root_.Set.prod_mono Subset.rfl subset_closure) (μ := (μ₀.restrict (_root_.Set.Icc a b)).prod _root_.MeasureTheory.MeasureSpace.volume)
    rw [← Measure.prod_restrict,
      Measure.restrict_restrict_of_subset (Subset.rfl : _root_.Set.Icc a b ⊆ _root_.Set.Icc a b)] at hb
    exact hb
  have hrinv : _root_.MeasureTheory.MemLp (fun p => (r p)⁻¹) ∞ ν := hlift _ (hrall.inv hrne).continuousOn
  have hrt : _root_.MeasureTheory.MemLp (fun p => fderiv ℝ r p (1, 0)) ∞ ν :=
    hlift _ ((hrall.fderiv_of_isOpen (m := (⊤ : ℕ∞)) (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hσmem : _root_.MeasureTheory.MemLp σ ∞ ν := hlift _ hσall.continuousOn
  have hAmem (i j) : _root_.MeasureTheory.MemLp (A i j) ∞ ν := hlift _ (hAall i j).continuousOn
  have hC : _root_.MeasureTheory.MemLp C 2 ν :=
    (hS.mul (r := 2) hrinv).sub ((hU.mul (r := 2) hσmem).mul (r := 2) (hrt.mul (r := ∞) hrinv))
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, _root_.Set.univ_inter]
    exact (_root_.MeasureTheory.measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans hΩs
  let P := fun j p => ∑ i, A i j p * K i p
  have hP (j) : _root_.MeasureTheory.MemLp (P j) 2 ν := by
    apply _root_.MeasureTheory.memLp_finsetSum
    intro i _
    exact (hK i).mul (r := 2) (hAmem i j)
  have hSsub : _root_.Set.Ioo a b ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg (_root_.Set.Ioo_subset_Icc_self hp.1), hsub hp.2⟩
  have hr := hrall.mono hSsub
  have hfixed : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω₀ →
      (∫ p, σ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ i, ∑ j, ∫ p, A i j p * K i p *
          fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, C p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fixed_density_eq_of_weighted_identity hG q α isOpen_Ioo
      (Ioo_subset_Icc_self.trans hreg) hΩ₀ (hsub.trans hchart)
      ((hU.mul (r := 2) hσmem).locallyIntegrable (by norm_num))
      (hS.locallyIntegrable (by norm_num))
      (fun ψ => ∑ i, ∑ j, ∫ p, A i j p * K i p *
        fderiv ℝ ψ p (0, EuclideanSpace.single j 1) ∂ν) hweak hφ hφc hφs
  have hw : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ _root_.Set.Ioo a b ×ˢ Ω₀ →
      (∫ p, (σ p * U p) * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => ψ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, C p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hψrs : tsupport (fun z => ψ z / r z) ⊆ _root_.Set.Ioo a b ×ˢ Ω₀ := by
      simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun z => (r z)⁻¹)).trans hψs
    have hψr : ContDiff ℝ (⊤ : ℕ∞) (fun z => ψ z / r z) :=
      (hψ.contDiffOn.div hr (fun p hp => hrne p (hSsub hp))).contDiff_of_tsupport_subset
        (isOpen_Ioo.prod hΩ₀) hψrs
    have hψrc : HasCompactSupport (fun z => ψ z / r z) := by
      exact hψc.isCompact.of_isClosed_subset (isClosed_tsupport _) (by
        simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun z => (r z)⁻¹)))
    have hdψ (j) : _root_.MeasureTheory.MemLp (fun p => fderiv ℝ (fun z => ψ z / r z) p (0, EuclideanSpace.single j 1)) ∞ ν :=
      ((hψr.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hψrc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
    have hin (i j) : _root_.MeasureTheory.Integrable (fun p => A i j p * K i p *
        fderiv ℝ (fun z => ψ z / r z) p (0, EuclideanSpace.single j 1)) ν :=
      (((hdψ j).mul (r := 2) ((hK i).mul (r := 2) (hAmem i j))).integrable (by norm_num))
    have heach (j) : (∫ p, P j p * fderiv ℝ (fun z => ψ z / r z) p
        (0, EuclideanSpace.single j 1) ∂ν) =
        ∑ i, ∫ p, A i j p * K i p * fderiv ℝ (fun z => ψ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν := by
      simp only [P, Finset.sum_mul]
      exact _root_.MeasureTheory.integral_finsetSum _ (fun i _ => hin i j)
    simp_rw [heach]
    rw [Finset.sum_comm]
    exact hfixed ψ hψ hψc hψs
  have hKO : _root_.Set.Icc a b ×ˢ closure Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg hp.1, hΩ₀Ω hp.2⟩
  have hηc : HasCompactSupport η :=
    hΩ₀c.of_isClosed_subset (isClosed_tsupport η) (hηs.trans subset_closure)
  have hcore := exists_lp_dual_of_fixed_density_cutoff_equation
    (q := q) α hΩ₀ hΩ₀c hΩ₀s (D.regular_isOpen.prod hΩ) hKO hrall hrne
    hC hP hw hη hηc hηs
  have hQeq (j) (p : ℝ × EuStd) : (η p.2 / r p) * P j p = Q j p := by
    simp only [P, Q, Finset.mul_sum, mul_assoc]
  have hBeq (p : ℝ × EuStd) : (η p.2 * C p - ∑ j, P j p * fderiv ℝ
      (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) = B p := by
    simp only [P, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  simpa only [hQeq, hBeq] using hcore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_cutoff_metric_divergence_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_cutoff_metric_divergence_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_cutoff_metric_divergence_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_cutoff_metric_divergence_equation

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
