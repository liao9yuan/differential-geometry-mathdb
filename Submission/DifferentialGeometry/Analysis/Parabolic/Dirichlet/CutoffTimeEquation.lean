import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartMassPairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

theorem exists_timeH1_of_cutoff_tensor_identity
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    {a b : ℝ} (hab : a < b) (μ : _root_.MeasureTheory.Measure ℝ) (hμ : μ = volume.restrict (_root_.Set.Icc a b))
    (H : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * H (t, z)))
    (hℓ : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
          ∂μ.prod (volume.restrict Ω)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
          ∂μ.prod (volume.restrict Ω))
    (htensor : ∀ (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ _root_.Set.Ioo a b →
      let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
      (∫ p, deriv τ p.1 * (η p.2 * (MetricExtension.densityOnEuclid q α p.2 * H p)) * ψ p.2
          ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
          ∫ p, τ p.1 * B p * ψ p.2
            ∂μ.prod (volume.restrict Ω)) :
    ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
      (∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
        w.toFun s z = _root_.Inner.inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z)) ∧
      w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s) := by
  let : _root_.MeasureTheory.IsFiniteMeasure μ := by rw [hμ]; infer_instance
  let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
  let mass : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (H1ComplDirichletToLp q) (H1ComplDirichletToLp q)
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) (hηs.trans subset_closure)
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (_root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) := Lp.SecondCountableTopology
  obtain ⟨P, hP, _⟩ := Lp.exists_curry (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) H
  have hvP : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * P t z) := by
    filter_upwards [hv, hP] with t hvt hPt
    apply hvt.trans
    apply chartPullback_ae_eq_of_ae_eq q α
    have hall := (_root_.MeasureTheory.ae_restrict_iff' hΩ.measurableSet).mp hPt
    filter_upwards [hall] with x hx
    by_cases hxs : x ∈ tsupport η
    · exact congrArg (η x * ·) (hx (hηs hxs)).symm
    · simp only [image_eq_zero_of_notMem_tsupport hxs, _root_.MulZeroClass.zero_mul]
  have hex : ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
      (fun s => mass (v (a + s))) =ᵐ[timeMeasure (b - a)] w.toFun ∧
      w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s) := by
    refine exists_timeH1_dual_of_tensor_integrals_on (ν := volume.restrict Ω)
      (X := H1ComplDirichlet q) (S := SmoothScalarDirichlet q) hab μ hμ
      (smoothToH1ComplDirichlet q) (denseRange_smoothToH1ComplDirichlet q)
      (mass.comp_memLp v) (Lp.memLp ℓ)
      (W := fun x => η x.2 * (σ x * H x)) (B := B) (Q := Q)
      (R := fun z x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q z)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)))
      (D := fun z j => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (smoothToH1ComplDirichlet q z)) ?_ ?_ ?_
    · intro τ z
      have h := integral_mass_inner_eq_integral_chart_prod q α hΩ hΩc hΩs hη hηc hηs
        τ v P H (hP.mono fun _ ht => ht.symm) (smoothToH1ComplDirichlet q z) hvP
      apply h.trans
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp only [σ]
      ring
    · intro τ z
      exact hℓ τ (smoothToH1ComplDirichlet q z)
    · intro z τ hτ hτc hτs
      exact integral_chart_tensor_test_of_smooth q α hΩ hΩc hΩs μ z τ (htensor z τ hτ hτc hτs)
  obtain ⟨w, hw, hd⟩ := hex
  refine ⟨w, ?_, hd⟩
  filter_upwards [hw] with s hs
  intro z
  exact (congrArg (fun L => L z) hs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_of_cutoff_tensor_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_of_cutoff_tensor_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_of_cutoff_tensor_identity ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_timeH1_of_cutoff_tensor_identity

theorem deriv_ae_eq_of_cutoff_tensor_identity
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    {a b : ℝ} (hab : a < b) (μ : _root_.MeasureTheory.Measure ℝ) (hμ : μ = volume.restrict (_root_.Set.Icc a b))
    (H : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * H (t, z)))
    (hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
      w.toFun s z = _root_.Inner.inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z))
    (hℓ : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
          ∂μ.prod (volume.restrict Ω)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
          ∂μ.prod (volume.restrict Ω))
    (htensor : ∀ (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ _root_.Set.Ioo a b →
      let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
      (∫ p, deriv τ p.1 * (η p.2 * (MetricExtension.densityOnEuclid q α p.2 * H p)) * ψ p.2
          ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
          ∫ p, τ p.1 * B p * ψ p.2
            ∂μ.prod (volume.restrict Ω)) :
    w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s) := by
  obtain ⟨v₁, hv₁, hd₁⟩ := exists_timeH1_of_cutoff_tensor_identity α hΩ hΩc hΩs hη hηs
    hab μ hμ H v ℓ Q B hv hℓ htensor
  have heq : w.toFun =ᵐ[timeMeasure (b - a)] v₁.toFun := by
    filter_upwards [hw, hv₁] with s hs ht
    ext z
    exact (hs z).trans (ht z).symm
  rw [timeH1.deriv_eq_of_toFun_ae_eq heq]
  exact hd₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.deriv_ae_eq_of_cutoff_tensor_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.deriv_ae_eq_of_cutoff_tensor_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.deriv_ae_eq_of_cutoff_tensor_identity ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.deriv_ae_eq_of_cutoff_tensor_identity

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
