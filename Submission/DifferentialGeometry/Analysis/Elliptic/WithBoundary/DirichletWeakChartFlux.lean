import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
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

theorem ae_cutoff_gradient_flux_eq_density_ratio
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (g : Z → SmoothRiemannianMetric I_hs M)
    (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) (u v : Z → H1ComplDirichlet q)
    (k : Fin (Module.finrank ℝ EuN))
    (H : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω₀)))
    {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => H i (t, z))
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t)) Ω₀)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    let ρ := fun p : Z × EuStd => MetricExtension.densityOnEuclid (g p.1) α p.2
    let σ := fun p : Z × EuStd => MetricExtension.densityOnEuclid q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : Z × EuStd) => MetricExtension.weightedInvGramOnEuclid (g p.1) α i j p.2
    let c := fun i j (p : Z × EuStd) => σ p * MetricExtension.invGramOnEuclid (g p.1) α i j p.2
    ∀ j, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω₀,
      (∑ i, (η z / r (t, z)) * A i j (t, z) * H i (t, z)) =
        (∑ i, c i j (t, z) * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) z) -
          ∑ i, c i j (t, z) * fderiv ℝ η z (EuclideanSpace.single i 1) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) z := by
  intro ρ σ r A c j
  have h := ae_cutoff_gradient_flux_eq q α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub
    u v k H A r hv hweak hη hηc j
  filter_upwards [h] with t ht
  filter_upwards [ht, _root_.MeasureTheory.ae_restrict_mem hΩ₀.measurableSet] with z hz hzm
  have hcoeff (i) : A i j (t, z) / r (t, z) = c i j (t, z) :=
    DifferentialGeometry.Analysis.Parabolic.Dirichlet.weightedInvGramOnEuclid_div_density_ratio
      q (g t) α i j z (hΩ₀s.trans (_root_.Set.image_mono interior_subset) (subset_closure hzm))
  simpa only [hcoeff] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_gradient_flux_eq_density_ratio then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_gradient_flux_eq_density_ratio"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_gradient_flux_eq_density_ratio ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_gradient_flux_eq_density_ratio

theorem ae_cutoff_flux_eq_density_ratio
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M)
    (g : Z → SmoothRiemannianMetric I_hs M)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (H : Z × EuStd → ℝ) (K : Fin (Module.finrank ℝ EuN) → Z × EuStd → ℝ)
    (hH : _root_.MeasureTheory.MemLp H 2 (μ.prod (volume.restrict Ω)))
    (hK : ∀ i, _root_.MeasureTheory.MemLp (K i) 2 (μ.prod (volume.restrict Ω)))
    (v : Z → H1ComplDirichlet q) {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * H (t, z)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => H (t, z)) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    let ρ := fun p : Z × EuStd => MetricExtension.densityOnEuclid (g p.1) α p.2
    let σ := fun p : Z × EuStd => MetricExtension.densityOnEuclid q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : Z × EuStd) => MetricExtension.weightedInvGramOnEuclid (g p.1) α i j p.2
    let c := fun i j (p : Z × EuStd) => σ p * MetricExtension.invGramOnEuclid (g p.1) α i j p.2
    ∀ j, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω,
      (∑ i, (η z / r (t, z)) * A i j (t, z) * K i (t, z)) =
        (∑ i, c i j (t, z) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) z) -
          ∑ i, c i j (t, z) * fderiv ℝ η z (EuclideanSpace.single i 1) * H (t, z) := by
  intro ρ σ r A c j
  classical
  have hpartial (i) : ∀ᵐ t ∂μ,
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
        (fun z => η z * K i (t, z) + fderiv ℝ η z (EuclideanSpace.single i 1) * H (t, z)) :=
    ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul q α hΩ hΩc hΩs v hv
      hH (hK i) i (hweak i) hη
  filter_upwards [ae_all_iff.mpr hpartial] with t ht
  filter_upwards [ae_all_iff.mpr ht, _root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with z hz hzm
  have hcoeff (i) : A i j (t, z) / r (t, z) = c i j (t, z) :=
    DifferentialGeometry.Analysis.Parabolic.Dirichlet.weightedInvGramOnEuclid_div_density_ratio q (g t) α i j z
      (hΩs.trans (_root_.Set.image_mono interior_subset) (subset_closure hzm))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i, ← hcoeff i]
  simp only [div_eq_mul_inv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_flux_eq_density_ratio then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_flux_eq_density_ratio"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_flux_eq_density_ratio ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.ae_cutoff_flux_eq_density_ratio

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
