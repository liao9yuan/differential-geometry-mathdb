import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedBall
import Submission.DifferentialGeometry.Analysis.Integration.Integral.CompactSupport
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Product
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Lipschitz
import Submission.DifferentialGeometry.Analysis.Parabolic.MetricDivergenceMixedRegularity
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquationAffine
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquationClassical
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import Submission.DifferentialGeometry.Geometry.Metric.Family.Pullback
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Handle
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

private theorem adjoint_apply_eq_mulVec
    {d m : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) :
    let C := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis L.toLinearMap
    (fun i => L.adjoint v i) = C.transpose *ᵥ (fun j => v j) := by
  intro C
  have hm := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis L.adjoint.toLinearMap v
  rw [← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.toMatrix_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hm
  rw [ContinuousLinearMap.adjoint_toLinearMap] at hm
  ext i
  have hi := congrFun hm i
  simpa only [C, ContinuousLinearMap.coe_coe, Matrix.mulVec, dotProduct,
      OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using hi.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.adjoint_apply_eq_mulVec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.adjoint_apply_eq_mulVec target :: scope.openDecls } }

private theorem ae_hasWeakGrad_comp_affineEquiv
    {T : Type*} [MeasurableSpace T] {μ : _root_.MeasureTheory.Measure T}
    {d m : ℕ} (e : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {U : T × EuclideanSpace ℝ (Fin m) → ℝ}
    {G : T × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hU : _root_.MeasureTheory.MemLp U p (μ.prod (volume.restrict Ω)))
    (hG : _root_.MeasureTheory.MemLp G p (μ.prod (volume.restrict Ω)))
    (hw : ∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => G (t, z)) (fun z => U (t, z)) Ω) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad
      (fun z => e.toContinuousAffineMap.contLinear.adjoint (G (t, e z)))
      (fun z => U (t, e z)) (e ⁻¹' Ω) := by
  have hUs : ∀ᵐ t ∂μ, _root_.MeasureTheory.MemLp (fun z => U (t, z)) p (volume.restrict Ω) := by
    by_cases hpt : p = ⊤
    · subst p
      exact hU.prodMk_left_top
    · exact hU.prodMk_left hpt
  have hGs : ∀ᵐ t ∂μ, _root_.MeasureTheory.MemLp (fun z => G (t, z)) p (volume.restrict Ω) := by
    by_cases hpt : p = ⊤
    · subst p
      exact hG.prodMk_left_top
    · exact hG.prodMk_left hpt
  filter_upwards [hUs, hGs, hw] with t htU htG htw
  exact htw.comp_affineEquiv e
    (_root_.MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict (htU.locallyIntegrable hp))
    (_root_.MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict (htG.locallyIntegrable hp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.ae_hasWeakGrad_comp_affineEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.ae_hasWeakGrad_comp_affineEquiv target :: scope.openDecls } }

private theorem memLp_comp_spatial_affineEquiv
    {d m : ℕ} (e : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    {B : Type*} [TopologicalSpace B] [ContinuousENorm B]
    {J : Set ℝ} {Ω : Set (EuclideanSpace ℝ (Fin m))} {p : ℝ≥0∞}
    {U : ℝ × EuclideanSpace ℝ (Fin m) → B}
    (hU : _root_.MeasureTheory.MemLp U p ((volume.restrict J).prod (volume.restrict Ω))) :
    _root_.MeasureTheory.MemLp (fun q => U (q.1, e q.2)) p
      ((volume.restrict J).prod (volume.restrict (e ⁻¹' Ω))) := by
  rw [Measure.prod_restrict] at hU ⊢
  exact hU.comp_affineEquiv ((ContinuousAffineEquiv.refl ℝ ℝ).prodCongr e)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.memLp_comp_spatial_affineEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.memLp_comp_spatial_affineEquiv target :: scope.openDecls } }

private theorem exists_affineEquiv_closedBall_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω) :
    ∃ e : E ≃ᴬ[ℝ] E, e 0 = x ∧ e '' Metric.closedBall 0 1 ⊆ Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  let L : E ≃L[ℝ] E := Units.mk0 r hr.ne' • ContinuousLinearEquiv.refl ℝ E
  let e := L.toContinuousAffineEquiv.trans (ContinuousAffineEquiv.constVAdd ℝ E x)
  refine ⟨e, ?_, ?_⟩
  · change x + (r • (0 : E)) = x
    simp only [smul_zero, add_zero]
  · rintro y ⟨z, hz, rfl⟩
    apply hball
    change _root_.Dist.dist (x + r • z) x ≤ r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_affineEquiv_closedBall_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.exists_affineEquiv_closedBall_subset target :: scope.openDecls } }

private theorem exists_local_contDiffOn_ae_eq_of_raw_metric_equation
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric (𝓡∂ n) M}
    (hG : MetricFamilySmoothOn D g)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) ''
      interior (extChartAt (𝓡∂ n) α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) :
    let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))
    let μ := volume.restrict (_root_.Set.Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × E => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × E => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    ∀ (U : ℝ × E → ℝ) (K : ℝ × E → E), _root_.MeasureTheory.MemLp U 2 ν → _root_.MeasureTheory.MemLp K 2 ν →
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => K (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          ∑ j, ∫ p, ((A p).transpose *ᵥ (fun i => K p i)) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      ∃ u : ℝ × E → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (_root_.Set.Ioo c d ×ˢ Ω₀) ∧
        U =ᵐ[(volume.restrict (_root_.Set.Ioo c d)).prod (volume.restrict Ω₀)] u := by
  intro E μ ν ρ A U K hU hK hKw hw
  let V := hU.toLp U
  have hKm (i) : _root_.MeasureTheory.MemLp (fun p => K p i) 2 ν := hK.eval_piLp i
  let P := fun i => (hKm i).toLp (fun p => K p i)
  have hV : V =ᵐ[ν] U := hU.coeFn_toLp
  have hP (i) : P i =ᵐ[ν] (fun p => K p i) := (hKm i).coeFn_toLp
  have hPw (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => P i (t, z)) (fun z => V (t, z)) Ω := by
    filter_upwards [hKw, Measure.ae_ae_of_ae_prod hV,
      Measure.ae_ae_of_ae_prod (hP i)] with t ht hu hk
    exact (ht i).congr_ae (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hk)
  let G : MetricConnectionFamilyOn (I := 𝓡∂ n) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hAc (i j) : ContinuousOn (fun p => A p i j) (_root_.Set.Icc a b ×ˢ Ω) :=
    ((weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j).mono
      (_root_.Set.prod_mono hreg (subset_closure.trans hΩs))).continuousOn
  have hAK (i j) : _root_.MeasureTheory.LocallyIntegrableOn (fun p => A p i j * K p i)
      (_root_.Set.Icc a b ×ˢ Ω) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
    have hk := (hKm i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [show ν = (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict (_root_.Set.Icc a b ×ˢ Ω) from Measure.prod_restrict _ _] at hk
    exact (_root_.MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict hk).continuousOn_mul
      (hAc i j) ((isClosed_Icc.preimage continuous_fst).isLocallyClosed.inter
        (hΩ.preimage continuous_snd).isLocallyClosed)
  have hw' (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω) :
      (∫ p, ρ p * V p * fderiv ℝ φ p (1, 0) ∂ν) =
        ∑ i, ∑ j, ∫ p, A p i j * P i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
    have hint (i j) : _root_.MeasureTheory.Integrable (fun p => A p i j * K p i *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν := by
      rw [show ν = (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict (_root_.Set.Icc a b ×ˢ Ω) from Measure.prod_restrict _ _]
      exact ((hAK i j).integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans
          (hφs.trans (Set.prod_mono _root_.Set.Ioo_subset_Icc_self Subset.rfl)))).mono_measure Measure.restrict_le_self
    calc
      _ = ∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [hV] with p hp
        rw [hp]
      _ = _ := hw φ hφ hφc hφs
      _ = ∑ j, ∑ i, ∫ p, A p i j * K p i *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
        exact _root_.MeasureTheory.integral_finsetSum _ (fun i _ => hint i j)
      _ = ∑ i, ∑ j, ∫ p, A p i j * K p i *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [hP i] with p hp
        rw [hp]
  obtain ⟨u, hu, hVu⟩ := exists_local_contDiffOn_ae_eq_of_homogeneous_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd V P hPw hw'
  have hμ₀ : μ.restrict (_root_.Set.Icc c d) = volume.restrict (_root_.Set.Ioo c d) := by
    change (volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d) = volume.restrict (_root_.Set.Ioo c d)
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (_root_.Set.Icc_subset_Icc hac.le hdb.le)]
    exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hmeasure : (μ.restrict (_root_.Set.Icc c d)).prod (volume.restrict Ω₀) ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self
      (Measure.restrict_mono (subset_closure.trans hΩ₀Ω) le_rfl)
  refine ⟨u, hu, ?_⟩
  rw [← hμ₀]
  exact (hV.filter_mono (_root_.MeasureTheory.ae_mono hmeasure)).symm.trans hVu

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_local_contDiffOn_ae_eq_of_raw_metric_equation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.exists_local_contDiffOn_ae_eq_of_raw_metric_equation target :: scope.openDecls } }

private theorem contDiffAt_of_affine_ae_eq
    {d : ℕ} (s : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin d))
    {J : Set ℝ} {Ω W : Set (EuclideanSpace ℝ (Fin d))} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {U u : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : ContinuousOn U (J ×ˢ W)) (hs : s '' Ω ⊆ W)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (J ×ˢ Ω))
    (heq : (fun p => U (p.1, s p.2)) =ᵐ[(volume.restrict J).prod (volume.restrict Ω)] u)
    {t : ℝ} {z : EuclideanSpace ℝ (Fin d)} (ht : t ∈ J) (hz : z ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) U (t, s z) := by
  have hc : ContinuousOn (fun p => U (p.1, s p.2)) (J ×ˢ Ω) :=
    hU.comp (continuous_fst.prodMk (s.continuous.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, hs (_root_.Set.mem_image_of_mem s hp.2)⟩)
  rw [Measure.prod_restrict] at heq
  have he := Measure.eqOn_open_of_ae_eq heq (hJ.prod hΩ) hc hu.continuousOn
  have hu' := hu.congr he
  have hsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (p.1, s.symm p.2)) :=
    contDiff_fst.prodMk (s.symm.toContinuousAffineMap.contDiff.comp contDiff_snd)
  have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => U (p.1, s p.2)) (t, z) :=
    hu'.contDiffAt ((hJ.prod hΩ).mem_nhds ⟨ht, hz⟩)
  have hat' : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => U (p.1, s p.2)) (t, s.symm (s z)) := by
    simpa only [s.symm_apply_apply] using hat
  simpa only [Function.comp_def, s.apply_symm_apply] using hat'.comp (t, s z) hsm.contDiffAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffAt_of_affine_ae_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.contDiffAt_of_affine_ae_eq target :: scope.openDecls } }

section

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)))))
local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell ``Submission.DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell ``Submission.DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell

private theorem chartModelBasis_repr_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x : E) (i : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr x i = toEuclidean x i := by
  rw [chartModelBasis, Module.Basis.map_repr]
  change (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.repr (toEuclidean x) i = _
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.chartModelBasis_repr_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.chartModelBasis_repr_apply target :: scope.openDecls } }

private def closedCellCoordinateEquiv
    (e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    EuStd ≃ᴬ[ℝ] EuStd := by
  let L : EuN ≃L[ℝ] EuStd := toEuclidean
  let t : EuN ≃ᴬ[ℝ] EuN := ContinuousAffineEquiv.constVAdd ℝ EuN
    (-EuclideanSpace.single (0 : Fin (m + 1)) 1)
  exact L.symm.toContinuousAffineEquiv.trans (t.trans (e.trans L.toContinuousAffineEquiv))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.closedCellCoordinateEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.closedCellCoordinateEquiv target :: scope.openDecls } }

private theorem closedCell_coordinate_affine_matrix
    (e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    let L : EuN ≃L[ℝ] EuStd := toEuclidean
    let s := closedCellCoordinateEquiv e
    (∀ z : EuStd, s z = L (e (closedCellShiftSucc m (-1) (L.symm z)))) ∧
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ EuN)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ EuN)) ℝ).toBasis s.toAffineEquiv.linear.toLinearMap =
      LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis EuN) e.toAffineEquiv.linear.toLinearMap := by
  intro L s
  constructor
  · intro z
    change L (e (-EuclideanSpace.single (0 : Fin (m + 1)) 1 + L.symm z)) = _
    rw [closedCellShiftSucc_eq_add]
    simp only [EuclideanSpace.basisFun_apply, neg_one_smul, add_comm]
  · ext i j
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, chartModelBasis_repr_apply, chartModelBasis_apply,
      LinearEquiv.coe_coe]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.closedCell_coordinate_affine_matrix
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.closedCell_coordinate_affine_matrix target :: scope.openDecls } }

section

variable {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem weak_metric_divergence_comp_closedCell_chart
    (g : ℝ → SmoothRiemannianMetric I M) (α : M) (e : EuN ≃ᴬ[ℝ] EuN)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {J : Set ℝ} {Ω : Set EuStd} :
    let L : EuN ≃L[ℝ] EuStd := toEuclidean
    let f := fun z => L (e (closedCellShiftSucc m (-1) (L.symm z)))
    let C := LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis EuN)
      e.toAffineEquiv.linear.toLinearMap
    let h : ℝ → SmoothRiemannianMetric (𝓡∂ (m + 1)) (ClosedCell (m + 1)) :=
      fun t : ℝ => (g t).pullback (I := 𝓡∂ (m + 1)) (J := I) (M := ClosedCell (m + 1)) (N := M)
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    let A' := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (h p.1) β i j p.2
    (∀ z ∈ f ⁻¹' Ω, L.symm z ∈ (extChartAt (𝓡∂ (m + 1)) β).target) →
    ∀ (U R : ℝ × EuStd → ℝ) (K : ℝ × EuStd → Fin (Module.finrank ℝ EuN) → ℝ),
      (∀ j, _root_.MeasureTheory.LocallyIntegrableOn (fun p => ((A p).transpose *ᵥ K p) j) (J ×ˢ Ω)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuStd))) →
      (∀ φ : ℝ × EuStd → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
        (∫ p in J ×ˢ Ω, ρ p * U p * fderiv ℝ φ p (1, 0) ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) =
          (∑ j, ∫ p in J ×ˢ Ω, ((A p).transpose *ᵥ K p) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) -
          ∫ p in J ×ˢ Ω, R p * φ p ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) →
      let K' := fun p : ℝ × EuStd => C.transpose *ᵥ K (p.1, f p.2)
      ∀ φ : ℝ × EuStd → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ (f ⁻¹' Ω) →
        (∫ p in J ×ˢ (f ⁻¹' Ω), densityOnEuclid (h p.1) β p.2 * U (p.1, f p.2) *
          fderiv ℝ φ p (1, 0) ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) =
          (∑ j, ∫ p in J ×ˢ (f ⁻¹' Ω), ((A' p).transpose *ᵥ K' p) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) -
          ∫ p in J ×ˢ (f ⁻¹' Ω), |e.toAffineEquiv.linear.toLinearMap.det| *
            R (p.1, f p.2) * φ p ∂volume.prod volume := by
  intro L f C h ρ A A' hΩ U R K hV hweak K' φ hφ hφc hφs
  let s := closedCellCoordinateEquiv e
  obtain ⟨hs, hC⟩ := closedCell_coordinate_affine_matrix e
  have hsfun : (s : EuStd → EuStd) = f := funext hs
  have hdet : s.toAffineEquiv.linear.toLinearMap.det = e.toAffineEquiv.linear.toLinearMap.det := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ EuN)) ℝ).toBasis]
    rw [hC, LinearMap.det_toMatrix]
  have hw := weighted_divergence_comp_spatial_affineEquiv s (ρ := ρ) (U := U) (R := R)
    (K := K) (A := A) hV hweak φ hφ hφc (hsfun.symm ▸ hφs)
  dsimp only at hw
  rw [hC, hdet] at hw
  simp only [hsfun] at hw
  have hρ (p : ℝ × EuStd) (hp : p.2 ∈ f ⁻¹' Ω) :
      densityOnEuclid (h p.1) β p.2 =
        |e.toAffineEquiv.linear.toLinearMap.det| * ρ (p.1, f p.2) := by
    have hh := densityOnEuclid_closedCell_chart_pullback_eq_abs_det_mul
      (g p.1) α e he hβ (hΩ p.2 hp)
    simpa only [L, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hA (p : ℝ × EuStd) (hp : p.2 ∈ f ⁻¹' Ω) :
      A' p = |e.toAffineEquiv.linear.toLinearMap.det| • (C⁻¹ * A (p.1, f p.2) * C⁻¹.transpose) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hh := weightedInvGramOnEuclid_closedCell_chart_pullback_eq_congruence
      (g p.1) α e he hβ (hΩ p.2 hp) i j
    simpa only [L, C, A, A', f, Matrix.of_apply, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hz (p : ℝ × EuStd) (hp : p.2 ∉ f ⁻¹' Ω) (v : ℝ × EuStd) : fderiv ℝ φ p v = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x v)
    intro ht
    exact hp (hφs (tsupport_fderiv_apply_subset ℝ v ht)).2
  calc
    _ = ∫ p in J ×ˢ (f ⁻¹' Ω), (|e.toAffineEquiv.linear.toLinearMap.det| * ρ (p.1, f p.2)) *
        U (p.1, f p.2) * fderiv ℝ φ p (1, 0) ∂volume.prod volume := by
      apply _root_.MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp only
        by_cases hp : p.2 ∈ f ⁻¹' Ω
        · rw [hρ p hp]
        · rw [hz p hp, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
    _ = _ := by
      rw [hw]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply _root_.MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp only
        by_cases hp : p.2 ∈ f ⁻¹' Ω
        · rw [hA p hp]
        · rw [hz p hp, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.weak_metric_divergence_comp_closedCell_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.weak_metric_divergence_comp_closedCell_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.weak_metric_divergence_comp_closedCell_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.weak_metric_divergence_comp_closedCell_chart

end

private theorem exists_local_contDiffOn_ae_eq_on_closedCell
    {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g)
    (α : M) (e : EuN ≃ᴬ[ℝ] EuN)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ (toEuclidean : EuN ≃L[ℝ] EuStd) '' interior (extChartAt (𝓡∂ (m + 1)) β).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) :
    let s := closedCellCoordinateEquiv e
    let μ := volume.restrict (_root_.Set.Icc a b)
    let ν := μ.prod (volume.restrict (s '' Ω))
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    ∀ (U : ℝ × EuStd → ℝ) (K : ℝ × EuStd → EuStd), _root_.MeasureTheory.MemLp U 2 ν → _root_.MeasureTheory.MemLp K 2 ν →
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => K (t, z)) (fun z => U (t, z)) (s '' Ω)) →
      (∀ j, _root_.MeasureTheory.LocallyIntegrableOn (fun p => ((A p).transpose *ᵥ (fun i => K p i)) j)
        (_root_.Set.Ioo a b ×ˢ (s '' Ω)) (volume.prod _root_.MeasureTheory.MeasureSpace.volume)) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ (s '' Ω) →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          ∑ j, ∫ p, ((A p).transpose *ᵥ (fun i => K p i)) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      ∃ u : ℝ × EuStd → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (_root_.Set.Ioo c d ×ˢ Ω₀) ∧
        (fun p => U (p.1, s p.2)) =ᵐ[(volume.restrict (_root_.Set.Ioo c d)).prod (volume.restrict Ω₀)] u := by
  intro s μ ν ρ A U K hU hK hKw hV hw
  have hcell : IsCompact {x : EuN | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using _root_.ProperSpace.isCompact_closedBall (0 : EuN) 1
  let : CompactSpace (ClosedCell (m + 1)) := isCompact_iff_compactSpace.mp hcell
  let h : ℝ → SmoothRiemannianMetric (𝓡∂ (m + 1)) (ClosedCell (m + 1)) :=
    fun t => (g t).pullback (I := 𝓡∂ (m + 1)) (J := I)
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
  have hh : MetricFamilySmoothOn D h := hG.of_pullback h
    (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
    (contMDiff_extChartAt_symm_comp_affine_closedCell α e he) (fun _ _ _ _ => rfl)
  have hpre : s ⁻¹' (s '' Ω) = Ω := s.injective.preimage_image Ω
  let U' := fun p : ℝ × EuStd => U (p.1, s p.2)
  let K' := fun p : ℝ × EuStd => s.toContinuousAffineMap.contLinear.adjoint (K (p.1, s p.2))
  have hU' : _root_.MeasureTheory.MemLp U' 2 (μ.prod (volume.restrict Ω)) := by
    have hu := memLp_comp_spatial_affineEquiv s hU
    rwa [hpre] at hu
  have hK' : _root_.MeasureTheory.MemLp K' 2 (μ.prod (volume.restrict Ω)) := by
    have hk := (memLp_comp_spatial_affineEquiv s hK).continuousLinearMap_comp
      s.toContinuousAffineMap.contLinear.adjoint
    rwa [hpre] at hk
  have hKw' : ∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => K' (t, z)) (fun z => U' (t, z)) Ω := by
    have hk := ae_hasWeakGrad_comp_affineEquiv s (by norm_num : (1 : ℝ≥0∞) ≤ 2) hU hK hKw
    rwa [hpre] at hk
  let L : EuN ≃L[ℝ] EuStd := toEuclidean
  obtain ⟨hs, hC⟩ := closedCell_coordinate_affine_matrix e
  have hsfun : (fun z => L (e (closedCellShiftSucc m (-1) (L.symm z)))) = s := (funext hs).symm
  have hdomain : ∀ z ∈ s ⁻¹' (s '' Ω), L.symm z ∈ (extChartAt (𝓡∂ (m + 1)) β).target := by
    intro z hz
    rw [hpre] at hz
    obtain ⟨y, hy, rfl⟩ := hΩs (subset_closure hz)
    simpa only [L, ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  have hμ : μ = volume.restrict (_root_.Set.Ioo a b) := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hν : ν = (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict (_root_.Set.Ioo a b ×ˢ (s '' Ω)) := by
    rw [show ν = μ.prod (volume.restrict (s '' Ω)) from rfl, hμ, Measure.prod_restrict]
  have hw₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ (s '' Ω)) :
      (∫ p in _root_.Set.Ioo a b ×ˢ (s '' Ω), ρ p * U p * fderiv ℝ φ p (1, 0) ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) =
        (∑ j, ∫ p in _root_.Set.Ioo a b ×ˢ (s '' Ω), ((A p).transpose *ᵥ (fun i => K p i)) j *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume) -
        ∫ p in _root_.Set.Ioo a b ×ˢ (s '' Ω), (0 : ℝ) * φ p ∂volume.prod volume := by
    simpa only [_root_.MulZeroClass.zero_mul, _root_.MeasureTheory.integral_zero, sub_zero, hν] using hw φ hφ hφc hφs
  have htransport := weak_metric_divergence_comp_closedCell_chart g α e he hβ
    (J := _root_.Set.Ioo a b) (Ω := s '' Ω)
  dsimp only at htransport
  rw [hsfun] at htransport
  have hweak := htransport hdomain U (fun _ => 0) (fun p i => K p i) hV hw₀
  have hw' (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω) :
      (∫ p, densityOnEuclid (h p.1) β p.2 * U' p * fderiv ℝ φ p (1, 0)
        ∂μ.prod (volume.restrict Ω)) =
        ∑ j, ∫ p, ((Matrix.of fun i j => weightedInvGramOnEuclid (h p.1) β i j p.2).transpose *ᵥ
          (fun i => K' p i)) j * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂μ.prod (volume.restrict Ω) := by
    have hk (p : ℝ × EuStd) : (fun i => K' p i) =
        (LinearMap.toMatrix (DifferentialGeometry.Tensor.Coordinates.chartModelBasis EuN)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis EuN)
          e.toAffineEquiv.linear.toLinearMap).transpose *ᵥ (fun i => K (p.1, s p.2) i) := by
      have hk := adjoint_apply_eq_mulVec s.toContinuousAffineMap.contLinear (K (p.1, s p.2))
      dsimp only at hk
      rw [show s.toContinuousAffineMap.contLinear.toLinearMap = s.toAffineEquiv.linear.toLinearMap from rfl,
        hC] at hk
      exact hk
    rw [hμ, Measure.prod_restrict]
    have htest := hweak φ hφ hφc (hpre.symm ▸ hφs)
    simp only [hpre, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, _root_.MeasureTheory.integral_zero, sub_zero, ← hs] at htest
    simp only [hk]
    exact htest
  exact exists_local_contDiffOn_ae_eq_of_raw_metric_equation hh hab hreg β hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω hac hdb hcd U' K' hU' hK' hKw' hw'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_local_contDiffOn_ae_eq_on_closedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.exists_local_contDiffOn_ae_eq_on_closedCell target :: scope.openDecls } }

private theorem contDiffOn_of_metric_equation_succ
    {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g)
    {a b : ℝ} (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ (toEuclidean : EuN ≃L[ℝ] EuStd) '' interior (extChartAt I α).target) :
    let μ := volume.restrict (_root_.Set.Ioo a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    ∀ (U : ℝ × EuStd → ℝ) (K : ℝ × EuStd → EuStd),
      ContinuousOn U (_root_.Set.Ioo a b ×ˢ Ω) →
      (∀ B : Set (ℝ × EuStd), IsCompact B → B ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        _root_.MeasureTheory.MemLp K 2 ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B)) →
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => K (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          ∑ j, ∫ p, ((A p).transpose *ᵥ (fun i => K p i)) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      ContDiffOn ℝ (⊤ : ℕ∞) U (_root_.Set.Ioo a b ×ˢ Ω) := by
  intro μ ν ρ A U K hUc hK hKw hw p hp
  classical
  obtain ⟨a₁, haa₁, ha₁t⟩ := exists_between hp.1.1
  obtain ⟨b₁, htb₁, hb₁b⟩ := exists_between hp.1.2
  obtain ⟨c, ha₁c, hct⟩ := exists_between ha₁t
  obtain ⟨d, htd, hdb₁⟩ := exists_between htb₁
  have htime : _root_.Set.Icc a₁ b₁ ⊆ _root_.Set.Ioo a b := fun t ht => ⟨haa₁.trans_le ht.1, ht.2.trans_lt hb₁b⟩
  let L : EuN ≃L[ℝ] EuStd := toEuclidean
  have hx : L.symm p.2 ∈ interior (extChartAt I α).target := by
    obtain ⟨y, hy, heq⟩ := hΩs hp.2
    rw [← heq]
    simpa only [L, ContinuousLinearEquiv.symm_apply_apply] using hy
  obtain ⟨e, he0, heball⟩ := exists_affineEquiv_closedBall_subset isOpen_interior hx
  have he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target := by
    intro x
    apply heball
    exact ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property, rfl⟩
  let β : ClosedCell (m + 1) := closedCellCenter (m + 1)
  have hβ : ‖β.val‖ < 1 := by simp [β, closedCellCenter]
  let s := closedCellCoordinateEquiv e
  let z : EuStd := L (closedCellShiftSucc m 1 (0 : EuN))
  have hsz : s z = p.2 := by
    rw [(closedCell_coordinate_affine_matrix e).1 z]
    change L (e (closedCellShiftSucc m (-1) (L.symm (L (closedCellShiftSucc m 1 0))))) = _
    rw [L.symm_apply_apply, closedCellShiftSucc_neg_left_inv, he0, L.apply_symm_apply]
  let W := L '' interior (extChartAt (𝓡∂ (m + 1)) β).target
  have hW : IsOpen W := L.toHomeomorph.isOpenMap _ isOpen_interior
  have hzW : z ∈ W := by
    refine ⟨closedCellShiftSucc m 1 0, ?_, rfl⟩
    rw [extChartAt_closedCell_target hβ]
    have hopen : IsOpen {y : EuN | ‖closedCellShiftSucc m (-1) y‖ < 1} :=
      isOpen_lt (continuous_norm.comp (closedCellShiftSucc_contDiff (-1)).continuous) continuous_const
    rw [hopen.interior_eq]
    simp only [_root_.Set.mem_ofPred_eq, closedCellShiftSucc_neg_left_inv, norm_zero, zero_lt_one]
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hW.inter (hΩ.preimage s.continuous)).mem_nhds ⟨hzW, by simpa only [_root_.Set.mem_preimage, hsz] using hp.2⟩)
  let V := Metric.ball z r
  let V₀ := Metric.ball z (r / 2)
  have hVc : IsCompact (closure V) := (_root_.ProperSpace.isCompact_closedBall z r).of_isClosed_subset isClosed_closure
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  have hVs : closure V ⊆ W := (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
    (fun x hx => (hball hx).1)
  have hVΩ : s '' V ⊆ Ω := by
    rintro y ⟨x, hx, rfl⟩
    exact (hball (Metric.ball_subset_closedBall hx)).2
  have hV₀V : closure V₀ ⊆ V :=
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by linarith : r / 2 < r))
  have hVopen : IsOpen (s '' V) := s.toHomeomorph.isOpenMap _ Metric.isOpen_ball
  let ν₁ := (volume.restrict (_root_.Set.Icc a₁ b₁)).prod (volume.restrict (s '' V))
  let B := _root_.Set.Icc a₁ b₁ ×ˢ (s '' closure V)
  have hBc : IsCompact B := isCompact_Icc.prod (hVc.image s.continuous)
  have hBsub : B ⊆ _root_.Set.Ioo a b ×ˢ Ω := _root_.Set.prod_mono htime (by
    rintro y ⟨x, hx, rfl⟩
    exact (hball ((closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall) hx)).2)
  have hν₁ : ν₁ ≤ (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B := by
    rw [show ν₁ = (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict (_root_.Set.Icc a₁ b₁ ×ˢ (s '' V)) from Measure.prod_restrict _ _]
    exact Measure.restrict_mono (Set.prod_mono Subset.rfl (_root_.Set.image_mono subset_closure)) le_rfl
  let : _root_.MeasureTheory.IsFiniteMeasure ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B) :=
    isFiniteMeasure_restrict.mpr hBc.measure_lt_top.ne
  have hUm : _root_.MeasureTheory.MemLp U 2 ν₁ :=
    (((hUc.mono hBsub).memLp_top_of_isCompact hBc hBc.measurableSet).mono_exponent le_top).mono_measure hν₁
  have hKm : _root_.MeasureTheory.MemLp K 2 ν₁ := (hK B hBc hBsub).mono_measure hν₁
  have hKw₁ : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a₁ b₁),
      DeGiorgi.HasWeakGrad (fun z => K (t, z)) (fun z => U (t, z)) (s '' V) := by
    filter_upwards [hKw.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono htime le_rfl))] with t ht
    exact fun i => (ht i).restrict hVopen hVΩ
  let G : MetricConnectionFamilyOn (I := I) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hAc (i j) : ContinuousOn (fun p => A p i j) (_root_.Set.Ioo a b ×ˢ Ω) :=
    ((weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j).mono
      (_root_.Set.prod_mono hreg hΩs)).continuousOn
  have hAK (i j) : _root_.MeasureTheory.LocallyIntegrableOn (fun p => A p i j * K p i)
      (_root_.Set.Ioo a b ×ˢ Ω) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
    apply (_root_.MeasureTheory.locallyIntegrableOn_iff (isOpen_Ioo.prod hΩ).isLocallyClosed).mpr
    intro C hC hCc
    let : _root_.MeasureTheory.IsFiniteMeasure ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict C) :=
      isFiniteMeasure_restrict.mpr hCc.measure_lt_top.ne
    exact IntegrableOn.continuousOn_mul ((hAc i j).mono hC)
      (((hK C hCc hC).eval_piLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hCc
  have hflux (j) : _root_.MeasureTheory.LocallyIntegrableOn (fun p => ((A p).transpose *ᵥ (fun i => K p i)) j)
      (_root_.Set.Ioo a₁ b₁ ×ˢ (s '' V)) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
    have hsum (F : Finset (Fin (Module.finrank ℝ EuN))) :
        LocallyIntegrableOn (fun p => ∑ i ∈ F, A p i j * K p i) (_root_.Set.Ioo a b ×ˢ Ω) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
      apply (_root_.MeasureTheory.locallyIntegrableOn_iff (isOpen_Ioo.prod hΩ).isLocallyClosed).mpr
      intro B hB hBc
      exact _root_.MeasureTheory.integrable_finsetSum F (fun i _ => (hAK i j).integrableOn_compact_subset hB hBc)
    exact (hsum Finset.univ).mono_set
      (_root_.Set.prod_mono (fun t ht => ⟨haa₁.trans ht.1, ht.2.trans hb₁b⟩) hVΩ)
  have hw₁ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ _root_.Set.Ioo a₁ b₁ ×ˢ (s '' V)) :
      (∫ q, ρ q * U q * fderiv ℝ φ q (1, 0) ∂ν₁) =
        ∑ j, ∫ q, ((A q).transpose *ᵥ (fun i => K q i)) j *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν₁ := by
    have hμ₁ : μ.restrict (_root_.Set.Icc a₁ b₁) = volume.restrict (_root_.Set.Icc a₁ b₁) := by
      rw [show μ = volume.restrict (_root_.Set.Ioo a b) from rfl,
        Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr htime]
    have hint (B : ℝ × EuStd → ℝ) (v : ℝ × EuStd) :
        (∫ q, B q * fderiv ℝ φ q v ∂ν) = ∫ q, B q * fderiv ℝ φ q v ∂ν₁ := by
      have hh := integral_eq_integral_restrict_prod_of_support_subset (μ := μ) (ν := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuStd))
        hVopen.measurableSet hVΩ (s := _root_.Set.Icc a₁ b₁)
        (f := fun q => B q * fderiv ℝ φ q v) (fun q hq => by
          rw [image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q v)
            (fun hs => hq ((Set.prod_mono _root_.Set.Ioo_subset_Icc_self Subset.rfl)
              (hφs (tsupport_fderiv_apply_subset ℝ v hs)))), _root_.MulZeroClass.mul_zero])
      rwa [hμ₁] at hh
    have hh := hw φ hφ hφc (hφs.trans
      (_root_.Set.prod_mono (fun t ht => ⟨haa₁.trans ht.1, ht.2.trans hb₁b⟩) hVΩ))
    simpa only [hint] using hh
  obtain ⟨u, hu, heq⟩ := exists_local_contDiffOn_ae_eq_on_closedCell hG α e he hβ
    (ha₁t.trans htb₁) (htime.trans hreg) (Ω := V) Metric.isOpen_ball hVc hVs
    (Ω₀ := V₀) Metric.isOpen_ball hV₀V ha₁c hdb₁ (hct.trans htd)
    U K hUm hKm hKw₁ hflux hw₁
  have hat := contDiffAt_of_affine_ae_eq s isOpen_Ioo Metric.isOpen_ball
    (hUc.mono (_root_.Set.prod_mono (fun t ht => ⟨haa₁.trans (ha₁c.trans ht.1), (ht.2.trans hdb₁).trans hb₁b⟩)
      Subset.rfl)) ((_root_.Set.image_mono (subset_closure.trans hV₀V)).trans hVΩ) hu heq
      (t := p.1) (z := z) ⟨hct, htd⟩ (Metric.mem_ball_self (by linarith : 0 < r / 2))
  rw [hsz] at hat
  exact hat.contDiffWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_metric_equation_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_metric_equation_succ target :: scope.openDecls } }

end

section

variable {n : ℕ} [NeZero n]
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))

theorem contDiffOn_of_homogeneous_metric_divergence_equation
    {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g)
    {a b : ℝ} (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ (toEuclidean : EuN ≃L[ℝ] EuStd) '' interior (extChartAt I α).target) :
    let μ := volume.restrict (_root_.Set.Ioo a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    ∀ (U : ℝ × EuStd → ℝ) (K : ℝ × EuStd → EuStd),
      ContinuousOn U (_root_.Set.Ioo a b ×ˢ Ω) →
      (∀ B : Set (ℝ × EuStd), IsCompact B → B ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        _root_.MeasureTheory.MemLp K 2 ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B)) →
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => K (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          ∑ j, ∫ p, ((A p).transpose *ᵥ (fun i => K p i)) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      ContDiffOn ℝ (⊤ : ℕ∞) U (_root_.Set.Ioo a b ×ˢ Ω) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact contDiffOn_of_metric_equation_succ hG hreg α hΩ hΩs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_homogeneous_metric_divergence_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_homogeneous_metric_divergence_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_homogeneous_metric_divergence_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_homogeneous_metric_divergence_equation


theorem metric_divergence_eq_of_homogeneous_weak_equation
    {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g)
    {a b : ℝ} (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ (toEuclidean : EuN ≃L[ℝ] EuStd) '' interior (extChartAt I α).target) :
    let μ := volume.restrict (_root_.Set.Ioo a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    ∀ (U : ℝ × EuStd → ℝ) (K : ℝ × EuStd → EuStd),
      ContinuousOn U (_root_.Set.Ioo a b ×ˢ Ω) →
      (∀ B : Set (ℝ × EuStd), IsCompact B → B ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        _root_.MeasureTheory.MemLp K 2 ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B)) →
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun z => K (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          ∑ j, ∫ p, ((A p).transpose *ᵥ (fun i => K p i)) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      ∀ p ∈ _root_.Set.Ioo a b ×ˢ Ω, fderiv ℝ (fun q => ρ q * U q) p (1, 0) =
        ∑ i, ∑ j, fderiv ℝ (fun q => A q i j * fderiv ℝ U q (0, EuclideanSpace.single i 1))
          p (0, EuclideanSpace.single j 1) := by
  intro μ ν ρ A U K hUc hK hKw hw
  have hu := contDiffOn_of_homogeneous_metric_divergence_equation hG hreg α hΩ hΩs U K hUc hK hKw hw
  have hKl (i) : _root_.MeasureTheory.LocallyIntegrableOn (fun p => K p i) (_root_.Set.Ioo a b ×ˢ Ω) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
    apply (_root_.MeasureTheory.locallyIntegrableOn_iff (isOpen_Ioo.prod hΩ).isLocallyClosed).mpr
    intro B hB hBc
    let : _root_.MeasureTheory.IsFiniteMeasure ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B) :=
      isFiniteMeasure_restrict.mpr hBc.measure_lt_top.ne
    exact ((hK B hBc hB).eval_piLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let G : MetricConnectionFamilyOn (I := I) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContDiffOn ℝ 1 ρ (_root_.Set.Ioo a b ×ˢ Ω) :=
    ((densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (_root_.Set.prod_mono hreg (hΩs.trans (_root_.Set.image_mono interior_subset)))).of_le (by simp)
  have hA (i j) : ContDiffOn ℝ 1 (fun p => A p i j) (_root_.Set.Ioo a b ×ˢ Ω) :=
    ((weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j).mono
      (_root_.Set.prod_mono hreg hΩs)).of_le (by simp)
  have hweak (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ i, ∑ j, ∫ p, A p i j * K p i * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, (0 : ℝ) * φ p ∂ν := by
    simp only [_root_.MulZeroClass.zero_mul, _root_.MeasureTheory.integral_zero, sub_zero]
    rw [hw φ hφ hφc hφs, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
    apply _root_.MeasureTheory.integral_finsetSum
    intro i _
    rw [show ν = (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict (_root_.Set.Ioo a b ×ˢ Ω) from Measure.prod_restrict _ _]
    have hAK := (hKl i).continuousOn_mul (hA i j).continuousOn (isOpen_Ioo.prod hΩ).isLocallyClosed
    exact (hAK.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hφs)).mono_measure
          Measure.restrict_le_self
  have h := weighted_divergence_eq_of_contDiffOn_ae_eq_of_locallyIntegrableOn isOpen_Ioo hΩ
    hKl (fun i => hKw.mono (fun _ ht => ht i))
    (hu.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) Filter.EventuallyEq.rfl hρ hA
    (continuousOn_const : ContinuousOn (fun _ => (0 : ℝ)) (_root_.Set.Ioo a b ×ˢ Ω)) hweak
  simpa only [add_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.metric_divergence_eq_of_homogeneous_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.metric_divergence_eq_of_homogeneous_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.metric_divergence_eq_of_homogeneous_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.metric_divergence_eq_of_homogeneous_weak_equation

theorem contDiffOn_and_metric_divergence_eq_of_locallyLipschitzOn
    {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g)
    {a b : ℝ} (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ (toEuclidean : EuN ≃L[ℝ] EuStd) '' interior (extChartAt I α).target) :
    let μ := volume.restrict (_root_.Set.Ioo a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    ∀ (U : ℝ × EuStd → ℝ),
      LocallyLipschitzOn (_root_.Set.Ioo a b ×ˢ Ω) U →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          ∑ j, ∫ p, ((A p).transpose *ᵥ
            (fun i => lineDeriv ℝ U p (0, EuclideanSpace.single i 1))) j *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      ContDiffOn ℝ (⊤ : ℕ∞) U (_root_.Set.Ioo a b ×ˢ Ω) ∧
        ∀ p ∈ _root_.Set.Ioo a b ×ˢ Ω, fderiv ℝ (fun q => ρ q * U q) p (1, 0) =
          ∑ i, ∑ j, fderiv ℝ (fun q => A q i j * fderiv ℝ U q (0, EuclideanSpace.single i 1))
            p (0, EuclideanSpace.single j 1) := by
  intro μ ν ρ A U hU hw
  let K : ℝ × EuStd → EuStd := fun p =>
    WithLp.toLp 2 (fun i => lineDeriv ℝ U p (0, EuclideanSpace.single i 1))
  have hK (B : Set (ℝ × EuStd)) (hB : IsCompact B) (hBs : B ⊆ _root_.Set.Ioo a b ×ˢ Ω) :
      MemLp K 2 ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict B) := by
    apply MemLp.of_eval_piLp
    intro i
    exact hU.memLp_lineDeriv_of_isCompact (isOpen_Ioo.prod hΩ) hB hBs hB.measure_lt_top.ne
      (0, EuclideanSpace.single i 1) 2
  have hKw : ∀ᵐ t ∂μ, DeGiorgi.HasWeakGrad (fun x => K (t, x)) (fun x => U (t, x)) Ω := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have h := Sobolev.Euclidean.hasWeakGrad_prodMk_left_of_locallyLipschitzOn hU ht
    simpa only [K, lineDeriv, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero] using h
  exact ⟨contDiffOn_of_homogeneous_metric_divergence_equation hG hreg α hΩ hΩs U K
    hU.continuousOn hK hKw hw,
    metric_divergence_eq_of_homogeneous_weak_equation hG hreg α hΩ hΩs U K
      hU.continuousOn hK hKw hw⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.contDiffOn_and_metric_divergence_eq_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.contDiffOn_and_metric_divergence_eq_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.contDiffOn_and_metric_divergence_eq_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_and_metric_divergence_eq_of_locallyLipschitzOn

end

end DifferentialGeometry.Analysis.Parabolic
