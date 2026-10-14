import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.PointwiseBounds.UniformChartCoefficients
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def chartRiemannEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartRiemannTensor (I := I) g α i j k l (toEuclidean.symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid ``Submission.DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRiemannEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartRiemannEuclid (I := I) g α i j k l y =
      chartRiemannTensor (I := I) g α i j k l (toEuclidean.symm y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_def ``Submission.DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_def

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma partialDeriv_contDiffOn_interior_of_contDiffOn
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior ((extChartAt I α).target : Set E)))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a f)
      (interior ((extChartAt I α).target : Set E)) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hrw : (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a f) =
      fun y => fderiv ℝ f y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a) := rfl
  rw [hrw]
  exact hfderiv.clm_apply contDiffOn_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.partialDeriv_contDiffOn_interior_of_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.partialDeriv_contDiffOn_interior_of_contDiffOn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      (interior ((extChartAt I α).target : Set E)) := by
  classical
  set U : Set E := interior ((extChartAt I α).target : Set E) with hU_def
  have hΓ : ∀ p q r : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α p q r) U :=
    fun p q r => chartChristoffel_contDiffOn_interior (I := I) g α p q r
  have hdΓ1 : ContDiffOn ℝ ∞
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hΓ i k l) j
  have hdΓ2 : ContDiffOn ℝ ∞
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hΓ i j l) k
  have hΓΓ : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l y *
            chartChristoffel (I := I) g α i k m y -
          chartChristoffel (I := I) g α k m l y *
            chartChristoffel (I := I) g α i j m y)) U := by
    refine ContDiffOn.sum (fun m _ => ?_)
    exact ((hΓ j m l).mul (hΓ i k m)).sub ((hΓ k m l).mul (hΓ i j m))
  have hrw : (chartRiemannTensor (I := I) g α i j k l) =
      fun y : E =>
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y) +
        (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) := by
    funext y; rw [chartRiemannTensor_def]
  rw [hrw]
  exact (hdΓ1.sub hdΓ2).add hΓΓ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartRiemannTensor_contDiffOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartRiemannTensor_contDiffOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartRiemannTensor_contDiffOn_interior ``Submission.DifferentialGeometry.Analysis.Elliptic.chartRiemannTensor_contDiffOn_interior

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannEuclid_contDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRiemannEuclid (I := I) g α i j k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE_int : ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      (interior ((extChartAt I α).target : Set E)) :=
    chartRiemannTensor_contDiffOn_interior (I := I) g α i j k l
  have htarget_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target (I := I) α
  have hE : ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      ((extChartAt I α).target) := by
    rw [show ((extChartAt I α).target : Set E) =
        interior ((extChartAt I α).target : Set E) from
      htarget_open.interior_eq.symm]
    exact hE_int
  have hcomp :
      ContDiffOn ℝ ∞
        (chartRiemannTensor (I := I) g α i j k l ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) hy
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Elliptic.chartRiemannEuclid_contDiffOn

theorem exists_chartRiemannData_uniform_bound_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ∀ (i j k l : Fin (Module.finrank ℝ E)),
          |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤ C := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set K_set : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_image_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouTsupport_image_subset_chartTargetEuclid (I := I) (M := M) α
  have h_each : ∀ q : (Fin n × Fin n) × (Fin n × Fin n), ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ K_set,
        |chartRiemannEuclid (I := I) g α q.1.1 q.1.2 q.2.1 q.2.2 y| ≤ C := by
    intro q
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (chartRiemannEuclid_contDiffOn (I := I) (M := M) g α q.1.1 q.1.2 q.2.1 q.2.2)
  choose C_fn hC_fn_nn hC_fn_bd using h_each
  set C : ℝ :=
    (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).sup'
      Finset.univ_nonempty C_fn with hC_def
  have hC_nn : 0 ≤ C := by
    rcases Finset.univ_nonempty
      (α := (Fin n × Fin n) × (Fin n × Fin n)) with ⟨q₀, _⟩
    exact (hC_fn_nn q₀).trans
      (Finset.le_sup'_of_le C_fn (Finset.mem_univ q₀) (le_refl _))
  refine ⟨C, hC_nn, ?_⟩
  intro b hb_inter i j k l
  have hb_tsupp : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb_inter.1
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hy_K : y ∈ K_set := ⟨b, hb_tsupp, rfl⟩
  have hval : chartRiemannEuclid (I := I) g α i j k l y =
      chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b) := by
    rw [chartRiemannEuclid_def, hy_def]
    congr 1
    exact toEuclidean.symm_apply_apply ((extChartAt I α) b)
  have hbd_q := hC_fn_bd ((i, j), (k, l)) y hy_K
  have hq_le : C_fn ((i, j), (k, l)) ≤ C :=
    Finset.le_sup'_of_le C_fn (Finset.mem_univ ((i, j), (k, l))) (le_refl _)
  calc |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)|
      = |chartRiemannEuclid (I := I) g α i j k l y| := by rw [hval]
    _ ≤ C_fn ((i, j), (k, l)) := hbd_q
    _ ≤ C := hq_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_pouTsupport ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_pouTsupport

theorem exists_chartRiemannData_uniform_bound_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C_g : ℝ, 0 ≤ C_g ∧
      ∀ {α : M}, α ∈ chartAtlasPOUFinset (I := I) (M := M) →
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          ∀ (i j k l : Fin (Module.finrank ℝ E)),
            |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤
              C_g := by
  classical
  have h_each : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ∀ (i j k l : Fin (Module.finrank ℝ E)),
          |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤ C :=
    fun α => exists_chartRiemannData_uniform_bound_pouTsupport (I := I) (M := M) g α
  choose C_fn hC_fn_nn hC_fn_bd using h_each
  set S : Finset M := chartAtlasPOUFinset (I := I) (M := M) with hS_def
  set C_g : ℝ := ∑ α ∈ S, C_fn α with hC_g_def
  have hC_g_nn : 0 ≤ C_g :=
    Finset.sum_nonneg (fun α _ => hC_fn_nn α)
  refine ⟨C_g, hC_g_nn, ?_⟩
  intro α hα b hb_inter i j k l
  have hbd : |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤
      C_fn α := hC_fn_bd α hb_inter i j k l
  have hα_S : α ∈ S := hα
  have h_le : C_fn α ≤ C_g := by
    rw [hC_g_def]
    exact Finset.single_le_sum (f := C_fn) (fun a _ => hC_fn_nn a) hα_S
  exact hbd.trans h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_compact ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_chartRiemannData_uniform_bound_compact

end Elliptic
end Analysis
end DifferentialGeometry

end
