import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.IteratedRegularityBootstrap
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapMixed
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapStep

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

section GenericRaiser

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem memWkp_succ_of_classicalPartial_memWkp
    (k : ℕ) {Ω : Set EE} (hΩ_open : IsOpen Ω)
    {u : EE → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_L2 : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (h_partial : ∀ l : Fin d,
      MemWkp (d := d) k 2
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single l 1)) Ω) :
    MemWkp (d := d) (k + 1) 2 u Ω := by
  classical
  rw [MemWkp_succ]
  have hu_W1 : DeGiorgi.MemW1p (d := d) 2 u Ω := by
    refine ⟨hu_L2, fun i => ?_⟩
    refine ⟨fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1), ?_, ?_⟩
    · exact (h_partial i).memLp
    · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ_open
        (hu_smooth.of_le (by norm_cast))
  refine ⟨hu_W1, fun i => ?_⟩
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hu_smooth hu_W1 i
  exact (MemWkp_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (h_partial i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_succ_of_classicalPartial_memWkp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_succ_of_classicalPartial_memWkp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_succ_of_classicalPartial_memWkp ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_succ_of_classicalPartial_memWkp

omit [NeZero d] in
theorem memWkp_of_iterClassicalPartial_memWkp_two
    (m : ℕ) {Ω : Set EE} (hΩ_open : IsOpen Ω)
    {u : EE → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_Wm : MemWkp (d := d) m 2 u Ω)
    (h_top : ∀ idx : Fin m → Fin d,
      MemWkp (d := d) 2 2 (iterClassicalPartial (d := d) m idx u) Ω) :
    MemWkp (d := d) (m + 2) 2 u Ω := by
  classical
  induction m generalizing u with
  | zero =>
      simpa [iterClassicalPartial_zero] using h_top (fun i : Fin 0 => i.elim0)
  | succ m ih =>
      have hu_L2 : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω) := hu_Wm.memLp
      have h_du : ∀ l : Fin d,
          MemWkp (d := d) (m + 2) 2
            (fun x => (fderiv ℝ u x) (EuclideanSpace.single l 1)) Ω := by
        intro l
        refine ih ?_ ?_ ?_
        · exact contDiff_partial_eta (d := d) hu_smooth l
        · exact classicalPartial_memWkp_of_memWkp_succ (d := d) hΩ_open
            hu_smooth hu_Wm l
        · intro idx
          have h_eq :
              iterClassicalPartial (d := d) m idx
                  (fun x => (fderiv ℝ u x) (EuclideanSpace.single l 1)) =
                iterClassicalPartial (d := d) (m + 1)
                  (Fin.cons l idx) u := by
            rw [iterClassicalPartial_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
          rw [h_eq]
          exact h_top (Fin.cons l idx)
      have h_raised : MemWkp (d := d) ((m + 2) + 1) 2 u Ω :=
        memWkp_succ_of_classicalPartial_memWkp (d := d) (m + 2) hΩ_open
          hu_smooth hu_L2 h_du
      have h_idx : (m + 2) + 1 = (m + 1) + 2 := by ring
      rwa [h_idx] at h_raised

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_of_iterClassicalPartial_memWkp_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_of_iterClassicalPartial_memWkp_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_of_iterClassicalPartial_memWkp_two ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.memWkp_of_iterClassicalPartial_memWkp_two

end GenericRaiser

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem iterClassicalPartial_memWkp_two_of_weakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_support : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (iterClassicalPartial (d := Module.finrank ℝ E) m idx
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)) Ω'' := by
  classical
  set B := tensorPrincipalForm (I := I) (M := M) g α hK hK_target with hB_def
  set u : EuclN → ℝ := tensorComponentEuclid (I := I) (M := M) g r s T α P₀
    with hu_def
  set RHS : EuclN → ℝ :=
    tensorComponentWeakRHS (I := I) (M := M) g r s T F α P₀
    with hRHS_def
  have h_weak_solution :
      B.IsSmoothWeakSolution
        (iterClassicalPartial (d := Module.finrank ℝ E) m idx u)
        (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx) :=
    tensorComponent_iterated_partial_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_support hF_support hT_K hweak m idx
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_support
  have hu_compact : HasCompactSupport u :=
    tensorComponentEuclid_hasCompactSupport (I := I) (M := M) g r s T α P₀ hT_support
  have hRHS_cd : ContDiff ℝ (⊤ : ℕ∞) RHS :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M) g r s T F α P₀
      hT_support hF_support
  have hRHS_compact : HasCompactSupport RHS :=
    tensorComponentWeakRHS_hasCompactSupport (I := I) (M := M) g r s T F α hK
      hK_target P₀ hT_support hF_support hT_K hweak
  have h_w_compact :
      HasCompactSupport (iterClassicalPartial (d := Module.finrank ℝ E) m idx u) :=
    hasCompactSupport_iterClassicalPartial (d := Module.finrank ℝ E) m idx hu_compact
  have h_s_cd : ContDiff ℝ (⊤ : ℕ∞)
      (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx) :=
    contDiff_iteratedPerturbedSource (d := Module.finrank ℝ E) B m hu_cd hRHS_cd idx
  have h_s_compact : HasCompactSupport
      (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx) := by
    have h_sub :
        tsupport (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx)
          ⊆ tsupport u ∪ tsupport RHS :=
      tsupport_iteratedPerturbedSource_subset (d := Module.finrank ℝ E) B m
        ((isClosed_tsupport u).union (isClosed_tsupport RHS))
        _root_.Set.subset_union_left _root_.Set.subset_union_right idx
    exact HasCompactSupport.of_support_subset_isCompact
      (hu_compact.union hRHS_compact)
      ((subset_tsupport _).trans h_sub)
  obtain ⟨C, _hC_nn, h_engine⟩ :=
    smooth_cc_h2_local_memWkp_two (d := Module.finrank ℝ E) B hΩ''_open
      hΩ''_compact_closure
  exact (h_engine h_weak_solution h_w_compact h_s_cd h_s_compact).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.iterClassicalPartial_memWkp_two_of_weakSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.iterClassicalPartial_memWkp_two_of_weakSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.iterClassicalPartial_memWkp_two_of_weakSolution ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.iterClassicalPartial_memWkp_two_of_weakSolution

omit [CompleteSpace E] in
theorem tensorComponent_memWkp_allOrders_interior
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_support : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (k : ℕ) :
    MemWkp (d := Module.finrank ℝ E) (2 * k + 2) 2
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' := by
  classical
  set u : EuclN → ℝ := tensorComponentEuclid (I := I) (M := M) g r s T α P₀
    with hu_def
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_support
  have h_even : ∀ j : ℕ,
      MemWkp (d := Module.finrank ℝ E) (2 * j) 2 u Ω'' := by
    intro j
    induction j with
    | zero =>
        rw [Nat.mul_zero, MemWkp_zero]
        have hu_compact : HasCompactSupport u :=
          tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
            g r s T α P₀ hT_support
        exact (Continuous.memLp_of_hasCompactSupport hu_cd.continuous hu_compact).restrict Ω''
    | succ j ih =>
        have h_step :
            MemWkp (d := Module.finrank ℝ E) (2 * j + 2) 2 u Ω'' :=
          memWkp_of_iterClassicalPartial_memWkp_two (d := Module.finrank ℝ E)
            (2 * j) hΩ''_open hu_cd ih
            (fun idx => iterClassicalPartial_memWkp_two_of_weakSolution
              (I := I) (M := M) g r s T F α hK hK_target P₀ hT_support hF_support
              hT_K hweak hΩ''_open hΩ''_compact_closure (2 * j) idx)
        have h_idx : 2 * j + 2 = 2 * (j + 1) := by ring
        rwa [h_idx] at h_step
  exact memWkp_of_iterClassicalPartial_memWkp_two (d := Module.finrank ℝ E)
    (2 * k) hΩ''_open hu_cd (h_even k)
    (fun idx => iterClassicalPartial_memWkp_two_of_weakSolution
      (I := I) (M := M) g r s T F α hK hK_target P₀ hT_support hF_support
      hT_K hweak hΩ''_open hΩ''_compact_closure (2 * k) idx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_memWkp_allOrders_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_memWkp_allOrders_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_memWkp_allOrders_interior ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_memWkp_allOrders_interior

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
