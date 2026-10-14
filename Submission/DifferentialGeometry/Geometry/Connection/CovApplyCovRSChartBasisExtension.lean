import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSSecondCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma exists_bump_tsupport_in_goodSet
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ χ : SmoothBumpFunction I b₀,
      tsupport (fun y : M => (χ : M → ℝ) y) ⊆ chartLeviCivitaGoodSet (I := I) α := by
  classical
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hnhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 b₀ := hopen.mem_nhds hb₀
  obtain ⟨χ, _, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) b₀).mem_iff.mp hnhds
  exact ⟨χ, hχ⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.exists_bump_tsupport_in_goodSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.exists_bump_tsupport_in_goodSet target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma bumpedChartBasis_contMDiff
    (α : M) {b₀ : M}
    (k : Fin (Module.finrank ℝ E))
    (χ : SmoothBumpFunction I b₀)
    (hχ_tsupp : tsupport (fun y : M => (χ : M → ℝ) y) ⊆
      chartLeviCivitaGoodSet (I := I) α) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y)) := by
  classical
  have hChart_baseSet : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := I) α k)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α k
  have hGood_sub_baseSet :
      chartLeviCivitaGoodSet (I := I) α ⊆
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hChart_on_good : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y))
      (chartLeviCivitaGoodSet (I := I) α) :=
    hChart_baseSet.mono hGood_sub_baseSet
  have hχ_global : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (χ : M → ℝ) y) :=
    χ.contMDiff
  have hχ_on_good : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (χ : M → ℝ) y)
      (chartLeviCivitaGoodSet (I := I) α) :=
    hχ_global.contMDiffOn
  exact ContMDiffOn.smul_section_of_tsupport hχ_on_good
    (chartLeviCivitaGoodSet_isOpen (I := I) α) hχ_tsupp hChart_on_good

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.bumpedChartBasis_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.bumpedChartBasis_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.bumpedChartBasis_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.bumpedChartBasis_contMDiff

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covApply_covRS_chartBasis_globalSmoothExtension
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ (S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯),
      ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
        U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
        ∀ y ∈ U,
          (S_k_ext : Π b : M, TensorRSSpace r s I b) y =
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) T₀.toSection y := by
  classical
  let _h_top : TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundleTopology r s
  let _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundleFiber r s
  obtain ⟨χ, hχ_tsupp⟩ :=
    exists_bump_tsupport_in_goodSet (I := I) α (b₀ := b₀) hb₀
  have hX_ext_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y)) :=
    bumpedChartBasis_contMDiff (I := I) α (b₀ := b₀) k χ hχ_tsupp
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% (fun y : M => T₀.toSection y)) :=
    T₀.toSection.contMDiff
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (T% (fun y : M => T₀.toSection y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_smooth
  have hSk_on : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% (fun y : M =>
        covApply cov
          (fun z : M => (χ : M → ℝ) z • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z)
          T₀.toSection y))
      Set.univ :=
    covApply_contMDiffOn (cov := cov) hX_ext_smooth hT_plus
  have hSk_global : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% (fun y : M =>
        covApply cov
          (fun z : M => (χ : M → ℝ) z • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z)
          T₀.toSection y)) := by
    intro y
    exact (hSk_on y (by trivial)).contMDiffAt (Filter.univ_mem)
  set S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b : M => TensorRSSpace r s I b⟯ :=
    { toFun := fun y : M =>
        covApply cov
          (fun z : M => (χ : M → ℝ) z • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z)
          T₀.toSection y
      contMDiff_toFun := hSk_global } with hSk_def
  have hχ_eq_one_nhds : ∀ᶠ y in 𝓝 b₀, (χ : M → ℝ) y = 1 := χ.eventuallyEq_one
  obtain ⟨V_set, hV_nhds, hχ_one_V⟩ :=
    Filter.eventually_iff_exists_mem.mp hχ_eq_one_nhds
  obtain ⟨V_open, hV_sub_V_set, hV_open_isOpen, hb₀_in_V_open⟩ :=
    mem_nhds_iff.mp hV_nhds
  set U : Set M :=
    V_open ∩ chartLeviCivitaGoodSet (I := I) α with hU_def
  have hU_open : IsOpen U :=
    hV_open_isOpen.inter (chartLeviCivitaGoodSet_isOpen (I := I) α)
  have hb₀_U : b₀ ∈ U := ⟨hb₀_in_V_open, hb₀⟩
  have hU_sub_good : U ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro y hy
    exact hy.2
  refine ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, ?_⟩
  intro y hyU
  have hχ_one_y : (χ : M → ℝ) y = 1 := by
    have hy_V_set : y ∈ V_set := hV_sub_V_set hyU.1
    exact hχ_one_V y hy_V_set
  have hS_k_val :
      (S_k_ext : Π b : M, TensorRSSpace r s I b) y =
        covApply cov
          (fun z : M => (χ : M → ℝ) z • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z)
          T₀.toSection y := rfl
  rw [hS_k_val]
  change cov.toFun T₀.toSection y
      ((fun z : M => (χ : M → ℝ) z • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z) y)
    = cov.toFun T₀.toSection y (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y)
  have hinner :
      (fun z : M => (χ : M → ℝ) z • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z) y
        = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y := by
    change (χ : M → ℝ) y • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y
        = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y
    rw [hχ_one_y, one_smul]
  rw [hinner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covApply_covRS_chartBasis_globalSmoothExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covApply_covRS_chartBasis_globalSmoothExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covApply_covRS_chartBasis_globalSmoothExtension ``Submission.DifferentialGeometry.Geometry.Connection.covApply_covRS_chartBasis_globalSmoothExtension

end Connection
end Geometry
end DifferentialGeometry

end
