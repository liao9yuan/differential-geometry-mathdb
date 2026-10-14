import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.SymmetricCoefficientBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.TensorMultilinear
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem exists_iteratedCovGrad_rs_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (i : ℕ) :
    ∃ τ : Equiv.Perm (Fin (s + i)), ∀ (x : M) (d : Tensor0SSpace r I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
            (iteratedCovGrad (I := I) g r s i Φ').toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) g r s i Φ).toSection x) d)) := by
  induction i with
  | zero =>
    refine ⟨σ, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
    exact hrel x d
  | succ i ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_rs_toModel_domDomCongr
      (I := I) (M := M) g r (s + i) τ
      (iteratedCovGrad (I := I) g r s i Φ) (iteratedCovGrad (I := I) g r s i Φ')
      hτ x d v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_iteratedCovGrad_rs_toModel_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_iteratedCovGrad_rs_toModel_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_iteratedCovGrad_rs_toModel_domDomCongr ``Submission.DifferentialGeometry.Analysis.Spectral.exists_iteratedCovGrad_rs_toModel_domDomCongr

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ :=
    exists_iteratedCovGrad_rs_toModel_domDomCongr (I := I) (M := M) g r s σ Φ Φ' hrel i
  have hsec : (iteratedCovGrad (I := I) g r s i Φ').toSection x =
      tensorRSDomDomCongr τ ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
          (iteratedCovGrad (I := I) g r s i Φ').toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
          tensorRSDomDomCongr τ ((iteratedCovGrad (I := I) g r s i Φ).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g r (s + i) x τ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g r s) (σ' : Equiv.Perm (Fin r)) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots
            (I := I) (M := M) g r s R σ')).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_reindexCoefficientInputSlots
        (I := I) (M := M) g r s R σ' i,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots_toSection,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoefficientInputSlotsFiber]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots
          (I := I) (M := M) g r s R σ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i R‖ ^ 2 := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_reindexCoefficientInputSlots
      (I := I) (M := M) g r s R σ i,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_reindexCoefficientInputSlots_eq
      (I := I) (M := M) g r (s + i)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq ``Submission.DifferentialGeometry.Analysis.Spectral.norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq

end Spectral
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Integral.Connection

alias exists_iteratedCovGrad_rs_toModel_domDomCongr :=
  DifferentialGeometry.Analysis.Spectral.exists_iteratedCovGrad_rs_toModel_domDomCongr
alias riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr :=
  DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
alias riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq :=
  DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq

end DifferentialGeometry.Integral.Connection

end
