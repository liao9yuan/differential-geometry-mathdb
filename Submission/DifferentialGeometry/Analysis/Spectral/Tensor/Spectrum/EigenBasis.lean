import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Defs
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def TensorNonzeroResolventEigenvalue
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  { μ : ℝ //
    tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧ μ ≠ 0 }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue

namespace TensorNonzeroResolventEigenvalue

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def val (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) : ℝ :=
  μ.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val

omit [NeZero (Module.finrank ℝ E)] in
lemma eigenspace_ne_bot
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≠ ⊥ :=
  μ.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.eigenspace_ne_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.eigenspace_ne_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.eigenspace_ne_bot ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.eigenspace_ne_bot

omit [NeZero (Module.finrank ℝ E)] in
lemma val_ne_zero
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    μ.val ≠ 0 := μ.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val_ne_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.val_ne_zero

omit [NeZero (Module.finrank ℝ E)] in
lemma hasEigenvalue
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    Module.End.HasEigenvalue
      ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ.val := by
  have h : tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≠ ⊥ :=
    μ.eigenspace_ne_bot
  unfold tensorResolventEigenspace at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.hasEigenvalue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.hasEigenvalue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.hasEigenvalue ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.hasEigenvalue

omit [NeZero (Module.finrank ℝ E)] in
@[ext] lemma ext
    (μ ν : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s)
    (h : μ.val = ν.val) : μ = ν := Subtype.ext h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.ext ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.ext

end TensorNonzeroResolventEigenvalue

omit [NeZero (Module.finrank ℝ E)] in
private lemma nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    { μ : ℝ |
      tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧ μ ≠ 0 } =
      ⋃ n : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue
          ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ ∧
        (1 : ℝ) / (n + 1) ≤ |μ| } := by
  ext μ
  constructor
  · rintro ⟨hμ_eig_ne, hμ_ne⟩
    have hμ_has : Module.End.HasEigenvalue
        ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ := by
      unfold tensorResolventEigenspace at hμ_eig_ne
      exact hμ_eig_ne
    have h_abs_pos : 0 < |μ| := abs_pos.mpr hμ_ne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h_abs_pos
    refine Set.mem_iUnion.mpr ⟨n, hμ_has, ?_⟩
    exact le_of_lt hn
  · rintro hμ_in_union
    obtain ⟨n, hμ_in_n⟩ := Set.mem_iUnion.mp hμ_in_union
    obtain ⟨hμ_eig, hμ_size⟩ := hμ_in_n
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have h_abs_pos : 0 < |μ| := lt_of_lt_of_le h_pos hμ_size
    have hμ_ne : μ ≠ 0 := abs_pos.mp h_abs_pos
    have hμ_eig_ne : tensorResolventEigenspace
        (I := I) (M := M) g r s μ ≠ ⊥ := by
      unfold tensorResolventEigenspace
      exact hμ_eig
    exact ⟨hμ_eig_ne, hμ_ne⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem nonzero_tensor_resolvent_eigenvalues_set_countable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Set.Countable
      { μ : ℝ |
        tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧
          μ ≠ 0 } := by
  rw [nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion]
  apply Set.countable_iUnion
  intro n
  have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
  exact (tensorResolvent_eigenvalues_finite_above
    (I := I) (M := M) g r s h_compact h_pos).countable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_tensor_resolvent_eigenvalues_set_countable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_tensor_resolvent_eigenvalues_set_countable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_tensor_resolvent_eigenvalues_set_countable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_tensor_resolvent_eigenvalues_set_countable

omit [NeZero (Module.finrank ℝ E)] in
theorem TensorNonzeroResolventEigenvalue.countable_ofCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Countable (TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) := by
  unfold TensorNonzeroResolventEigenvalue
  exact (nonzero_tensor_resolvent_eigenvalues_set_countable
    (I := I) (M := M) g r s h_compact).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.countable_ofCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.countable_ofCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.countable_ofCompact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.countable_ofCompact

omit [NeZero (Module.finrank ℝ E)] in
theorem TensorNonzeroResolventEigenvalue.finiteDimensional_ofCompact
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
  tensorResolventEigenspace_finiteDim
    (I := I) (M := M) g r s h_compact μ.val_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.finiteDimensional_ofCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.finiteDimensional_ofCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.finiteDimensional_ofCompact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.finiteDimensional_ofCompact

noncomputable def tensorResolventEigenspaceONB
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ
        (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)))
      ℝ (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
  letI : FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
    μ.finiteDimensional_ofCompact h_compact
  stdOrthonormalBasis ℝ
    (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspaceONB then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspaceONB"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspaceONB ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspaceONB

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    OrthogonalFamily ℝ
      (fun μ : TensorNonzeroResolventEigenvalue
          (I := I) (M := M) g r s =>
        ↥(tensorResolventEigenspace (I := I) (M := M) g r s μ.val))
      (fun μ =>
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtypeₗᵢ) := by
  have hSymm :
      ((tensorResolventL2
        (I := I) (M := M) g r s).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s)
  have h_full : OrthogonalFamily ℝ
      (fun μ : ℝ =>
        ↥(tensorResolventEigenspace (I := I) (M := M) g r s μ))
      (fun μ =>
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ).subtypeₗᵢ) :=
    hSymm.orthogonalFamily_eigenspaces
  have h_inj : Function.Injective
      (fun μ : TensorNonzeroResolventEigenvalue
          (I := I) (M := M) g r s => μ.val) :=
    fun μ ν h => Subtype.ext h
  exact h_full.comp h_inj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace_orthogonalFamily_nonzero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace_orthogonalFamily_nonzero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace_orthogonalFamily_nonzero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace_orthogonalFamily_nonzero

noncomputable def tensorResolventEigenbasisVec
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    TensorL2 r s g :=
  ((tensorResolventEigenspaceONB
        (I := I) (M := M) h_compact i.1 i.2 :
      tensorResolventEigenspace (I := I) (M := M) g r s i.1.val) :
    TensorL2 r s g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenbasisVec_mem
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventEigenbasisVec (I := I) (M := M) h_compact i ∈
      tensorResolventEigenspace (I := I) (M := M) g r s i.1.val := by
  unfold tensorResolventEigenbasisVec
  exact (tensorResolventEigenspaceONB
    (I := I) (M := M) h_compact i.1 i.2).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_mem ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_mem

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenbasisVec_orthonormal
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Orthonormal ℝ
      (tensorResolventEigenbasisVec (I := I) (M := M) (g := g)
        (r := r) (s := s) h_compact) := by
  have h_fam :=
    tensorResolventEigenspace_orthogonalFamily_nonzero
      (I := I) (M := M) g r s
  have h_each : ∀ μ : TensorNonzeroResolventEigenvalue
        (I := I) (M := M) g r s,
      Orthonormal ℝ
        (tensorResolventEigenspaceONB
          (I := I) (M := M) h_compact μ) :=
    fun μ =>
      (tensorResolventEigenspaceONB
        (I := I) (M := M) h_compact μ).orthonormal
  have h_sig := h_fam.orthonormal_sigma_orthonormal h_each
  convert h_sig using 1
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_orthonormal ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_orthonormal

omit [NeZero (Module.finrank ℝ E)] in
private lemma span_tensorResolventEigenbasisVec_le_iSup_eigenspace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)) ≤
      ⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine SetLike.mem_coe.mpr ?_
  refine Submodule.mem_iSup_of_mem i.1 ?_
  exact tensorResolventEigenbasisVec_mem
    (I := I) (M := M) h_compact i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.span_tensorResolventEigenbasisVec_le_iSup_eigenspace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.span_tensorResolventEigenbasisVec_le_iSup_eigenspace target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≤
      Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)) := by
  intro x hx
  let : FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
    μ.finiteDimensional_ofCompact h_compact
  set b := tensorResolventEigenspaceONB
    (I := I) (M := M) h_compact μ
  have h_basis_span : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) = ⊤ :=
    b.toBasis.span_eq
  have h_subtype_apply :
      ((tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtype '' Set.range b) =
      Set.range (fun k =>
        ((b k : tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
          TensorL2 r s g)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have h_in_basis_set : ∀ k : Fin (Module.finrank ℝ
        (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)),
      ((b k :
          tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
            TensorL2 r s g) ∈
      Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact) := by
    intro k
    refine ⟨⟨μ, k⟩, ?_⟩
    rfl
  have h_subtype_subset : Set.range (fun k =>
      ((b k :
          tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
            TensorL2 r s g)) ⊆
      Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact) := by
    rintro y ⟨k, rfl⟩
    exact h_in_basis_set k
  have hx_subtype : x =
      (tensorResolventEigenspace
        (I := I) (M := M) g r s μ.val).subtype ⟨x, hx⟩ := rfl
  have h_top_mem :
      (⟨x, hx⟩ :
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val) ∈
      Submodule.span ℝ (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) := by
    rw [h_basis_span]; trivial
  have h_after_map : x ∈ Submodule.map
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtype
        (Submodule.span ℝ (Set.range (b.toBasis :
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val)) →
          tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val))) := by
    refine ⟨⟨x, hx⟩, h_top_mem, rfl⟩
  rw [Submodule.map_span] at h_after_map
  have h_eq_basis : ((b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val)) = (b : _ → _) := by
    funext k
    have := OrthonormalBasis.coe_toBasis b
    exact congr_fun this k
  rw [h_eq_basis] at h_after_map
  rw [h_subtype_apply] at h_after_map
  exact Submodule.span_mono h_subtype_subset h_after_map

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem span_tensorResolventEigenbasisVec_eq_iSup_eigenspace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)) =
      ⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val := by
  refine le_antisymm
    (span_tensorResolventEigenbasisVec_le_iSup_eigenspace
      (I := I) (M := M) h_compact) ?_
  exact iSup_le
    (tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
      (I := I) (M := M) h_compact)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.span_tensorResolventEigenbasisVec_eq_iSup_eigenspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.span_tensorResolventEigenbasisVec_eq_iSup_eigenspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.span_tensorResolventEigenbasisVec_eq_iSup_eigenspace ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.span_tensorResolventEigenbasisVec_eq_iSup_eigenspace

omit [NeZero (Module.finrank ℝ E)] in
theorem nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    (⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)ᗮ = ⊥ := by
  suffices h_iSup_eq :
      (⨆ μ : TensorNonzeroResolventEigenvalue
                (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val) =
      (⨆ μ : ℝ, tensorResolventEigenspace
                  (I := I) (M := M) g r s μ) by
    rw [h_iSup_eq]
    exact tensorResolventEigenspaces_iSup_orthogonal_eq_bot
      (I := I) (M := M) g r s h_compact
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun μ => ?_)
    exact le_iSup
      (fun ν : ℝ =>
        tensorResolventEigenspace (I := I) (M := M) g r s ν) μ.val
  · refine iSup_le (fun ν => ?_)
    by_cases hν : ν = 0
    · rw [hν,
          tensorResolventEigenspace_zero_eq_bot
            (I := I) (M := M) g r s]
      exact bot_le
    · by_cases h_eig_bot :
          tensorResolventEigenspace (I := I) (M := M) g r s ν = ⊥
      · rw [h_eig_bot]; exact bot_le
      · let hν_in_subtype :
            TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s :=
          ⟨ν, h_eig_bot, hν⟩
        have hval : hν_in_subtype.val = ν := rfl
        calc tensorResolventEigenspace
              (I := I) (M := M) g r s ν
            = tensorResolventEigenspace
                (I := I) (M := M) g r s hν_in_subtype.val := by rw [hval]
          _ ≤ ⨆ μ : TensorNonzeroResolventEigenvalue
                      (I := I) (M := M) g r s,
                  tensorResolventEigenspace
                    (I := I) (M := M) g r s μ.val :=
              le_iSup
                (fun μ : TensorNonzeroResolventEigenvalue
                          (I := I) (M := M) g r s =>
                  tensorResolventEigenspace
                    (I := I) (M := M) g r s μ.val) hν_in_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenbasisVec_span_orthogonal_eq_bot
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    (Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)))ᗮ =
      ⊥ := by
  rw [span_tensorResolventEigenbasisVec_eq_iSup_eigenspace]
  exact nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot
    (I := I) (M := M) h_compact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_span_orthogonal_eq_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_span_orthogonal_eq_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_span_orthogonal_eq_bot ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_span_orthogonal_eq_bot

noncomputable def tensorResolventHilbertEigenbasisSigma
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    HilbertBasis
      (Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)))
      ℝ (TensorL2 r s g) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (tensorResolventEigenbasisVec_orthonormal
      (I := I) (M := M) h_compact)
    (tensorResolventEigenbasisVec_span_orthogonal_eq_bot
      (I := I) (M := M) h_compact)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorResolventHilbertEigenbasisSigma_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_compact i =
      tensorResolventEigenbasisVec
        (I := I) (M := M) h_compact i := by
  unfold tensorResolventHilbertEigenbasisSigma
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (tensorResolventEigenbasisVec_orthonormal
        (I := I) (M := M) h_compact)
      (tensorResolventEigenbasisVec_span_orthogonal_eq_bot
        (I := I) (M := M) h_compact))
    i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventHilbertEigenbasisSigma_ofCompact_isEigenvector
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventL2 (I := I) (M := M) g r s
        (tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact i) =
      i.1.val •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact i := by
  rw [tensorResolventHilbertEigenbasisSigma_apply
    (I := I) (M := M) h_compact i]
  have h_mem := tensorResolventEigenbasisVec_mem
    (I := I) (M := M) h_compact i
  exact (mem_tensorResolventEigenspace_iff
    (I := I) (M := M) g r s i.1.val _).mp h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_ofCompact_isEigenvector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_ofCompact_isEigenvector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_ofCompact_isEigenvector ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_ofCompact_isEigenvector

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
