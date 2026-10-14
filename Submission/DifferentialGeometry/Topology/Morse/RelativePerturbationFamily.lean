import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Set _root_.Filter _root_.Function _root_.Module
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators
namespace DifferentialGeometry.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : ℕ}


def finitePerturbation (f : M → ℝ) (φ : Fin n → M → ℝ) (a : Fin n → ℝ) (x : M) : ℝ :=
  f x + ∑ i, a i * φ i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.finitePerturbation ``Submission.DifferentialGeometry.Morse.finitePerturbation

omit [TopologicalSpace M] in
theorem finitePerturbation_zero (f : M → ℝ) (φ : Fin n → M → ℝ) :
    finitePerturbation f φ 0 = f := by
  ext x
  simp [finitePerturbation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.finitePerturbation_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.finitePerturbation_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.finitePerturbation_zero ``Submission.DifferentialGeometry.Morse.finitePerturbation_zero


theorem contMDiff_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i))
    (a : Fin n → ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (finitePerturbation f φ a) := by
  apply hf.add
  exact contMDiff_finsetSum fun i _ => contMDiff_const.mul (hφ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contMDiff_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contMDiff_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contMDiff_finitePerturbation ``Submission.DifferentialGeometry.Morse.contMDiff_finitePerturbation


theorem exists_open_finitePerturbation_eq {f : M → ℝ} {φ : Fin n → M → ℝ} {U : Set M}
    (hφ : ∀ i, tsupport (φ i) ⊆ U) :
    ∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ ∀ a, _root_.Set.EqOn (finitePerturbation f φ a) f N := by
  refine ⟨(⋃ i, tsupport (φ i))ᶜ, (isClosed_iUnion_of_finite fun i => isClosed_tsupport _).isOpen_compl,
    compl_subset_compl.mpr (_root_.Set.iUnion_subset hφ), ?_⟩
  intro a x hx
  have hz : ∀ i, φ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
    (fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩))
  simp [finitePerturbation, hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_open_finitePerturbation_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_open_finitePerturbation_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_open_finitePerturbation_eq ``Submission.DifferentialGeometry.Morse.exists_open_finitePerturbation_eq


def parameterDifferential (φ : Fin n → M → ℝ) (x : M) :
    (Fin n → ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (Fintype.linearCombination ℝ (fun i : Fin n =>
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.parameterDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.parameterDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.parameterDifferential ``Submission.DifferentialGeometry.Morse.parameterDifferential


theorem parameterDifferential_apply (φ : Fin n → M → ℝ) (x : M) (a : Fin n → ℝ) :
    parameterDifferential (I := I) φ x a = ∑ i, a i •
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.parameterDifferential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.parameterDifferential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.parameterDifferential_apply ``Submission.DifferentialGeometry.Morse.parameterDifferential_apply


theorem mfderiv_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ i) x) (a : Fin n → ℝ) :
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ a) x) =
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) + parameterDifferential (I := I) φ x a := by
  have hh := hf.hasMFDerivAt.add (HasMFDerivAt.sum (t := Finset.univ)
    (fun i _ => (hφ i).hasMFDerivAt.const_smul (a i)))
  have hfun : finitePerturbation f φ a = f + ∑ i, a i • φ i := by
    ext y
    simp [finitePerturbation]
  rw [parameterDifferential_apply, hfun]
  exact hh.mfderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.mfderiv_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.mfderiv_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.mfderiv_finitePerturbation ``Submission.DifferentialGeometry.Morse.mfderiv_finitePerturbation


theorem hasFDerivAt_mfderiv_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ i) x) (a : Fin n → ℝ) :
    HasFDerivAt (fun p : Fin n → ℝ =>
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x))
      (parameterDifferential (I := I) φ x) a := by
  have hh := ((parameterDifferential (I := I) φ x).hasFDerivAt (x := a)).const_add
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x)
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun p => mfderiv_finitePerturbation hf hφ p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.hasFDerivAt_mfderiv_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.hasFDerivAt_mfderiv_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.hasFDerivAt_mfderiv_finitePerturbation ``Submission.DifferentialGeometry.Morse.hasFDerivAt_mfderiv_finitePerturbation


theorem surjective_parameterDifferential {φ : Fin n → M → ℝ} {x : M}
    (hspan : Submodule.span ℝ (_root_.Set.range (fun i : Fin n =>
      (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))) = ⊤) :
    Surjective (parameterDifferential (I := I) φ x) := by
  apply LinearMap.range_eq_top.mp
  change (Fintype.linearCombination ℝ (fun i : Fin n =>
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))).range = ⊤
  rw [Fintype.range_linearCombination]
  exact hspan

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.surjective_parameterDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.surjective_parameterDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.surjective_parameterDifferential ``Submission.DifferentialGeometry.Morse.surjective_parameterDifferential


theorem contMDiff_joint_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) :
    ContMDiff (𝓘(ℝ, Fin n → ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : (Fin n → ℝ) × M => finitePerturbation f φ q.1 q.2) := by
  apply (hf.comp contMDiff_snd).add
  apply contMDiff_finsetSum
  intro i _
  exact ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contMDiff.comp
    contMDiff_fst).mul ((hφ i).comp contMDiff_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contMDiff_joint_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contMDiff_joint_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contMDiff_joint_finitePerturbation ``Submission.DifferentialGeometry.Morse.contMDiff_joint_finitePerturbation


theorem exists_relative_perturbation_parameter_submersion
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → M → ℝ) (N : Set M),
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      IsOpen N ∧ Uᶜ ⊆ N ∧
      (∀ a, ContMDiff I 𝓘(ℝ, ℝ) ∞ (finitePerturbation f φ a) ∧
        _root_.Set.EqOn (finitePerturbation f φ a) f N) ∧
      ∀ x ∈ K, ∀ a : Fin n → ℝ,
        _root_.Function.Surjective (fderiv ℝ (fun p : Fin n → ℝ =>
          (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x)) a) := by
  obtain ⟨n, φ, hφ, hspan⟩ := exists_supported_differentials_span_of_isCompact (I := I) hK hU hKU
  obtain ⟨N, hN, hUN, heq⟩ := exists_open_finitePerturbation_eq (f := f) (fun i => (hφ i).2.2)
  refine ⟨n, φ, N, hφ, hN, hUN, fun a =>
    ⟨contMDiff_finitePerturbation hf (fun i => (hφ i).1) a, heq a⟩, ?_⟩
  intro x hx a
  rw [(hasFDerivAt_mfderiv_finitePerturbation (hf.mdifferentiableAt (by simp))
    (fun i => (hφ i).1.mdifferentiableAt (by simp)) a).fderiv]
  exact surjective_parameterDifferential (hspan x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_relative_perturbation_parameter_submersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_relative_perturbation_parameter_submersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_relative_perturbation_parameter_submersion ``Submission.DifferentialGeometry.Morse.exists_relative_perturbation_parameter_submersion

end DifferentialGeometry.Morse
