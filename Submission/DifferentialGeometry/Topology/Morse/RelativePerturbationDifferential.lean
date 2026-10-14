import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationFamily
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators
namespace DifferentialGeometry.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ}

private theorem isOpen_surjective_clm
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] : IsOpen {L : A →L[ℝ] B | _root_.Function.Surjective L} := by
  let : CompleteSpace B := FiniteDimensional.complete ℝ B
  apply isOpen_iff_mem_nhds.mpr
  intro L hL
  obtain ⟨r,hr⟩ := L.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  let R : B →L[ℝ] A := r.toContinuousLinearMap
  have hLR : L.comp R = ContinuousLinearMap.id ℝ B := by
    ext x
    exact DFunLike.congr_fun hr x
  have ho : IsOpen {T : A →L[ℝ] B | IsUnit (T.comp R)} :=
    Units.isOpen.preimage (show Continuous (fun T : A →L[ℝ] B => T.comp R) from
      continuous_id.clm_comp continuous_const)
  have hh : {T : A →L[ℝ] B | IsUnit (T.comp R)} ∈ nhds L :=
    ho.mem_nhds (by change IsUnit (L.comp R); rw [hLR]; exact isUnit_one)
  apply Filter.mem_of_superset hh
  intro T hT
  exact Surjective.of_comp (show _root_.Function.Surjective (T ∘ R) from
    (ContinuousLinearMap.isUnit_iff_bijective.mp hT).2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Morse.isOpen_surjective_clm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Morse.isOpen_surjective_clm target :: scope.openDecls } }


def perturbationDifferential (f : E → ℝ) (φ : Fin n → E → ℝ)
    (q : (Fin n → ℝ) × E) : E →L[ℝ] ℝ := fderiv ℝ (finitePerturbation f φ q.1) q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.perturbationDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.perturbationDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.perturbationDifferential ``Submission.DifferentialGeometry.Morse.perturbationDifferential


theorem perturbationDifferential_eq {f : E → ℝ} {φ : Fin n → E → ℝ} {q : (Fin n → ℝ) × E}
    (hf : DifferentiableAt ℝ f q.2) (hφ : ∀ i, DifferentiableAt ℝ (φ i) q.2) :
    perturbationDifferential f φ q = fderiv ℝ f q.2 + ∑ i, q.1 i • fderiv ℝ (φ i) q.2 := by
  simpa only [mfderiv_eq_fderiv, parameterDifferential_apply, perturbationDifferential] using
    mfderiv_finitePerturbation (I := 𝓘(ℝ, E)) hf.mdifferentiableAt
      (fun i => (hφ i).mdifferentiableAt) q.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.perturbationDifferential_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.perturbationDifferential_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.perturbationDifferential_eq ``Submission.DifferentialGeometry.Morse.perturbationDifferential_eq


theorem contDiff_perturbationDifferential {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ContDiff ℝ ∞ (perturbationDifferential f φ) := by
  have heq : perturbationDifferential f φ = fun q : (Fin n → ℝ) × E =>
      fderiv ℝ f q.2 + ∑ i, q.1 i • fderiv ℝ (φ i) q.2 := by
    funext q
    exact perturbationDifferential_eq (hf.differentiable (by simp) q.2)
      (fun i => (hφ i).differentiable (by simp) q.2)
  rw [heq]
  apply ((contDiff_infty_iff_fderiv.mp hf).2.comp contDiff_snd).add
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst).smul
    ((contDiff_infty_iff_fderiv.mp (hφ i)).2.comp contDiff_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contDiff_perturbationDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contDiff_perturbationDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contDiff_perturbationDifferential ``Submission.DifferentialGeometry.Morse.contDiff_perturbationDifferential


theorem hasFDerivAt_perturbationDifferential_parameter {f : E → ℝ} {φ : Fin n → E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hφ : ∀ i, DifferentiableAt ℝ (φ i) x) (a : Fin n → ℝ) :
    HasFDerivAt (fun p => perturbationDifferential f φ (p,x))
      (parameterDifferential (I := 𝓘(ℝ, E)) φ x) a := by
  simpa only [mfderiv_eq_fderiv, perturbationDifferential] using
    hasFDerivAt_mfderiv_finitePerturbation (I := 𝓘(ℝ, E)) hf.mdifferentiableAt
      (fun i => (hφ i).mdifferentiableAt) a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.hasFDerivAt_perturbationDifferential_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.hasFDerivAt_perturbationDifferential_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.hasFDerivAt_perturbationDifferential_parameter ``Submission.DifferentialGeometry.Morse.hasFDerivAt_perturbationDifferential_parameter


theorem surjective_fderiv_perturbationDifferential {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q : (Fin n → ℝ) × E)
    (hreg : _root_.Function.Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ q.2)) :
    Surjective (fderiv ℝ (perturbationDifferential f φ) q) := by
  have hd := ((contDiff_perturbationDifferential hf hφ).differentiable (by simp) q).hasFDerivAt
  have hh := hd.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
  have heq := hh.unique (hasFDerivAt_perturbationDifferential_parameter
    (hf.differentiable (by simp) q.2) (fun i => (hφ i).differentiable (by simp) q.2) q.1)
  rw [← heq] at hreg
  exact Surjective.of_comp (show _root_.Function.Surjective ((fderiv ℝ (perturbationDifferential f φ) q) ∘
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) E)) from hreg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.surjective_fderiv_perturbationDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.surjective_fderiv_perturbationDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.surjective_fderiv_perturbationDifferential ``Submission.DifferentialGeometry.Morse.surjective_fderiv_perturbationDifferential


theorem continuous_parameterDifferential {φ : Fin n → E → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    Continuous (parameterDifferential (I := 𝓘(ℝ, E)) φ) := by
  apply continuous_clm_apply.mpr
  intro a
  simp only [parameterDifferential_apply, mfderiv_eq_fderiv]
  exact continuous_finsetSum _ fun i _ => ((hφ i).continuous_fderiv (by simp)).const_smul (a i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.continuous_parameterDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.continuous_parameterDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.continuous_parameterDifferential ``Submission.DifferentialGeometry.Morse.continuous_parameterDifferential


theorem isOpen_regularPerturbationBase [FiniteDimensional ℝ E] {φ : Fin n → E → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    IsOpen {x : E | _root_.Function.Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ x)} :=
  isOpen_surjective_clm.preimage (continuous_parameterDifferential hφ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isOpen_regularPerturbationBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isOpen_regularPerturbationBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isOpen_regularPerturbationBase ``Submission.DifferentialGeometry.Morse.isOpen_regularPerturbationBase

section FiniteDimension
variable [FiniteDimensional ℝ E]


theorem perturbationZero_finrank :
    Module.finrank ℝ ((Fin n → ℝ) × E) - Module.finrank ℝ (E →L[ℝ] ℝ) = n := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
  simp [Module.finrank_prod, Subspace.dual_finrank_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.perturbationZero_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.perturbationZero_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.perturbationZero_finrank ``Submission.DifferentialGeometry.Morse.perturbationZero_finrank


def regularPerturbationDomain (φ : Fin n → E → ℝ) : Set ((Fin n → ℝ) × E) :=
  univ ×ˢ {x : E | _root_.Function.Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ x)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.regularPerturbationDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.regularPerturbationDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.regularPerturbationDomain ``Submission.DifferentialGeometry.Morse.regularPerturbationDomain


theorem isOpen_regularPerturbationDomain {φ : Fin n → E → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) : IsOpen (regularPerturbationDomain φ) :=
  isOpen_univ.prod (isOpen_regularPerturbationBase hφ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isOpen_regularPerturbationDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isOpen_regularPerturbationDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isOpen_regularPerturbationDomain ``Submission.DifferentialGeometry.Morse.isOpen_regularPerturbationDomain


theorem exists_supported_regularPerturbationDomain {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      IsOpen (regularPerturbationDomain φ) ∧
      (_root_.Set.univ ×ˢ K : Set ((Fin n → ℝ) × E)) ⊆ regularPerturbationDomain φ := by
  obtain ⟨n, φ, hφ,hspan⟩ := exists_supported_differentials_span_of_isCompact
    (I := 𝓘(ℝ, E)) hK hU hKU
  have hφ' : ∀ i, ContDiff ℝ ∞ (φ i) := fun i => contMDiff_iff_contDiff.mp (hφ i).1
  refine ⟨n, φ, fun i => ⟨hφ' i, (hφ i).2⟩,isOpen_regularPerturbationDomain hφ',?_⟩
  intro q hq
  exact ⟨mem_univ _,surjective_parameterDifferential (hspan q.2 hq.2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_supported_regularPerturbationDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_supported_regularPerturbationDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_supported_regularPerturbationDomain ``Submission.DifferentialGeometry.Morse.exists_supported_regularPerturbationDomain

end FiniteDimension
end DifferentialGeometry.Morse
