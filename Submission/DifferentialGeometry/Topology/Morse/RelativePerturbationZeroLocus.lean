import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationDifferential
import Submission.DifferentialGeometry.Topology.Morse.RegularZeroAtlas
import Submission.DifferentialGeometry.Topology.Morse.CriticalImageNull

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem regularPerturbationDomain_regular {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∀ q ∈ regularPerturbationDomain φ, perturbationDifferential f φ q = 0 →
      Surjective (fderiv ℝ (perturbationDifferential f φ) q) :=
  fun q hq _ => surjective_fderiv_perturbationDifferential hf hφ q hq.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Morse.regularPerturbationDomain_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Morse.regularPerturbationDomain_regular target :: scope.openDecls } }

@[reducible]
private def reindexZeroAtlas {Z : Type*} [TopologicalSpace Z] {k l : ℕ} (h : k = l)
    (C : ChartedSpace (Fin k → ℝ) Z) : ChartedSpace (Fin l → ℝ) Z := h ▸ C

run_cmd do
  let target := ``Submission.DifferentialGeometry.Morse.reindexZeroAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Morse.reindexZeroAtlas target :: scope.openDecls } }


@[reducible]
def perturbationZeroChartedSpace {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ChartedSpace (Fin n → ℝ)
      {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} :=
  reindexZeroAtlas (perturbationZero_finrank (E := E) (n := n)) (
    regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
      ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn
      (regularPerturbationDomain_regular hf hφ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.perturbationZeroChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.perturbationZeroChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.perturbationZeroChartedSpace ``Submission.DifferentialGeometry.Morse.perturbationZeroChartedSpace


theorem perturbationZeroIsManifold {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    let _ := perturbationZeroChartedSpace hf hφ
    IsManifold 𝓘(ℝ, Fin n → ℝ) 1
      {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := by
  let C := regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
    ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn
    (regularPerturbationDomain_regular hf hφ)
  have hh : ∀ (d : ℕ) (hd : Module.finrank ℝ ((Fin n → ℝ) × E) -
      Module.finrank ℝ (E →L[ℝ] ℝ) = d),
      let _ : ChartedSpace (Fin d → ℝ)
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := reindexZeroAtlas hd C
      IsManifold 𝓘(ℝ, Fin d → ℝ) 1
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := by
    intro d hd
    cases hd
    exact regularZeroIsManifold _ _ _
  exact hh n (perturbationZero_finrank (E := E) (n := n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.perturbationZeroIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.perturbationZeroIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.perturbationZeroIsManifold ``Submission.DifferentialGeometry.Morse.perturbationZeroIsManifold


theorem contMDiff_perturbationZero_inclusion {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    let _ := perturbationZeroChartedSpace hf hφ
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) × E) 1
      (Subtype.val : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0} → (Fin n → ℝ) × E) := by
  let C := regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
    ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn
    (regularPerturbationDomain_regular hf hφ)
  have hh : ∀ (d : ℕ) (hd : Module.finrank ℝ ((Fin n → ℝ) × E) -
      Module.finrank ℝ (E →L[ℝ] ℝ) = d),
      let _ : ChartedSpace (Fin d → ℝ)
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := reindexZeroAtlas hd C
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, (Fin n → ℝ) × E) 1
        (Subtype.val : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
          perturbationDifferential f φ q = 0} → (Fin n → ℝ) × E) := by
    intro d hd
    cases hd
    exact contMDiff_regularZero_inclusion _ _ _
  exact hh n (perturbationZero_finrank (E := E) (n := n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contMDiff_perturbationZero_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contMDiff_perturbationZero_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contMDiff_perturbationZero_inclusion ``Submission.DifferentialGeometry.Morse.contMDiff_perturbationZero_inclusion


theorem contMDiff_perturbationZero_projection {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    let _ := perturbationZeroChartedSpace hf hφ
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) 1
      (fun q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0} => q.val.1) := by
  let _ := perturbationZeroChartedSpace hf hφ
  exact (ContinuousLinearMap.fst ℝ (Fin n → ℝ) E).contDiff.contMDiff.comp
    (contMDiff_perturbationZero_inclusion hf hφ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contMDiff_perturbationZero_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contMDiff_perturbationZero_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contMDiff_perturbationZero_projection ``Submission.DifferentialGeometry.Morse.contMDiff_perturbationZero_projection


theorem ae_regular_perturbationZero_projection {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
    (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    let _ := perturbationZeroChartedSpace hf hφ
    ∀ᵐ p ∂μ, ∀ q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0}, q.val.1 = p →
      _root_.Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
        (fun y : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
          perturbationDifferential f φ q = 0} => y.val.1) q) := by
  let _ := perturbationZeroChartedSpace hf hφ
  let _ := perturbationZeroIsManifold hf hφ
  exact ae_regular_values μ ((contMDiff_perturbationZero_projection hf hφ).mdifferentiable one_ne_zero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.ae_regular_perturbationZero_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.ae_regular_perturbationZero_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.ae_regular_perturbationZero_projection ``Submission.DifferentialGeometry.Morse.ae_regular_perturbationZero_projection

end DifferentialGeometry.Morse
