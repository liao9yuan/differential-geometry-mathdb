import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import Submission.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.ContDiff
namespace DifferentialGeometry.CheegerGromovCompactness

section ContinuousParameter
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mapCInfConvergenceOnCompacts_of_continuous_spatial_jets
    {G : P → E → F} {A : Set P} {V : Set E} (hV : IsOpen V)
    (hG : ∀ p ∈ A, ContDiffOn ℝ ∞ (G p) V)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun z : P × E => iteratedFDeriv ℝ r (G z.1) z.2) (A ×ˢ V))
    (τ : ℕ → P) (hτ : ∀ n, τ n ∈ A) {p : P} (hp : p ∈ A)
    (htend : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 p)) :
    MapCInfConvergenceOnCompacts V (fun n => G (τ n)) (G p) := by
  intro K hK hKV m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hV hKV
    (fun n => (hG (τ n) (hτ n)).of_le (by exact_mod_cast le_top))
    ((hG p hp).of_le (by exact_mod_cast le_top))
  intro r _hr
  have ht : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝[A] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall hτ⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  obtain ⟨U, hU, hclose⟩ := hK.mem_uniformity_of_prod
    (f := fun q x => iteratedFDeriv ℝ r (G q) x)
    ((hjets r).mono (_root_.Set.prod_mono_right hKV)) hp (Metric.dist_mem_uniformity hepsilon)
  filter_upwards [ht.eventually hU] with n hn
  intro x hx
  have hh : _root_.Dist.dist (iteratedFDeriv ℝ r (G (τ n)) x)
      (iteratedFDeriv ℝ r (G p) x) < epsilon := hclose (τ n) hn x hx
  simpa only [dist_comm] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_continuous_spatial_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_continuous_spatial_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_continuous_spatial_jets ``Submission.DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_continuous_spatial_jets

end ContinuousParameter

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mapCInfConvergenceOnCompacts_of_tendsto_parameter
    {G : P → E → F} {A : Set P} {V : Set E} (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (A ×ˢ V))
    (τ : ℕ → P) (hτ : ∀ n, τ n ∈ A) {p : P} (hp : p ∈ A)
    (htend : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 p)) :
    MapCInfConvergenceOnCompacts V (fun n => G (τ n)) (G p) := by
  apply mapCInfConvergenceOnCompacts_of_continuous_spatial_jets hV _ _ τ hτ hp htend
  · intro q hq
    exact hG.comp (f := fun x => (q, x)) (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hx => ⟨hq, hx⟩)
  · intro r
    exact (hG.iteratedFDeriv_snd hV r (m := 0) (by exact_mod_cast le_top)).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_tendsto_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_tendsto_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_tendsto_parameter ``Submission.DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_tendsto_parameter

theorem mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
    {G : P → E → F} {A : Set P} {V : Set E} (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (A ×ˢ V))
    (τ : ℕ → P) (hτ : ∀ n, τ n ∈ A) {p : P} (hp : p ∈ A)
    (htend : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 p))
    (w : ℕ → ℝ) {w₀ : ℝ} (hw : _root_.Filter.Tendsto w _root_.Filter.atTop (𝓝 w₀)) :
    MapCInfConvergenceOnCompacts V (fun n x => w n • G (τ n) x)
      (fun x => w₀ • G p x) := by
  have hfamily : ContDiffOn ℝ ∞
      (fun q : (ℝ × P) × E => q.1.1 • G q.1.2 q.2) ((_root_.Set.univ ×ˢ A) ×ˢ V) :=
    contDiffOn_fst.fst.smul
      (hG.comp (f := fun q : (ℝ × P) × E => (q.1.2, q.2))
        (contDiffOn_fst.snd.prodMk contDiffOn_snd) (fun _ hq => ⟨hq.1.2, hq.2⟩))
  exact mapCInfConvergenceOnCompacts_of_tendsto_parameter
    (P := ℝ × P) (A := (_root_.Set.univ : Set ℝ) ×ˢ A) (p := (w₀, p))
    (G := fun (q : ℝ × P) (x : E) => q.1 • G q.2 x) hV hfamily (fun n => (w n, τ n))
    (fun n => ⟨mem_univ _, hτ n⟩) ⟨mem_univ _, hp⟩ (hw.prodMk_nhds htend)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter ``Submission.DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter

end DifferentialGeometry.CheegerGromovCompactness
