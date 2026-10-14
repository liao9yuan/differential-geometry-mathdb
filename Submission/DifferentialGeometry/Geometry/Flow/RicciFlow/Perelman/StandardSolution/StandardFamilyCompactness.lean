import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SequentialCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (standardCapWindow)
open scoped _root_.Manifold _root_.Submission.Manifold
namespace DifferentialGeometry.PDE.RicciFlow

theorem StandardSolution.exists_subseq_tendsto_on_compact {Θ : ℝ} (hΘ : Θ < 1)
    (Q : ℕ → StandardSolution) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ Q' : StandardSolution,
      ∀ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc 0 Θ,
          metricDerivNormSupOn K p ((Q (ρ i)).val.metric t) (Q'.val.metric t)
            StandardCap.metric < e := by
  set T : ℝ := (_root_.Max.max Θ 0 + 1) / 2
  have hT : 0 < T := by positivity
  have hΘT : Θ < T := by
    have := le_max_left Θ 0
    have := max_lt hΘ zero_lt_one
    dsimp only [T]
    linarith
  have hT1 : T < 1 := by
    have := max_lt hΘ zero_lt_one
    dsimp only [T]
    linarith
  have hlt : ENNReal.ofReal T < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hT1
  obtain ⟨ρ, hρ, Q', -, hconv⟩ :=
    exists_standard_solution_subsequence_on_shorter_interval Q hT hlt
  refine ⟨ρ, hρ, Q', fun K hK p e he => ?_⟩
  obtain ⟨j, hj⟩ := hconv K hK p e he
  exact ⟨j, fun i hi t ht => hj i hi t ⟨ht.1, ht.2.trans_lt hΘT⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_on_compact

theorem StandardSolution.exists_subseq_tendsto_restrictOpen {Θ : ℝ} (hΘ : Θ < 1)
    (Q : ℕ → StandardSolution) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ Q' : StandardSolution,
      ∀ (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) [SigmaCompactSpace U],
        ∀ K : Set U, IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc 0 Θ,
          metricDerivNormSupOn K p (((Q (ρ i)).val.metric t).restrictOpen U)
            ((Q'.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U) < e := by
  obtain ⟨ρ, hρ, Q', hconv⟩ := StandardSolution.exists_subseq_tendsto_on_compact hΘ Q
  refine ⟨ρ, hρ, Q', fun U _ K hK p e he => ?_⟩
  obtain ⟨j, hj⟩ := hconv (Subtype.val '' K) (hK.image continuous_subtype_val) p e he
  refine ⟨j, fun i hi t ht => ?_⟩
  rw [metricDerivNormSupOn_restrictOpen]
  exact hj i hi t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto_restrictOpen

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSubtypeEuclideanSpaceRealFinOfNatNatMemOpens_differentialGeometry (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) :
    SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSubtypeEuclideanSpaceRealFinOfNatNatMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSubtypeEuclideanSpaceRealFinOfNatNatMemOpens_differentialGeometry target :: scope.openDecls } }

theorem StandardSolution.exists_subseq_tendsto {Θ : ℝ} (hΘ : Θ < 1)
    (Q : ℕ → StandardSolution) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ Q' : StandardSolution, ∀ D : ℝ,
      ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc 0 Θ,
          metricDerivNormSupOn K p
            (((Q (ρ i)).val.metric t).restrictOpen (standardCapWindow D))
            ((Q'.val.metric t).restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D)) < e := by
  obtain ⟨ρ, hρ, Q', hconv⟩ := StandardSolution.exists_subseq_tendsto_restrictOpen hΘ Q
  exact ⟨ρ, hρ, Q', fun D => hconv (standardCapWindow D)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_subseq_tendsto

end DifferentialGeometry.PDE.RicciFlow
