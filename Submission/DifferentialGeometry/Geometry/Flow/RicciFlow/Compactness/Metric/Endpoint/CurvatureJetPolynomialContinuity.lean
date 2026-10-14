import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeCoefficientContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance flowPolynomialC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flowPolynomialC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flowPolynomialC1 target :: scope.openDecls } }
private local instance flowPolynomialC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flowPolynomialC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flowPolynomialC2 target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in theorem solution_metricPair_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousWithinAt (fun t => (S.base.metric t).inner x v w) (Set.Iio b) b := by
  have hnear : D.carrier ∈ 𝓝[<] b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Set.Ioo_subset_Icc_self.trans hslab)
  exact ((hS.smoothMetric.coeff_cont x v w) b (hslab ⟨hab.le, le_rfl⟩)).mono_of_mem_nhdsWithin hnear

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricPair_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricPair_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricPair_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricPair_continuousWithinAt_terminal

omit [SigmaCompactSpace M] in theorem solution_ricciTensorPair_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousWithinAt (fun t => ricciTensor (I := I) (S.base.metric t) x v w)
      (Set.Iio b) b := by
  have hnear : D.carrier ∈ 𝓝[<] b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Set.Ioo_subset_Icc_self.trans hslab)
  have hc : ContinuousOn (fun t => S.ricci t x (vec2 v w)) D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.ricciCont.eval_continuous (P := {t : ℝ // t ∈ D.carrier})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun t => t.2) continuous_const
      (v := fun k _ => vec2 v w k) (fun _ => continuous_const)
  have heq (t : ℝ) : S.ricci t x (vec2 v w) =
      ricciTensor (I := I) (S.base.metric t) x v w := by
    change metricRicciAt (I := I) (S.base.metric t) x (vec2 v w) = _
    exact metricRicciAt_apply_eq_ricciTensor (I := I) (S.base.metric t) x v w
  simpa only [heq] using
    (hc b (hslab ⟨hab.le, le_rfl⟩)).mono_of_mem_nhdsWithin hnear

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_ricciTensorPair_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_ricciTensorPair_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_ricciTensorPair_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_ricciTensorPair_continuousWithinAt_terminal

theorem solution_curvatureJetPolynomialValues_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (N : ℕ) {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (i : CurvatureJetPolynomialVariable n N) :
    ContinuousWithinAt (fun t => curvatureJetPolynomialValues S N t basis i) (Set.Iio b) b := by
  cases i with
  | inl ij =>
    exact basisInvMetric_continuousWithinAt S.base.metric basis
      (fun j k => solution_metricPair_continuousWithinAt_terminal S hS hab hslab x
        (basis j) (basis k)) ij.1 ij.2
  | inr js =>
    have hn : n ≠ 0 := by
      intro hn
      subst n
      exact Fin.elim0 (js.2 0)
    have hdim : Module.finrank ℝ E = n := by
      calc
        Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) :=
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.finrank_eq.symm
        _ = n := by
          simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis basis
    let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; exact hn⟩
    exact (solution_nablaKRm04_eval_continuousWithinAt_terminal S hS hab hslab hreg js.1.val x
      (fun k => basis (js.2 k))).mono Set.Iio_subset_Iic_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialValues_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialValues_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialValues_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialValues_continuousWithinAt_terminal

theorem solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (N : ℕ) {n r : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ) :
    ContinuousWithinAt (fun t => tensorOfPolynomialComponents basis P
      (curvatureJetPolynomialValues S N t basis)) (Set.Iio b) b :=
  tensorOfPolynomialComponents_continuousWithinAt basis P
    (solution_curvatureJetPolynomialValues_continuousWithinAt_terminal S hS hab hslab hreg N basis)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal

omit [SigmaCompactSpace M] in theorem solution_metricTimeCorrection_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    {n r : ℕ} {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} (hA : ContinuousWithinAt A (Set.Iio b) b) :
    ContinuousWithinAt
      (fun t => covariantEndomorphismAction0S (A t) (ricciSharp (S.base.metric t) x))
      (Set.Iio b) b :=
  metricTimeCorrection_continuousWithinAt S.base.metric basis hA
    (fun i j => solution_metricPair_continuousWithinAt_terminal S hS hab hslab x (basis i) (basis j))
    (fun i j => solution_ricciTensorPair_continuousWithinAt_terminal S hS hab hslab x (basis i) (basis j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricTimeCorrection_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricTimeCorrection_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricTimeCorrection_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_metricTimeCorrection_continuousWithinAt_terminal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
