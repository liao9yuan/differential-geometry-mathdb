import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def IsReducedLengthAttainment {H : ObservedHistory.{u}} (S : VariationalStrip H)
    (u : ℝ) : Prop :=
  ∀ x : (H.stage 0).Carrier,
    IsLeast (_root_.Set.range fun y => S.reducedLength u y) (S.reducedLength u x) →
      (∃ γ : ℝ → (H.stage 0).Carrier,
        S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x) →
      ∃ γ : ℝ → (H.stage 0).Carrier,
        S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x ∧
          reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthAttainment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthAttainment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthAttainment ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthAttainment

def HasAdmissibleCurve {H : ObservedHistory.{u}} (S : VariationalStrip H) : Prop :=
  ∃ γ : ℝ → (H.stage 0).Carrier, S.admissible γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasAdmissibleCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasAdmissibleCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasAdmissibleCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasAdmissibleCurve

def IsReducedLengthRealization {H : ObservedHistory.{u}} (S : VariationalStrip H) : Prop :=
  (∀ u ∈ _root_.Set.Ioo S.start S.finish, IsReducedLengthAttainment S u) ∧
    (∀ u ∈ _root_.Set.Ioo S.start S.finish,
      LowerSemicontinuousOn (fun x => S.reducedLength u x)
        (_root_.Set.univ : Set (H.stage 0).Carrier)) ∧
    (∀ u ∈ _root_.Set.Ioo S.start S.finish, ∃ x : (H.stage 0).Carrier,
      IsLeast (_root_.Set.range fun y => S.reducedLength u y) (S.reducedLength u x) ∧
        ∃ γ : ℝ → (H.stage 0).Carrier,
          S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x) ∧
    (∀ u ∈ _root_.Set.Ioo S.start S.finish, ∀ x : (H.stage 0).Carrier,
      IsLeast (_root_.Set.range fun y => S.reducedLength u y) (S.reducedLength u x) →
      (∀ γ : ℝ → (H.stage 0).Carrier, S.admissible γ → γ 0 = S.pole →
        γ (S.finish - u) = x →
        reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x →
        S.regular γ) →
      ∀ η : ℝ, 0 < η →
        ∃ (U : TopologicalSpace.Opens (H.stage 0).Carrier) (hxU : x ∈ U)
          (F : ℝ → ↥U → ℝ) (hF : ∀ σ : ℝ, ContMDiff ThreeModel 𝓘(ℝ, ℝ) ∞ (F σ)),
          F u ⟨x, hxU⟩ = S.reducedLength u x ∧
          (∀ y : ↥U, y ≠ ⟨x, hxU⟩ →
            F u y < S.reducedLength u (y : (H.stage 0).Carrier)) ∧
          deriv (fun σ : ℝ => F σ ⟨x, hxU⟩) u +
            DifferentialGeometry.Geometry.Operator.ΔG (I := ThreeModel) (M := ↥U)
              ((S.metricAt u).restrictOpen U) (⟨F u, hF u⟩ : C^∞⟮ThreeModel, ↥U; ℝ⟯)
              ⟨x, hxU⟩ ≤ 6 + η ∧
          Real.sqrt (DifferentialGeometry.Geometry.Operator.normGradSqFun (I := ThreeModel)
            (M := ↥U) ((S.metricAt u).restrictOpen U) (F u) ⟨x, hxU⟩) ≤ η) ∧
    (∀ u ∈ _root_.Set.Ioo S.start S.finish,
      LowerSemicontinuousWithinAt
        (fun τ : ℝ => _root_.InfSet.sInf (_root_.Set.range (fun x => S.reducedLength (S.finish - τ) x)) - 6 * τ)
        (_root_.Set.Ioo S.start S.finish) (S.finish - u))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsReducedLengthRealization

def isReducedLengthRealizationInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H), HasAdmissibleCurve S →
    IsReducedLengthRealization S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput

theorem isReducedLengthRealizationInput_of_isSurgeryVariationalInput
    (h : isSurgeryVariationalInput.{u}) : isReducedLengthRealizationInput.{u} := by
  intro H S _
  obtain ⟨hfirst, hbarrier, hshift⟩ := h H S
  refine ⟨?_, ?_, ?_, hbarrier, hshift⟩
  · intro u hu x hle _
    exact (hfirst u hu).2.2 x hle
  · intro u hu
    exact (hfirst u hu).1
  · intro u hu
    obtain ⟨x, hx⟩ := (hfirst u hu).2.1
    obtain ⟨γ, hγ, hγ0, hγτ, -⟩ := (hfirst u hu).2.2 x hx
    exact ⟨x, hx, γ, hγ, hγ0, hγτ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isSurgeryVariationalInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isSurgeryVariationalInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isSurgeryVariationalInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isSurgeryVariationalInput

theorem not_isReducedLengthRealization_of_not_hasAdmissibleCurve {H : ObservedHistory.{u}}
    {S : VariationalStrip H} (h : ¬ HasAdmissibleCurve S) : ¬ IsReducedLengthRealization S := by
  intro hreal
  obtain ⟨-, -, hleast, -⟩ := hreal
  obtain ⟨x, -, γ, hγ, -, -⟩ :=
    hleast ((S.start + S.finish) / 2) (by constructor <;> linarith [S.start_lt_finish])
  exact h ⟨γ, hγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isReducedLengthRealization_of_not_hasAdmissibleCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isReducedLengthRealization_of_not_hasAdmissibleCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isReducedLengthRealization_of_not_hasAdmissibleCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isReducedLengthRealization_of_not_hasAdmissibleCurve

def isCommonLocalRealizationOnAdmissibleStrips : Prop :=
  isLocalStabilityInput ∧ isBufferedControlInput.{u} ∧ isReducedLengthRealizationInput.{u} ∧
    isJacobianInput.{u} ∧ (∃ d : OldData, isOldTubeInput.{u} d) ∧
      isEnlargementInput.{u} ∧ isRoundDegreeInput.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips

theorem isLocalStabilityInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : isLocalStabilityInput :=
  h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem isBufferedControlInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : isBufferedControlInput.{u} :=
  h.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem isReducedLengthRealizationInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : isReducedLengthRealizationInput.{u} :=
  h.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isReducedLengthRealizationInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem isJacobianInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : isJacobianInput.{u} :=
  h.2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem exists_isOldTubeInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : ∃ d : OldData, isOldTubeInput.{u} d :=
  h.2.2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isOldTubeInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isOldTubeInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isOldTubeInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isOldTubeInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem isEnlargementInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : isEnlargementInput.{u} :=
  h.2.2.2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem isRoundDegreeInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) : isRoundDegreeInput.{u} :=
  h.2.2.2.2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput_of_isCommonLocalRealizationOnAdmissibleStrips then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput_of_isCommonLocalRealizationOnAdmissibleStrips"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput_of_isCommonLocalRealizationOnAdmissibleStrips ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput_of_isCommonLocalRealizationOnAdmissibleStrips

theorem isCommonLocalRealizationOnAdmissibleStrips_of_components
    (hstability : isLocalStabilityInput) (hbuffered : isBufferedControlInput.{u})
    (hvariational : isReducedLengthRealizationInput.{u}) (hjacobian : isJacobianInput.{u})
    (htube : ∃ d : OldData, isOldTubeInput.{u} d) (henlargement : isEnlargementInput.{u})
    (hround : isRoundDegreeInput.{u}) : isCommonLocalRealizationOnAdmissibleStrips.{u} :=
  ⟨hstability, hbuffered, hvariational, hjacobian, htube, henlargement, hround⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_components ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_components

theorem isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isCommonLocalRealizationOnAdmissibleStrips.{u} :=
  ⟨h.1, h.2.1, isReducedLengthRealizationInput_of_isSurgeryVariationalInput h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
