import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def curveOfLoopFamily (γ : ℝ → ContinuousFreeLoop M) : CurveMap M := fun z t => γ t z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveOfLoopFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveOfLoopFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveOfLoopFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveOfLoopFamily

def LoopFamilyVelocityExtension (a b : ℝ) (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∃ X : ℝ → (p : M) → TangentSpace I p,
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) ∧
    (∀ t ∈ _root_.Set.Ico a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (_root_.Set.Ici t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))) ∧
    ∀ t ∈ _root_.Set.Ioc a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (_root_.Set.Iic t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension

theorem loopFamilyVelocityExtension_zero (a b : ℝ)
    (γ : ℝ → ContinuousFreeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t') :
    LoopFamilyVelocityExtension (I := I) a b γ := by
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I) (n := ∞))
  · intro t _ z
    have hpt : (fun s : ℝ => γ s z) = fun _ : ℝ => γ t z := by
      funext s
      rw [hconst s t]
    rw [hpt, ContinuousLinearMap.smulRight_zero]
    exact hasMFDerivWithinAt_const (γ t z) (_root_.Set.Ici t) t
  · intro t _ z
    have hpt : (fun s : ℝ => γ s z) = fun _ : ℝ => γ t z := by
      funext s
      rw [hconst s t]
    rw [hpt, ContinuousLinearMap.smulRight_zero]
    exact hasMFDerivWithinAt_const (γ t z) (_root_.Set.Iic t) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_zero

def LiftLoopFamily (X : ℝ → (p : M) → TangentSpace I p) :
    ℝ → (p : ℝ × M) → TangentSpace (𝓘(ℝ,ℝ).prod I) p :=
  fun _ (q : ℝ × M) => ((1:ℝ), X q.1 q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LiftLoopFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LiftLoopFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LiftLoopFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LiftLoopFamily

theorem liftLoopFamily_contMDiff (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M => (⟨p, LiftLoopFamily (I := I) X p.1 p⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
  DifferentialGeometry.Analysis.ODE.autonomizedFlowVF_section_contMDiff (I := I) X hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.liftLoopFamily_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.liftLoopFamily_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.liftLoopFamily_contMDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.liftLoopFamily_contMDiff

variable {a b : ℝ}

theorem loopFamilyVelocityExtension_of_subset {a' b' : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (ha : a' ≤ a) (hb : b ≤ b') (h : LoopFamilyVelocityExtension (I := I) a' b' γ) :
    LoopFamilyVelocityExtension (I := I) a b γ := by
  obtain ⟨X, hX, hIco, hIoc⟩ := h
  exact ⟨X, hX,
    fun t ht z => hIco t ⟨le_trans ha ht.1, lt_of_lt_of_le ht.2 hb⟩ z,
    fun t ht z => hIoc t ⟨lt_of_le_of_lt ha ht.1, le_trans ht.2 hb⟩ z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_subset

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
