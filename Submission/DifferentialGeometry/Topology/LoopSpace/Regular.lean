import Submission.DifferentialGeometry.Topology.LoopSpace.PeriodicDescent
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open _root_.Function _root_.ContinuousMap _root_.Manifold
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem periodic_iteratedDeriv {f : ℝ → F} {T : ℝ} (hf : _root_.Function.Periodic f T) (n : ℕ) :
    Periodic (iteratedDeriv n f) T := by
  intro x
  have h := congrFun (iteratedDeriv_comp_add_const n f T) x
  rw [show (fun z => f (z + T)) = f from funext hf] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodic_iteratedDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodic_iteratedDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodic_iteratedDeriv ``Submission.DifferentialGeometry.Topology.periodic_iteratedDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



abbrev regularLoop (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  {γ : freeLoop M // ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => γ (t : loopCircle))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoop ``Submission.DifferentialGeometry.Topology.regularLoop


def regularLoopValue (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ : regularLoop E M) : freeLoop F :=
  (⟨e, he.continuous⟩ : C(M, F)).comp γ.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoopValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoopValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoopValue ``Submission.DifferentialGeometry.Topology.regularLoopValue

theorem regularLoop_embedded_contDiff (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (γ : regularLoop E M) :
    ContDiff ℝ 1 (fun t : ℝ => e (γ.val (t : loopCircle))) :=
  (he.comp γ.property).contDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoop_embedded_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoop_embedded_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoop_embedded_contDiff ``Submission.DifferentialGeometry.Topology.regularLoop_embedded_contDiff


def regularLoopDerivative (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ : regularLoop E M) : freeLoop F :=
  periodicLoop (deriv (fun t : ℝ => e (γ.val (t : loopCircle))))
    (by
      simpa only [iteratedDeriv_one] using periodic_iteratedDeriv (n := 1)
        (f := fun t : ℝ => e (γ.val (t : loopCircle))) (T := 1) (by
          intro t
          simp only [QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]))
    (by
      simpa only [iteratedDeriv_one] using
        (contDiff_nat_iff_iteratedDeriv.mp (regularLoop_embedded_contDiff e he γ)).1 1 le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoopDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoopDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoopDerivative ``Submission.DifferentialGeometry.Topology.regularLoopDerivative

@[simp] theorem regularLoopDerivative_coe (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (γ : regularLoop E M) (t : ℝ) :
    regularLoopDerivative e he γ (t : loopCircle) =
      deriv (fun s : ℝ => e (γ.val (s : loopCircle))) t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoopDerivative_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoopDerivative_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoopDerivative_coe ``Submission.DifferentialGeometry.Topology.regularLoopDerivative_coe


def regularLoopJet (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (γ : regularLoop E M) : freeLoop F × freeLoop F :=
  (regularLoopValue e he γ, regularLoopDerivative e he γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoopJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoopJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoopJet ``Submission.DifferentialGeometry.Topology.regularLoopJet



@[instance_reducible] def regularLoopTopology (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) :
    TopologicalSpace (regularLoop E M) :=
  TopologicalSpace.induced (regularLoopJet e he) inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoopTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoopTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoopTopology ``Submission.DifferentialGeometry.Topology.regularLoopTopology

variable {K : Type*} [TopologicalSpace K]



theorem continuous_regularLoop_iff (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (Γ : K → regularLoop E M) :
    Continuous[inferInstance, regularLoopTopology e he] Γ ↔
      Continuous (fun p : K × loopCircle => e ((Γ p.1).val p.2)) ∧
      Continuous (fun p : K × ℝ => deriv (fun t : ℝ => e ((Γ p.1).val (t : loopCircle))) p.2) := by
  change Continuous[inferInstance, TopologicalSpace.induced (regularLoopJet e he) _] Γ ↔ _
  rw [continuous_induced_rng]
  constructor
  · intro h
    have h₀ := (FreeLoop.continuous_family_iff _).mp h.fst
    have h₁ := (FreeLoop.continuous_family_iff _).mp h.snd
    refine ⟨h₀, ?_⟩
    exact h₁.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  · rintro ⟨h₀, h₁⟩
    have hder : Continuous (fun k => regularLoopDerivative e he (Γ k)) :=
      continuous_periodicLoop_family h₁ _
    exact ((FreeLoop.continuous_family_iff _).mpr h₀).prodMk hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_regularLoop_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_regularLoop_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_regularLoop_iff ``Submission.DifferentialGeometry.Topology.continuous_regularLoop_iff



theorem continuous_regularLoop_inclusion (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e) :
    Continuous[regularLoopTopology e he, inferInstance]
      (fun γ : regularLoop E M => γ.val) := by
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he
  apply (FreeLoop.continuous_family_iff _).mpr
  apply hemb.isInducing.continuous_iff.mpr
  exact ((continuous_regularLoop_iff e he id).mp continuous_id).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_regularLoop_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_regularLoop_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_regularLoop_inclusion ``Submission.DifferentialGeometry.Topology.continuous_regularLoop_inclusion

end DifferentialGeometry.Topology
