import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormBounds
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothBasis
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.CompactVolumeEquivalence
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Continuity
import Submission.DifferentialGeometry.Analysis.ODE.Existence.StateCoerciveMass
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem dirichletMass_time_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (K ×ˢ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletMass (g t) u v) K := by
  unfold dirichletMass
  apply integral_family_cont (I := I_half n) (M := M) hK hcont
  exact (u.smooth.continuous.mul v.smooth.continuous).continuousOn.comp
    continuousOn_snd (fun _ _ => Set.mem_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_time_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_time_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_time_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_time_cont

omit [T2Space M] [CompactSpace M] in
private lemma tangentSectionAction_family_continuousOn
    {K : Set ℝ}
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hX : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (K ×ˢ (Set.univ : Set M)))
    {f : M → ℝ} (hf : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn
      (fun p : ℝ × M => tangentSectionAction (I := I_half n) (X p.1) f p.2)
      (K ×ˢ (Set.univ : Set M)) := by
  have htan : Continuous
      (tangentMap (I_half n) 𝓘(ℝ, ℝ) f) :=
    hf.continuous_tangentMap (by simp)
  have hcomp : ContinuousOn
      (fun p : ℝ × M =>
        tangentMap (I_half n) 𝓘(ℝ, ℝ) f
          (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2)))
      (K ×ˢ (Set.univ : Set M)) :=
    htan.continuousOn.comp hX (fun _ _ => Set.mem_univ _)
  have hsnd : Continuous
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) :=
    (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ) (n := 0)).continuous
  exact (hsnd.continuousOn.comp hcomp (fun _ _ => Set.mem_univ _)).congr
    (fun _ _ => rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.tangentSectionAction_family_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.tangentSectionAction_family_continuousOn target :: scope.openDecls } }

theorem dirichletEnergy_time_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular)
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletEnergy (G.metric t) u v) K := by
  unfold dirichletEnergy
  apply integral_family_cont (I := I_half n) (M := M) hK
  · exact fun x₀ i j => hG.chartGramMatrix_continuousOn hKreg x₀ i j
  · exact WithBoundary.gradient_inner_continuousOn_of_tsupport_subset_interior
      hG hKreg u.smooth v.smooth u.interior_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_time_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_time_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_time_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_time_cont

theorem dirichletDrift_time_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hX : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (K ×ˢ (Set.univ : Set M)))
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletDrift (G.metric t) (X t) u v) K := by
  unfold dirichletDrift
  apply integral_family_cont (I := I_half n) (M := M) hK
  · exact fun x₀ i j => hG.chartGramMatrix_continuousOn hKreg x₀ i j
  · have haction := tangentSectionAction_family_continuousOn X hX u.smooth
    have hv : ContinuousOn (fun p : ℝ × M => v.toFun p.2)
        (K ×ˢ (Set.univ : Set M)) :=
      v.smooth.continuous.continuousOn.comp continuousOn_snd
        (fun _ _ => Set.mem_univ _)
    refine (haction.mul hv).congr ?_
    intro p _
    change (G.metric p.1).inner p.2 (X p.1 p.2)
        (gradFun (I := I_half n) (G.metric p.1) u.toFun p.2) * v.toFun p.2 =
      tangentSectionAction (I := I_half n) (X p.1) u.toFun p.2 * v.toFun p.2
    rw [WithBoundary.tangentSectionAction_grad_g_with_boundary_eq_inner
      (I := I_half n) (G.metric p.1) (X p.1) p.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_time_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_time_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_time_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_time_cont

theorem dirichletWeakForm_time_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hX : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (K ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (ha : ContinuousOn a K)
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn
      (fun t => dirichletWeakForm (G.metric t) (X t) (a t) u v) K := by
  have henergy := dirichletEnergy_time_cont hG hK hKreg u v
  have hdrift := dirichletDrift_time_cont hG hK hKreg X hX u v
  have hmass : ContinuousOn (fun t => dirichletMass (G.metric t) u v) K :=
    dirichletMass_time_cont G.metric hK
      (fun x₀ i j => hG.chartGramMatrix_continuousOn hKreg x₀ i j) u v
  unfold dirichletWeakForm
  refine ((henergy.neg.add hdrift).sub (ha.mul hmass)).congr ?_
  intro t _
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_time_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_time_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_time_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_time_cont

section Finite

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def dirichletFinMass
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletMass h (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletMass_add_left])
    (fun c u v => by simp only [map_smul, dirichletMass_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletMass_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletMass_smul_right, smul_eq_mul])).toContinuousBilinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass

@[simp] theorem dirichletFinMass_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinMass h J u v = dirichletMass h (J u) (J v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_apply

def dirichletFinEnergy
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletEnergy h (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletEnergy_add_left])
    (fun c u v => by simp only [map_smul, dirichletEnergy_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletEnergy_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletEnergy_smul_right, smul_eq_mul])).toContinuousBilinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy

@[simp] theorem dirichletFinEnergy_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinEnergy h J u v = dirichletEnergy h (J u) (J v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_apply

theorem dirichletFinEnergy_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u : V) :
    0 ≤ dirichletFinEnergy h J u u := by
  rw [dirichletFinEnergy_apply]
  exact dirichletEnergy_self_nonneg h (J u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_self_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinEnergy_self_nonneg

def dirichletFinDrift
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletDrift h X (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletDrift_add_left])
    (fun c u v => by simp only [map_smul, dirichletDrift_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletDrift_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletDrift_smul_right, smul_eq_mul])).toContinuousBilinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift

@[simp] theorem dirichletFinDrift_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinDrift h X J u v = dirichletDrift h X (J u) (J v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinDrift_apply

def dirichletFinWeakForm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletWeakForm h X a (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletWeakForm_add_left])
    (fun c u v => by simp only [map_smul, dirichletWeakForm_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletWeakForm_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletWeakForm_smul_right, smul_eq_mul])).toContinuousBilinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm

@[simp] theorem dirichletFinWeakForm_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinWeakForm h X a J u v =
      dirichletWeakForm h X a (J u) (J v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_apply

theorem dirichletFinWeakForm_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hX : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (K ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (ha : ContinuousOn a K)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    ContinuousOn
      (fun t => dirichletFinWeakForm (G.metric t) (X t) (a t) J) K := by
  rw [continuousOn_clm_apply]
  intro u
  rw [continuousOn_clm_apply]
  intro v
  simpa only [dirichletFinWeakForm_apply] using
    dirichletWeakForm_time_cont hG hK hKreg X hX a ha (J u) (J v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_cont

theorem dirichletFinMass_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (K ×ˢ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletFinMass (g t) J) K := by
  rw [continuousOn_clm_apply]
  intro u
  rw [continuousOn_clm_apply]
  intro v
  simpa only [dirichletFinMass_apply] using
    dirichletMass_time_cont g hK hcont (J u) (J v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_cont

theorem dirichletFinMass_lower
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2)
    (u : V) :
    C.toReal⁻¹ * ‖u‖ * ‖u‖ ≤ dirichletFinMass h J u u := by
  have hCr : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hrev := dirichletMass_self_rev h C hC0 hCtop hvol (J u)
  rw [horth u] at hrev
  calc
    C.toReal⁻¹ * ‖u‖ * ‖u‖ = C.toReal⁻¹ * ‖u‖ ^ 2 := by ring
    _ ≤ dirichletMass h (J u) (J u) := (inv_mul_le_iff₀ hCr).2 hrev
    _ = dirichletFinMass h J u u := by rw [dirichletFinMass_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_lower ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_lower

end Finite

section FiniteFamily

variable {ι : Type*} [Fintype ι]

def dirichletFinIncl
    {q : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet q) :
    EuclideanSpace ℝ ι →ₗ[ℝ] SmoothScalarDirichlet q := by
  classical
  exact
    { toFun := fun u => ∑ i, u i • φ i
      map_add' := fun u v => by
        simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
          Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, _root_.SemigroupAction.mul_smul,
          Finset.smul_sum, RingHom.id_apply] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl

omit [T2Space M] [CompactSpace M] in
@[simp] theorem dirichletFinIncl_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet q) (u : EuclideanSpace ℝ ι) :
    dirichletFinIncl φ u = ∑ i, u i • φ i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_apply

theorem dirichletFinIncl_orth
    {q : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet q)
    (hφ : Orthonormal ℝ (fun i => smoothToLpDirichlet q (φ i)))
    (u : EuclideanSpace ℝ ι) :
    dirichletMass q (dirichletFinIncl φ u) (dirichletFinIncl φ u) = ‖u‖ ^ 2 := by
  rw [show dirichletMass q (dirichletFinIncl φ u) (dirichletFinIncl φ u) =
      ‖smoothToLpDirichlet q (dirichletFinIncl φ u)‖ ^ 2 from
    (dirichletFinIncl φ u).norm_smoothToLp_sq.symm]
  rw [← real_inner_self_eq_norm_sq]
  rw [dirichletFinIncl_apply]
  simp only [map_sum, map_smul]
  rw [hφ.inner_sum (fun i => u i) (fun i => u i) Finset.univ]
  simp only [RCLike.conj_to_real]
  rw [EuclideanSpace.norm_sq_eq]
  congr 1
  funext i
  rw [Real.norm_eq_abs, sq_abs]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_orth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_orth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_orth ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinIncl_orth

end FiniteFamily

section SmoothBasisFiniteFamily

variable {q : SmoothRiemannianMetric (I_half n) M}

noncomputable def smoothDirichletBasisFinIncl
    (s : Finset (SmoothDirichletBasisIndex q)) :
    EuclideanSpace ℝ s →ₗ[ℝ] SmoothScalarDirichlet q :=
  dirichletFinIncl (fun i : s => smoothDirichletBasisFunction q i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl

noncomputable def smoothDirichletBasisCoordinates
    (s : Finset (SmoothDirichletBasisIndex q))
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    EuclideanSpace ℝ s :=
  WithLp.toLp 2 (fun i : s => (smoothDirichletHilbertBasis q).repr f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisCoordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisCoordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisCoordinates ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisCoordinates

@[simp] theorem smoothDirichletBasisFinIncl_apply
    (s : Finset (SmoothDirichletBasisIndex q)) (u : EuclideanSpace ℝ s) :
    smoothDirichletBasisFinIncl s u =
      ∑ i, u i • smoothDirichletBasisFunction q i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_apply

theorem dirichletMass_smoothDirichletBasisFinIncl
    (s : Finset (SmoothDirichletBasisIndex q)) (u : EuclideanSpace ℝ s) :
    dirichletMass q (smoothDirichletBasisFinIncl s u)
        (smoothDirichletBasisFinIncl s u) = ‖u‖ ^ 2 := by
  apply dirichletFinIncl_orth
  change Orthonormal ℝ
    ((fun i => smoothToLpDirichlet q (smoothDirichletBasisFunction q i)) ∘
      ((↑) : s → SmoothDirichletBasisIndex q))
  exact (smoothDirichletBasisFunction_orthonormal q).comp
    ((↑) : s → SmoothDirichletBasisIndex q) Subtype.val_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smoothDirichletBasisFinIncl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smoothDirichletBasisFinIncl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smoothDirichletBasisFinIncl ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smoothDirichletBasisFinIncl

theorem smoothDirichletBasisFinIncl_coordinates
    (m : ℕ)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    smoothDirichletBasisFinIncl (smoothDirichletBasisFinset q m)
        (smoothDirichletBasisCoordinates (smoothDirichletBasisFinset q m) f) =
      smoothDirichletBasisApproximation q m f := by
  rw [smoothDirichletBasisFinIncl_apply]
  unfold smoothDirichletBasisApproximation
  simp only [smoothDirichletBasisCoordinates, PiLp.toLp_apply]
  exact Finset.sum_attach (smoothDirichletBasisFinset q m)
    (fun i => (smoothDirichletHilbertBasis q).repr f i •
      smoothDirichletBasisFunction q i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_coordinates ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothDirichletBasisFinIncl_coordinates

end SmoothBasisFiniteFamily

section FiniteHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

omit [CompleteSpace V] in
theorem dirichletFinMass_coercive
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2) :
    IsCoercive (dirichletFinMass h J) := by
  refine ⟨C.toReal⁻¹, inv_pos.mpr (ENNReal.toReal_pos hC0 hCtop), ?_⟩
  exact dirichletFinMass_lower h C hC0 hCtop hvol J horth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_coercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_coercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_coercive ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinMass_coercive

theorem dirichletFin_exists
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 < T)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
        C • riemannianVolumeMeasure (I := I_half n) (M := M) (g t))
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2)
    (resid : ℝ → V → (V →L[ℝ] ℝ)) {A : ℝ} {L : ℝ≥0}
    (hA : 0 ≤ A)
    (hlip : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, LipschitzWith L (resid t))
    (hres_cont : ∀ v : V, ContinuousOn (fun t => resid t v) (_root_.Set.Icc (0 : ℝ) T))
    (haff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ A + (L : ℝ) * ‖v‖)
    (v₀ : V) :
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (_root_.Set.Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
        HasDerivWithinAt γ
          ((dirichletFinMass_coercive (g t) C hC0 hCtop
              (hvol t ⟨ht.1, le_of_lt ht.2⟩) J horth).sharpCLM
            (resid t (γ t)))
          (_root_.Set.Ici (0 : ℝ)) t := by
  have hCr : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  let mass : ℝ → V →L[ℝ] V →L[ℝ] ℝ := fun t => dirichletFinMass (g t) J
  have hmass : ContinuousOn mass (_root_.Set.Icc (0 : ℝ) T) :=
    dirichletFinMass_cont g _root_.CompactIccSpace.isCompact_Icc hcont J
  have hcoer : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      C.toReal⁻¹ * ‖v‖ * ‖v‖ ≤ mass t v v := by
    intro t ht v
    exact dirichletFinMass_lower (g t) C hC0 hCtop (hvol t ht) J horth v
  simpa only [mass] using
    (DifferentialGeometry.Analysis.ODE.coerciveMassODE_exists
      (mass := mass) (resid := resid) hT (inv_pos.mpr hCr)
      hA hmass hcoer hlip hres_cont haff v₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFin_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFin_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFin_exists ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFin_exists

theorem dirichletFinWeakForm_exists
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 < T)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
        C • riemannianVolumeMeasure (I := I_half n) (M := M) (g t))
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ)
    (hweak : ContinuousOn
      (fun t => dirichletFinWeakForm (g t) (X t) (a t) J)
      (_root_.Set.Icc (0 : ℝ) T))
    (v₀ : V) :
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (_root_.Set.Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
        HasDerivWithinAt γ
          ((dirichletFinMass_coercive (g t) C hC0 hCtop
              (hvol t ⟨ht.1, le_of_lt ht.2⟩) J horth).sharpCLM
          (dirichletFinWeakForm (g t) (X t) (a t) J (γ t)))
          (_root_.Set.Ici (0 : ℝ)) t := by
  let _ : SeminormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let B : ℝ → V →L[ℝ] V →L[ℝ] ℝ :=
    fun t => dirichletFinWeakForm (g t) (X t) (a t) J
  let resid : ℝ → V → (V →L[ℝ] ℝ) := fun t v => B t v
  have hB : ContinuousOn B (_root_.Set.Icc (0 : ℝ) T) := hweak
  have hnorm : ContinuousOn (fun t => ‖B t‖) (_root_.Set.Icc (0 : ℝ) T) := hB.norm
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.bddAbove_image hnorm
  let L : ℝ≥0 := ⟨max C₀ 0, le_max_right C₀ 0⟩
  have hbound : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ‖B t‖ ≤ (L : ℝ) := by
    intro t ht
    exact (hC₀ ⟨t, ht, rfl⟩).trans (le_max_left C₀ 0)
  have hlip : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, LipschitzWith L (resid t) := by
    intro t ht
    exact (B t).lipschitz.weaken (by
      exact_mod_cast hbound t ht)
  have htime : ∀ v : V, ContinuousOn (fun t => resid t v) (_root_.Set.Icc (0 : ℝ) T) := by
    intro v
    exact hB.clm_apply continuousOn_const
  have haff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ (L : ℝ) * ‖v‖ := by
    intro t ht v
    exact (B t).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg v))
  have haff' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ 0 + (L : ℝ) * ‖v‖ := by
    simpa only [zero_add] using haff
  simpa only [resid, B, zero_add] using
    (dirichletFin_exists g hT hcont C hC0 hCtop hvol J horth resid
      (A := 0) (L := L) le_rfl hlip htime haff' v₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_exists ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletFinWeakForm_exists

theorem dirichletGalerkin_solution_exists
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hX : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (ha : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    (v₀ : V) :
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (_root_.Set.Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
        ∃ v : V, HasDerivWithinAt γ v (_root_.Set.Ici (0 : ℝ)) t ∧
          dirichletFinMass (G.metric t) J v =
            dirichletFinWeakForm (G.metric t) (X t) (a t) J (γ t) := by
  let hgram := fun x₀ i j => hG.chartGramMatrix_continuousOn hreg x₀ i j
  obtain ⟨C, hC0, hCtop, hvol⟩ :=
    volume_uniform_equiv (I := I_half n) (M := M) q G.metric
      _root_.CompactIccSpace.isCompact_Icc hgram
  have hweak := dirichletFinWeakForm_cont hG _root_.CompactIccSpace.isCompact_Icc hreg X hX a ha J
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    dirichletFinWeakForm_exists G.metric hT hgram C hC0 hCtop
      (fun t ht => (hvol t ht).2) J horth X a hweak v₀
  refine ⟨γ, hγ0, hγcont, ?_⟩
  intro t ht
  have ht' : t ∈ _root_.Set.Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  let hco := dirichletFinMass_coercive (G.metric t) C hC0 hCtop
    (hvol t ht').2 J horth
  let v := hco.sharpCLM
    (dirichletFinWeakForm (G.metric t) (X t) (a t) J (γ t))
  refine ⟨v, ?_, ?_⟩
  · simpa only [v, hco] using hγderiv t ht
  · simpa only [v, hco, IsCoercive.sharpCLM_apply] using
      hco.apply_sharp
        (dirichletFinWeakForm (G.metric t) (X t) (a t) J (γ t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_solution_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_solution_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_solution_exists ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_solution_exists

end FiniteHilbert

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
