import Mathlib.Topology.UniformSpace.CompactConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ContinuousFreeLoop)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


structure SmoothImmersion where
  map : AddCircle (1 : ℝ) → M
  smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => map (x : AddCircle (1 : ℝ)))
  immersed : ∀ x : ℝ,
    mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => map (y : AddCircle (1 : ℝ))) x (1 : ℝ) ≠ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem CurveMap.smooth_slice (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) := by
  have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : ℝ => (x, t)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact contMDiffOn_univ.mp (hc.comp hp.contMDiffOn (fun _ _ => ⟨mem_univ _, ht⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smooth_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smooth_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smooth_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.smooth_slice

def SmoothImmersion.slice (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) : SmoothImmersion (I := I) (M := M) where
  map := fun z => c z t
  smooth := c.smooth_slice hc ht
  immersed := fun x => hi x t ht

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.slice

def SmoothCircleMap (f : AddCircle (1 : ℝ) → AddCircle (1 : ℝ)) : Prop :=
  ∀ x : ℝ, ∃ localLift : ℝ → ℝ, ContDiffAt ℝ ∞ localLift x ∧
    ∀ᶠ y in 𝓝 x, (localLift y : AddCircle (1 : ℝ)) = f (y : AddCircle (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothCircleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothCircleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothCircleMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothCircleMap

structure CircleReparametrization (J : Set ℝ) where
  map : ℝ → (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
  smooth : ∀ x t, t ∈ J → ∃ localLift : ℝ × ℝ → ℝ,
    ContDiffWithinAt ℝ ∞ localLift (_root_.Set.univ ×ˢ J) (x, t) ∧
      ∀ᶠ p in 𝓝[_root_.Set.univ ×ˢ J] (x, t),
        (localLift p : AddCircle (1 : ℝ)) = map p.2 (p.1 : AddCircle (1 : ℝ))
  smooth_inverse : ∀ x t, t ∈ J → ∃ localLift : ℝ × ℝ → ℝ,
    ContDiffWithinAt ℝ ∞ localLift (_root_.Set.univ ×ˢ J) (x, t) ∧
      ∀ᶠ p in 𝓝[_root_.Set.univ ×ˢ J] (x, t),
        (localLift p : AddCircle (1 : ℝ)) = (map p.2).symm (p.1 : AddCircle (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CircleReparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CircleReparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CircleReparametrization ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CircleReparametrization

omit [CompleteSpace E] in
theorem parabolic_gauge_velocity [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < (c.speed g x t) ^ (-2 : ℤ) ∧
    (c.speed g x t) ^ (-2 : ℤ) • c.Dx g c.X x t = c.curvatureVector g x t +
      (deriv (fun y => c.speed g y t) x / c.speed g x t ^ 3) • c.X x t := by
  classical
  have hspos : 0 < c.speed g x t := c.speed_pos g hi x t ht
  have hne : c.speed g x t ≠ 0 := ne_of_gt hspos
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y : ℝ => c.lift y t) x :=
    (c.smooth_slice hc ht).contMDiffAt
  have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y : ℝ => c.lift y t) x := by
    refine hγ.of_le (m := 2) ?_
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hrep : DifferentiableAt ℝ
      (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) x := by
    simpa only [CurveMap.X] using
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.differentiableAt_chartRepAt_curveVelocity
        (I := I) hγ2
  have hpair : HasDerivAt (fun s : ℝ => (g t).inner (c.lift s t) (c.X s t) (c.X s t))
      ((g t).inner (c.lift x t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) (c.X x t) +
        (g t).inner (c.lift x t) (c.X x t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x)) x :=
    DifferentialGeometry.Geometry.Riemannian.Variation.inner_deriv_at (I := I) (n := ∞)
      (by simp) (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t)
      (fun s : ℝ => c.X s t) x hγ hrep hrep
  have hF : HasDerivAt (fun s : ℝ => (g t).inner (c.lift s t) (c.X s t) (c.X s t))
      (2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) x := by
    have hval : (g t).inner (c.lift x t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) (c.X x t) +
      (g t).inner (c.lift x t) (c.X x t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) =
        2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) := by
      rw [show c.Dx g c.X x t =
        DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x from rfl]
      rw [← (g t).symm (c.lift x t) (c.X x t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x)]
      ring
    exact hval ▸ hpair
  have hneF : (g t).inner (c.lift x t) (c.X x t) (c.X x t) ≠ 0 := by
    intro h0
    exact hne (by simp [CurveMap.speed, h0])
  have hspeed : HasDerivAt (fun y : ℝ => c.speed g y t)
      ((2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
        (2 * c.speed g x t)) x := by
    have := hF.sqrt hneF
    simpa only [CurveMap.speed] using this
  have hspd : deriv (fun y : ℝ => c.speed g y t) x =
      (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) / c.speed g x t := by
    rw [hspeed.deriv]
    field_simp
  have hinv : HasDerivAt (fun y : ℝ => (c.speed g y t)⁻¹)
      (-(2 * ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
          (2 * c.speed g x t)) / c.speed g x t ^ 2) x :=
    hspeed.inv hne
  have hsmul := DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smulFun
    (g t) (fun y : ℝ => c.lift y t) (fun y : ℝ => (c.speed g y t)⁻¹)
    (fun s : ℝ => c.X s t) x hinv.differentiableAt hrep
  refine ⟨zpow_pos hspos _, ?_⟩
  rw [show c.curvatureVector g x t = (c.speed g x t)⁻¹ •
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (g t) (fun y : ℝ => c.lift y t)
        (fun s : ℝ => (c.speed g s t)⁻¹ • c.X s t) x from rfl]
  rw [hsmul, hinv.deriv, hspd]
  have hz : c.speed g x t ^ (-2 : ℤ) = (c.speed g x t)⁻¹ * (c.speed g x t)⁻¹ := by
    rw [zpow_neg, zpow_ofNat, pow_two, mul_inv]
  have hcoef : (c.speed g x t)⁻¹ *
        (-(2 * ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
            (2 * c.speed g x t)) / c.speed g x t ^ 2) +
      ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
        c.speed g x t / c.speed g x t ^ 3) = 0 := by
    field_simp
    ring
  have hdi : (c.speed g x t)⁻¹ *
        (-(2 * ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
            (2 * c.speed g x t)) / c.speed g x t ^ 2) =
      -((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
        c.speed g x t / c.speed g x t ^ 3) := by
    linarith [hcoef]
  rw [hz, smul_add, smul_smul, smul_smul, hdi, neg_smul]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.parabolic_gauge_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.parabolic_gauge_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.parabolic_gauge_velocity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.parabolic_gauge_velocity

@[instance_reducible] def smoothImmersionTopology {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    TopologicalSpace (SmoothImmersion (I := I) (M := M)) :=
  TopologicalSpace.generateFrom {U | ∃ c : SmoothImmersion (I := I) (M := M),
    ∃ m : ℕ, ∃ ε : ℝ, 0 < ε ∧ U = {d | ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      ‖iteratedDeriv m (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x -
        iteratedDeriv m (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) x‖ < ε}}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology

@[instance_reducible] def smoothCylinderTopology {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (J : Set ℝ) : TopologicalSpace (CurveMap M) :=
  TopologicalSpace.generateFrom {U | ∃ c : CurveMap M, ∃ m : ℕ, ∃ ε : ℝ,
    0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (d.lift q.1 q.2))
        (_root_.Set.univ ×ˢ J) p -
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2))
        (_root_.Set.univ ×ˢ J) p‖ ≤ ρ}}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem smoothCylinderJets_eq_of_eqOn {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {c d : CurveMap M} {J : Set ℝ} (h : ∀ z t, t ∈ J → c z t = d z t)
    (m : ℕ) (p : ℝ × ℝ) (hp : p ∈ _root_.Set.univ ×ˢ J) :
    iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2)) (_root_.Set.univ ×ˢ J) p =
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (d.lift q.1 q.2)) (_root_.Set.univ ×ˢ J) p := by
  apply iteratedFDerivWithin_congr _ hp m
  intro q hq
  exact congrArg e.map (h (q.1 : AddCircle (1 : ℝ)) q.2 hq.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderJets_eq_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderJets_eq_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderJets_eq_of_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderJets_eq_of_eqOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem smoothCylinderTopology_induced_eq_of_eqOn {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} {J : Set ℝ} (f g : P → CurveMap M)
    (h : ∀ p z t, t ∈ J → f p z t = g p z t) :
    TopologicalSpace.induced f (smoothCylinderTopology e J) =
      TopologicalSpace.induced g (smoothCylinderTopology e J) := by
  unfold smoothCylinderTopology
  rw [induced_generateFrom_eq, induced_generateFrom_eq]
  congr 1
  apply Set.image_congr
  intro V hV
  obtain ⟨c, m, ε, hε, rfl⟩ := hV
  ext p
  change (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ J, _ ≤ ρ) ↔
    (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ J, _ ≤ ρ)
  constructor
  · rintro ⟨ρ, hρ, hbound⟩
    refine ⟨ρ, hρ, ?_⟩
    intro q hq
    simpa only [smoothCylinderJets_eq_of_eqOn e (h p) m q ⟨mem_univ _, hq.2⟩] using
      hbound q hq
  · rintro ⟨ρ, hρ, hbound⟩
    refine ⟨ρ, hρ, ?_⟩
    intro q hq
    simpa only [smoothCylinderJets_eq_of_eqOn e (h p) m q ⟨mem_univ _, hq.2⟩] using
      hbound q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_induced_eq_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_induced_eq_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_induced_eq_of_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_induced_eq_of_eqOn


@[instance_reducible]
def immersionJetFamily (p : Σ N : ℕ, Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    TopologicalSpace (SmoothImmersion (I := I) (M := M)) :=
  smoothImmersionTopology p.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetFamily

@[instance_reducible]
def immersionJetTopology : TopologicalSpace (SmoothImmersion (I := I) (M := M)) :=
  ⨅ (p : Σ N : ℕ, Width.SmoothLoopEmbedding (I := I) (Q := M) N), immersionJetFamily p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology

def immersionJetTopologyIntrinsic : Prop :=
  ∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    smoothImmersionTopology e = immersionJetTopology (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem immersionJetTopology_le {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    immersionJetTopology (I := I) (M := M) ≤ smoothImmersionTopology e :=
  iInf_le immersionJetFamily ⟨N, e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopology_le

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem immersionJetTopologyIntrinsic_of_isEmpty [IsEmpty M] :
    immersionJetTopologyIntrinsic (I := I) (M := M) := by
  have hempty : IsEmpty (SmoothImmersion (I := I) (M := M)) :=
    ⟨fun d => (inferInstance : IsEmpty M).elim (d.map 0)⟩
  intro N e
  exact Subsingleton.elim _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionJetTopologyIntrinsic_of_isEmpty

@[instance_reducible]
def cylinderJetFamily (s u : ℝ) (p : Σ N : ℕ, Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    TopologicalSpace {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} :=
  TopologicalSpace.induced
    (fun c : {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} => c.1)
    (smoothCylinderTopology p.2 (_root_.Set.Icc s u))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetFamily

@[instance_reducible]
def cylinderJetTopology (s u : ℝ) :
    TopologicalSpace {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} :=
  ⨅ (p : Σ N : ℕ, Width.SmoothLoopEmbedding (I := I) (Q := M) N), cylinderJetFamily s u p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology

def cylinderJetTopologyIntrinsic : Prop :=
  ∀ (N : ℕ) (s u : ℝ), s < u → ∀ (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    TopologicalSpace.induced
      (fun c : {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} => c.1)
      (smoothCylinderTopology e (_root_.Set.Icc s u)) =
        cylinderJetTopology (I := I) (M := M) s u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopologyIntrinsic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopologyIntrinsic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopologyIntrinsic ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopologyIntrinsic

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem cylinderJetTopology_le {N : ℕ} (s u : ℝ)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    cylinderJetTopology (I := I) (M := M) s u ≤
      TopologicalSpace.induced
        (fun c : {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} => c.1)
        (smoothCylinderTopology e (_root_.Set.Icc s u)) :=
  iInf_le (cylinderJetFamily s u) ⟨N, e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.cylinderJetTopology_le

def continuousFreeLoopOfImmersion (d : SmoothImmersion (I := I) (M := M)) :
    ContinuousFreeLoop M :=
  ⟨d.map, ⟨fun s hs => by
    have hq : Topology.IsCoinducing (fun x : ℝ => (x : AddCircle (1 : ℝ))) :=
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).isCoinducing
    have hcont : Continuous (fun x : ℝ => d.map (x : AddCircle (1 : ℝ))) :=
      continuous_iff_continuousAt.mpr fun x => (d.smooth x).continuousAt
    exact (Topology.isCoinducing_iff.mp hq (d.map ⁻¹' s)).mp
      (by
        change IsOpen ((fun x : ℝ => d.map (x : AddCircle (1 : ℝ))) ⁻¹' s)
        exact hcont.isOpen_preimage s hs)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousFreeLoopOfImmersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousFreeLoopOfImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousFreeLoopOfImmersion ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousFreeLoopOfImmersion

def regularLoopOfImmersion (d : SmoothImmersion (I := I) (M := M)) :
    Width.RegularLoop I M where
  toContinuousLoop := continuousFreeLoopOfImmersion d
  contMDiff_lift := fun x => (d.smooth x).of_le (m := 1) (by
    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.regularLoopOfImmersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.regularLoopOfImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.regularLoopOfImmersion ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.regularLoopOfImmersion

def immersionContinuityIntoRegularLoops : Prop :=
  ∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    @Continuous (SmoothImmersion (I := I) (M := M)) (Width.RegularLoop I M)
      (smoothImmersionTopology e) (Width.regularLoopTopologicalSpace (I := I) (Q := M))
      (regularLoopOfImmersion (I := I) (M := M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionContinuityIntoRegularLoops then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionContinuityIntoRegularLoops"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionContinuityIntoRegularLoops ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.immersionContinuityIntoRegularLoops

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem smoothImmersionTopology_independent {N N' : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (e' : Width.SmoothLoopEmbedding (I := I) (Q := M) N')
    (h : immersionJetTopologyIntrinsic (I := I) (M := M)) :
    smoothImmersionTopology e = smoothImmersionTopology e' :=
  (h N e).trans (h N' e').symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology_independent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology_independent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology_independent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothImmersionTopology_independent

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem smoothCylinderTopology_independent {N N' : ℕ} {s u : ℝ} (hsu : s < u)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (e' : Width.SmoothLoopEmbedding (I := I) (Q := M) N')
    (h : cylinderJetTopologyIntrinsic (I := I) (M := M)) :
    TopologicalSpace.induced
      (fun c : {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} => c.1)
      (smoothCylinderTopology e (_root_.Set.Icc s u)) =
    TopologicalSpace.induced
      (fun c : {c : CurveMap M // c.SmoothOn (I := I) (_root_.Set.Icc s u)} => c.1)
      (smoothCylinderTopology e' (_root_.Set.Icc s u)) :=
  (h N s u hsu e).trans (h N' s u hsu e').symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_independent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_independent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_independent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothCylinderTopology_independent

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem smooth_immersion_regular_family {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (h : immersionContinuityIntoRegularLoops (I := I) (M := M)) :
    ∃ loops : C(P, Width.RegularLoop I M), ∀ p z, loops p z = (initial p).map z :=
  ⟨⟨fun p => regularLoopOfImmersion (initial p),
      @Continuous.comp P (SmoothImmersion (I := I) (M := M)) (Width.RegularLoop I M)
        inferInstance (smoothImmersionTopology e)
        (Width.regularLoopTopologicalSpace (I := I) (Q := M))
        initial (regularLoopOfImmersion (I := I) (M := M)) (h N e) hinit⟩,
    fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smooth_immersion_regular_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smooth_immersion_regular_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smooth_immersion_regular_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smooth_immersion_regular_family

variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M] [nonemptyM : Nonempty M]
  [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

def curveShorteningLocalExistence (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ t₀ ∈ _root_.Set.Ico a b, ∀ c₀ : SmoothImmersion (I := I) (M := M),
    ∃ τ > 0, t₀ + τ ≤ b ∧ ∃ c : CurveMap M,
      c.IsSolutionOn B.family.metric (_root_.Set.Icc t₀ (t₀ + τ)) ∧ ∀ z, c z t₀ = c₀.map z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence

def curveShorteningLocalUniqueness (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ (t₀ t₁ t₂ : ℝ), a ≤ t₀ → t₀ < t₁ → t₀ < t₂ → t₁ ≤ b → t₂ ≤ b →
    ∀ (c₁ c₂ : CurveMap M),
      c₁.IsSolutionOn B.family.metric (_root_.Set.Icc t₀ t₁) →
      c₂.IsSolutionOn B.family.metric (_root_.Set.Icc t₀ t₂) →
      (∀ z, c₁ z t₀ = c₂ z t₀) →
      ∀ z t, t ∈ _root_.Set.Icc t₀ (_root_.Min.min t₁ t₂) → c₁ z t = c₂ z t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness

def curveShorteningLocalUniformDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ (t₀ : {t : ℝ // t ∈ _root_.Set.Ico a b}) (c₀ : SmoothImmersion (I := I) (M := M))
    (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ τ > 0, ∃ U : Set ({t : ℝ // t ∈ _root_.Set.Ico a b} × SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ (t₀, c₀) ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (_root_.Set.Icc 0 τ)) solutions) ∧
        ∀ p : U, (p.1.1 : ℝ) + τ ≤ b ∧
          (solutions p).IsSolutionOn (fun v => B.family.metric ((p.1.1 : ℝ) + v)) (_root_.Set.Icc 0 τ) ∧
          ∀ z, solutions p z 0 = p.1.2.map z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniformDependence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniformDependence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniformDependence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniformDependence

def circleReparametrizationInvariance
    (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ ⦃s u : ℝ⦄, s < u → _root_.Set.Icc s u ⊆ _root_.Set.Icc a b → ∀ (c : CurveMap M),
    c.IsSolutionOn B.family.metric (_root_.Set.Icc s u) → ∀ (φ : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)),
    SmoothCircleMap φ → SmoothCircleMap φ.symm →
    CurveMap.IsSolutionOn (I := I) (fun z t => c (φ z) t) B.family.metric (_root_.Set.Icc s u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleReparametrizationInvariance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleReparametrizationInvariance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleReparametrizationInvariance ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleReparametrizationInvariance

def geometricSolutionGaugeNormalization
    (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ ⦃s u : ℝ⦄, s < u → _root_.Set.Icc s u ⊆ _root_.Set.Icc a b → ∀ (c : CurveMap M) (α : ℝ → ℝ → ℝ),
    c.IsGeometricSolutionOn B.family.metric (_root_.Set.Icc s u) α →
    ∃ τ > 0, s + τ ≤ u ∧ ∃ φ : CircleReparametrization (_root_.Set.Icc s (s + τ)),
      (∀ z, φ.map s z = z) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) B.family.metric
        (_root_.Set.Icc s (s + τ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometricSolutionGaugeNormalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometricSolutionGaugeNormalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometricSolutionGaugeNormalization ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometricSolutionGaugeNormalization

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem exists_mem_Ico_of_lt {c d : ℝ} (h : c < d) : ∃ t₀, t₀ ∈ _root_.Set.Ico c d :=
  ⟨c, le_rfl, h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_mem_Ico_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_mem_Ico_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_mem_Ico_of_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_mem_Ico_of_lt

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningLocalExistence_of_isEmpty [IsEmpty M]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalExistence (I := I) (M := M) B :=
  fun _ _ c₀ => (inferInstance : IsEmpty M).elim (c₀.map 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalExistence_of_isEmpty

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningLocalUniqueness_of_isEmpty [IsEmpty M]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalUniqueness (I := I) (M := M) B :=
  fun _ _ _ _ _ _ _ _ _ c₁ _ _ _ _ _ _ => (inferInstance : IsEmpty M).elim (c₁ 0 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_isEmpty

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem rfs_csf_gauge (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {s u : ℝ} (hsu : s < u) (hwindow : _root_.Set.Icc s u ⊆ _root_.Set.Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (_root_.Set.Icc s u))
    (φ : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hφ : SmoothCircleMap φ) (hφinv : SmoothCircleMap φ.symm)
    (h : circleReparametrizationInvariance (I := I) (M := M) B) :
    CurveMap.IsSolutionOn (I := I) (fun z t => c (φ z) t) B.family.metric (_root_.Set.Icc s u) :=
  h hsu hwindow c hc φ hφ hφinv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_gauge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_gauge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_gauge ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_gauge

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem geometric_solution_reparametrize
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {s u : ℝ} (hsu : s < u) (hwindow : _root_.Set.Icc s u ⊆ _root_.Set.Icc a b)
    (c : CurveMap M) (α : ℝ → ℝ → ℝ)
    (hc : c.IsGeometricSolutionOn B.family.metric (_root_.Set.Icc s u) α)
    (h : geometricSolutionGaugeNormalization (I := I) (M := M) B) :
    ∃ τ > 0, s + τ ≤ u ∧ ∃ φ : CircleReparametrization (_root_.Set.Icc s (s + τ)),
      (∀ z, φ.map s z = z) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) B.family.metric (_root_.Set.Icc s (s + τ)) :=
  h hsu hwindow c α hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometric_solution_reparametrize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometric_solution_reparametrize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometric_solution_reparametrize ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.geometric_solution_reparametrize

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem rfs_csf_local_input (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Ico a b) (c₀ : SmoothImmersion (I := I) (M := M))
    (h : curveShorteningLocalExistence (I := I) (M := M) B) :
    ∃ τ > 0, t₀ + τ ≤ b ∧ ∃ c : CurveMap M,
      c.IsSolutionOn B.family.metric (_root_.Set.Icc t₀ (t₀ + τ)) ∧
      ∀ z, c z t₀ = c₀.map z :=
  h t₀ ht₀ c₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_local_input then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_local_input"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_local_input ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_local_input

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem local_solution_unique (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {t₀ t₁ t₂ : ℝ} (ht₀ : a ≤ t₀) (h₁ : t₀ < t₁) (h₂ : t₀ < t₂)
    (hb₁ : t₁ ≤ b) (hb₂ : t₂ ≤ b) (c₁ c₂ : CurveMap M)
    (hc₁ : c₁.IsSolutionOn B.family.metric (_root_.Set.Icc t₀ t₁))
    (hc₂ : c₂.IsSolutionOn B.family.metric (_root_.Set.Icc t₀ t₂))
    (hinit : ∀ z, c₁ z t₀ = c₂ z t₀)
    (h : curveShorteningLocalUniqueness (I := I) (M := M) B) :
    ∀ z t, t ∈ _root_.Set.Icc t₀ (_root_.Min.min t₁ t₂) → c₁ z t = c₂ z t :=
  h t₀ t₁ t₂ ht₀ h₁ h₂ hb₁ hb₂ c₁ c₂ hc₁ hc₂ hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_unique ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_unique

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem local_solution_starting_time_uniform
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (t₀ : {t : ℝ // t ∈ _root_.Set.Ico a b}) (c₀ : SmoothImmersion (I := I) (M := M))
    (h : curveShorteningLocalUniformDependence (I := I) (M := M) B) :
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ τ > 0, ∃ U : Set ({t : ℝ // t ∈ _root_.Set.Ico a b} × SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ (t₀, c₀) ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (_root_.Set.Icc 0 τ)) solutions) ∧
        ∀ p : U, (p.1.1 : ℝ) + τ ≤ b ∧
          (solutions p).IsSolutionOn
            (fun v => B.family.metric ((p.1.1 : ℝ) + v)) (_root_.Set.Icc 0 τ) ∧
          ∀ z, solutions p z 0 = p.1.2.map z :=
  h t₀ c₀ N e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_starting_time_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_starting_time_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_starting_time_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.local_solution_starting_time_uniform

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem continuous_smoothCylinderTopology_of_continuousOn_jets
    {P : Type*} [TopologicalSpace P] {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J : Set ℝ} (hJ : IsCompact J) {c : P → CurveMap M}
    (hjet : ∀ m : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ m
        (fun v : ℝ × ℝ => e.map ((c q.1).lift v.1 v.2)) (_root_.Set.univ ×ˢ J) q.2)
      (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ×ˢ J)) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e J) c := by
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e J
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro V ⟨d, m, ε, _, rfl⟩ ⟨ρ, hρε, hρ⟩
  let K : Set (ℝ × ℝ) := _root_.Set.Icc (0 : ℝ) 1 ×ˢ J
  let : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact K from isCompact_Icc.prod hJ)
  let jet (p : P) : C(K, (ℝ × ℝ) [×m]→L[ℝ] EuclideanSpace ℝ (Fin N)) :=
    ⟨fun q => iteratedFDerivWithin ℝ m
      (fun v : ℝ × ℝ => e.map ((c p).lift v.1 v.2)) (_root_.Set.univ ×ˢ J) q.1,
      (hjet m).comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun q => ⟨mem_univ _, q.2⟩)⟩
  have hj : Continuous jet := ContinuousMap.continuous_of_continuous_uncurry _
    ((hjet m).comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun q => ⟨mem_univ _, q.2.2⟩))
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hj.tendsto p)
  have hb := (Metric.tendstoUniformly_iff.mp hu) ((ε - ρ) / 2) (by linarith)
  filter_upwards [hb] with q hq
  refine ⟨ρ + (ε - ρ) / 2, by linarith, ?_⟩
  intro v hv
  have hnear : ‖jet q ⟨v, hv⟩ - jet p ⟨v, hv⟩‖ < (ε - ρ) / 2 := by
    rw [← dist_eq_norm, dist_comm]
    exact hq ⟨v, hv⟩
  have hbase := hρ v hv
  change ‖jet q ⟨v, hv⟩ - _‖ ≤ _
  exact (norm_sub_le_norm_sub_add_norm_sub _ (jet p ⟨v, hv⟩) _).trans
    ((add_le_add hnear.le hbase).trans_eq (add_comm _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_smoothCylinderTopology_of_continuousOn_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_smoothCylinderTopology_of_continuousOn_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_smoothCylinderTopology_of_continuousOn_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_smoothCylinderTopology_of_continuousOn_jets

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
