import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.TimeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle


variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
noncomputable def solutionMetricField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (r : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  Tensor0SBundle.metricTensorField (I := I) (S.family.metric r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionMetricField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionMetricField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionMetricField ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionMetricField

noncomputable def solutionRicField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  CovariantDerivative.ricciSection (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) (S.family.metric t))
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) (S.family.metric t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionRicField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionRicField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionRicField ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionRicField

noncomputable def solutionEvolutionField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  (-2 : Real) • solutionRicField (I := I) S t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionEvolutionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionEvolutionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionEvolutionField ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionEvolutionField

omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solutionRicField_eq_ricciAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (solutionRicField (I := I) S t) x = S.ricciAt t x := by
  have h := CovariantDerivative.ricciSection_apply (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) (S.family.metric t))
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) (S.family.metric t)) x
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionRicField_eq_ricciAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionRicField_eq_ricciAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionRicField_eq_ricciAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionRicField_eq_ricciAt

omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solutionMetricDeriv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ D.regular, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt
        (fun r : Real => (solutionMetricField (I := I) S r) x v)
        ((solutionEvolutionField (I := I) S t) x v)
        D.carrier t := by
  intro t ht x v
  have heq := metric_derivWithin_eq_neg_two_ricci (I := I) S hS ⟨t, ht⟩ x (v 0) (v 1)
  have hvec : vec2 (I := I) (v 0) (v 1) = v := by
    funext i
    fin_cases i <;> simp [vec2]
  rw [hvec] at heq
  have hfun : (fun r : Real => (solutionMetricField (I := I) S r) x v)
      = fun s : Real => (S.family.metric s).inner x (v 0) (v 1) := by
    funext r
    exact Tensor0SBundle.metricTensorField_apply (I := I) (S.family.metric r) x v
  have hval : (solutionEvolutionField (I := I) S t) x v
      = (-2 : Real) * S.ricciAt t x v := by
    simp only [solutionEvolutionField]
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, solutionRicField_eq_ricciAt]
    rw [Tensor0SSpace.smul_apply]
    simp [smul_eq_mul]
  rw [hfun, hval]
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionMetricDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionMetricDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionMetricDeriv ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionMetricDeriv

omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solutionTower_hasDerivAt
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ D.regular, ∀ x : M,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivAt
          (fun r : Real =>
            (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S r) p) x v)
          ((covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) S t) p) x v) t := by
  intro p hp t ht x v
  have h := covDerivOfField_eval_hasDerivWithinAt (I := I) gRef
    (fun r => solutionMetricField (I := I) S r)
    (fun t' => solutionEvolutionField (I := I) S t')
    D.carrier D.regular N
    (solutionMetricDeriv (I := I) S hS) hswap p hp t ht x v
  exact h.hasDerivAt (D.regular_mem_nhds ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionTower_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionTower_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionTower_hasDerivAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionTower_hasDerivAt

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solutionTowerSwap_of_smooth
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x))
    (hFdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ s ∈ D.carrier, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S s) p) y
            (fun a : Fin (p + 2) => V a y)) x)
    (hFtdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) S t) p) y
            (fun a : Fin (p + 2) => V a y)) x) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  covDerivOfField_swapRegularity (I := I) gRef
    (fun r => solutionMetricField (I := I) S r)
    (fun t => solutionEvolutionField (I := I) S t)
    D.carrier D.regular D.regular_subset
    (fun ht => D.regular_mem_nhds ht) N
    (solutionMetricDeriv (I := I) S hS) hSmooth hFdiff hFtdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_smooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_smooth

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem solutionMetricJointAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t : Real} {x : M}
    (hDreg : D.regular ∈ 𝓝 t)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        (solutionMetricField (I := I) S q.1) q.2 (fun a : Fin 2 => V a q.2))
      (t, x) := by
  classical
  set e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x with he
  set b := Module.finBasis Real E with hb
  have hxe : x ∈ e.baseSet := by simp [he]
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) e b
  have hcompOn := hS.smoothMetric.frameCompSmooth (e.localFrame b) hframe
  have hmemProd : (D.regular ×ˢ e.baseSet : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds hDreg (e.open_baseSet.mem_nhds hxe)
  have hcompAt : ∀ i j, ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        (S.family.metric q.1).inner q.2 (e.localFrame b i q.2) (e.localFrame b j q.2))
      (t, x) := fun i j =>
    (hcompOn i j).contMDiffAt hmemProd
  have hcoeff : ∀ (a : Fin 2) i, ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M => e.localFrameCoeff I b i y ((V a) y)) x := fun a i =>
    _root_.contMDiffAt_localFrameCoeff (I := I) b hxe
      ((V a).contMDiff.contMDiffAt) i
  have hsum : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        ∑ i, ∑ j,
          (e.localFrameCoeff I b i q.2 ((V 0) q.2)) *
            (e.localFrameCoeff I b j q.2 ((V 1) q.2)) *
            (S.family.metric q.1).inner q.2 (e.localFrame b i q.2)
              (e.localFrame b j q.2)) (t, x) := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (((hcoeff 0 i).comp (t, x) contMDiffAt_snd).mul
      ((hcoeff 1 j).comp (t, x) contMDiffAt_snd)).mul (hcompAt i j)
  refine hsum.congr_of_eventuallyEq ?_
  have hev0 := Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul
    (I := I) e b (s := fun y => (V 0) y) hxe
  have hev1 := Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul
    (I := I) e b (s := fun y => (V 1) y) hxe
  have hev : ∀ᶠ q : Real × M in 𝓝 (t, x),
      ((V 0) q.2 = ∑ i, e.localFrameCoeff I b i q.2 ((V 0) q.2) • e.localFrame b i q.2) ∧
      ((V 1) q.2 = ∑ i, e.localFrameCoeff I b i q.2 ((V 1) q.2) • e.localFrame b i q.2) :=
    (continuous_snd.tendsto (t, x)).eventually (hev0.and hev1)
  filter_upwards [hev] with q hq
  have h0 := hq.1
  have h1 := hq.2
  have happ : (solutionMetricField (I := I) S q.1) q.2 (fun a : Fin 2 => V a q.2)
      = (S.family.metric q.1).inner q.2 ((V 0) q.2) ((V 1) q.2) :=
    Tensor0SBundle.metricTensorField_apply (I := I) (S.family.metric q.1) q.2 _
  have hexp : (S.family.metric q.1).inner q.2 ((V 0) q.2) ((V 1) q.2)
      = (S.family.metric q.1).inner q.2
          (∑ i, (Trivialization.localFrameCoeff I e b i q.2) ((V 0) q.2)
            • e.localFrame b i q.2)
          (∑ j, (Trivialization.localFrameCoeff I e b j q.2) ((V 1) q.2)
            • e.localFrame b j q.2) := by
    rw [← h0, ← h1]
  rw [happ, hexp]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionMetricJointAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionMetricJointAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionMetricJointAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionMetricJointAt

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem solutionTowerSwap_of_joint
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x)) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  solutionTowerSwap_of_smooth (I := I) gRef S hS N hSmooth
    (fun p _ V s _ x =>
      covDerivOfField_eval_mdiffAt (I := I) gRef (solutionMetricField (I := I) S s) p V x)
    (fun p _ V t _ x =>
      covDerivOfField_eval_mdiffAt (I := I) gRef (solutionEvolutionField (I := I) S t) p V x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_joint ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_of_joint

omit [SigmaCompactSpace M] in
theorem solutionTowerSwap_regularity
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hDreg : ∀ {t : Real}, t ∈ D.regular → D.regular ∈ 𝓝 t) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solutionMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  solutionTowerSwap_of_joint (I := I) gRef S hS N
    (fun p _ V _t ht _x =>
      (covDerivOfField_eval_contMDiffAt (I := I) gRef
        (fun r => solutionMetricField (I := I) S r)
        (fun W => solutionMetricJointAt (I := I) S hS (hDreg ht) W)
        p V).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_regularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_regularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_regularity ``Submission.DifferentialGeometry.CheegerGromovCompactness.solutionTowerSwap_regularity

end CheegerGromovCompactness
end DifferentialGeometry
