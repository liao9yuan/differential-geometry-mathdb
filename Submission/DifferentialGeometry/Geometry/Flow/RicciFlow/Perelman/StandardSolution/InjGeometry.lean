import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjOpen
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinUnique
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy
import Submission.DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem rm_bound_of_original_min
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    {Z : TangentSpace I x} {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x) :
    ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  apply hRm sigma hsigma
  intro t ht
  have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
  have hback : T - t ≤ sigma := by linarith only [ht.1]
  have hsqrt : Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
  have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
  have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
    rw [Real.sq_sqrt hnonneg]
    ring
  simpa only [heq] using hclock

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rm_bound_of_original_min
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rm_bound_of_original_min target :: scope.openDecls } }

theorem lInj_local_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun W : E ↦ lExp S T x W tau) Z := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  obtain ⟨K, hK⟩ := rm_bound_of_original_min S T x hRm hmin
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_rm S hS K T x Z hmin htau hsigma.le hK
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).mp hminTau).1
  have hconj : ¬ IsLConjugate S T x Z tau :=
    lMinVec_nconj_lt_of_rm S hS K T x hmin hsigma hK
  exact lExp_localDiffeo S hS T x Z tau hdom hconj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lInj_local_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lInj_local_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lInj_local_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lInj_local_of_rm

variable [NeZero (Module.finrank ℝ E)]

theorem lInj_inj_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau) :
    Set.InjOn (fun Z : E ↦ lExp S T x Z tau)
      (lInjDomain S T x tau) := by
  intro Z hZ W hW hend
  obtain ⟨sigmaZ, hsigmaZ, hZmin⟩ := hZ
  obtain ⟨sigmaW, hsigmaW, hWmin⟩ := hW
  obtain ⟨KZ, hKZ⟩ := rm_bound_of_original_min S T x hRm hZmin
  obtain ⟨KW, hKW⟩ := rm_bound_of_original_min S T x hRm hWmin
  have hWtau : (W, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_rm S hS KW T x W hWmin htau hsigmaW.le hKW
  exact (lMinVec_unique_lt_of_rm S hS KZ T x
    hZmin htau hsigmaZ hWtau hend.symm hKZ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lInj_inj_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lInj_inj_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lInj_inj_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lInj_inj_of_rm

variable [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

theorem exists_lExpPartial_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = lInjDomain S T x tau ∧
      Φ.target =
        (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau ∧
      Set.EqOn Φ (fun Z : E ↦ lExp S T x Z tau)
        (lInjDomain S T x tau) := by
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (fun Z : E ↦ lExp S T x Z tau) (lInjDomain S T x tau) := by
    intro Z
    exact lInj_local_of_rm S hS T x hRm tau htau Z.property
  exact exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
    hlocal (lInj_isOpen_of_rm S hS T hg x hRm tau)
    (lInj_inj_of_rm S hS T x hRm tau htau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_lExpPartial_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_lExpPartial_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_lExpPartial_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_lExpPartial_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
