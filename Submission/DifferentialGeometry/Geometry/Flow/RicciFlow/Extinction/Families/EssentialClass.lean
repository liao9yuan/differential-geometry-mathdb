import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {Q : Type*} [TopologicalSpace Q]


def constantContractibleLoops : C(Q, ContractibleContinuousLoop Q) :=
  ⟨fun q => ⟨constantLoops q, isContractibleLoop_constant q⟩,
    constantLoops.continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.constantContractibleLoops then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.constantContractibleLoops"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.constantContractibleLoops ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.constantContractibleLoops

def IsEssentialFamilyClass (ξ : FreeContractibleSphereClass Q) : Prop :=
  ∀ f : C(Sphere 2, Q), FreeHomotopyClass.mk (constantContractibleLoops.comp f) ≠ ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.IsEssentialFamilyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.IsEssentialFamilyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.IsEssentialFamilyClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.IsEssentialFamilyClass

theorem not_isEssentialFamilyClass_constant (f : C(Sphere 2, Q)) :
    ¬ IsEssentialFamilyClass (FreeHomotopyClass.mk (constantContractibleLoops.comp f)) := by
  intro h
  exact h f rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.not_isEssentialFamilyClass_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.not_isEssentialFamilyClass_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.not_isEssentialFamilyClass_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.not_isEssentialFamilyClass_constant

theorem isEssentialFamilyClass_of_pi2_zero
    (hpi2 : ∀ q : Q, Subsingleton (HomotopyGroup (Fin 2) Q q))
    (ξ : FreeContractibleSphereClass Q)
    (hnonnull : ∀ q : Q, ξ ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2)
        (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q))) :
    IsEssentialFamilyClass ξ := by
  intro f hf
  obtain ⟨q, hq⟩ := sphereFamily_homotopic_const_of_pi2_subsingleton hpi2 f
  have hconst : ContinuousMap.Homotopic (constantContractibleLoops.comp f)
      (ContinuousMap.const (Sphere 2)
        (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q)) := by
    exact (ContinuousMap.Homotopic.refl constantContractibleLoops).comp hq
  exact hnonnull q (hf.symm.trans ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hconst))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.isEssentialFamilyClass_of_pi2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.isEssentialFamilyClass_of_pi2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.isEssentialFamilyClass_of_pi2_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.isEssentialFamilyClass_of_pi2_zero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [ChartedSpace H Q] [IsManifold I ∞ Q]
    [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]

include hT2 hCompact hConnected hBoundary

theorem rfs_essential_short_family (g : SmoothRiemannianMetric I Q) :
    ∃ sigma K : ℝ, 0 < sigma ∧ 0 ≤ K ∧
      (∀ (ξ : FreeContractibleSphereClass Q), IsEssentialFamilyClass ξ →
        ∀ Γ : RegularRepresentative (I := I) ξ,
          ∀ ell : ℝ, 0 < ell → ell ≤ sigma →
            ∃ p : Sphere 2, ell ≤ loopLength g (Γ.1 p).1.toContinuousLoop) ∧
      (∀ (γ : ContractibleRegularLoop (I := I) (Q := Q)) (ell : ℝ),
        0 < ell → ell ≤ sigma → loopLength g γ.1.toContinuousLoop < ell →
          regularLeastArea g γ ≤ K * ell ^ 2) := by
  classical
  obtain ⟨sigma, K, hsigma, hK, hfill, hcontract, _⟩ := rfs_short_loop_fillings.{0} g
  refine ⟨sigma, K, hsigma, hK, ?_, ?_⟩
  · intro ξ hξ Γ ell _hell hellsigma
    by_contra hnone
    have hshort : ∀ k, loopLength g (Γ.1 k).1.toContinuousLoop < sigma := by
      intro k
      exact (lt_of_not_ge (fun hk => hnone ⟨k, hk⟩)).trans_le hellsigma
    obtain ⟨F, hzero, hone⟩ := hcontract (Sphere 2) Γ.1 hshort
    let i : C(ContractibleRegularLoop (I := I) (Q := Q), RegularLoop I Q) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let f : C(Sphere 2, Q) := loopEvaluation.comp (regularLoopInclusion.comp (i.comp Γ.1))
    have hhom : ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ.1)
        (constantContractibleLoops.comp f) := by
      refine ⟨{
        toFun := fun p => contractibleRegularLoopInclusion (F p)
        continuous_toFun := contractibleRegularLoopInclusion.continuous.comp F.continuous
        map_zero_left := ?_
        map_one_left := ?_ }⟩
      · intro k
        exact congrArg contractibleRegularLoopInclusion (hzero k)
      · intro k
        have h := congrArg contractibleRegularLoopInclusion (hone k)
        convert! h using 1
    exact hξ f (((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hhom).symm.trans Γ.2)
  · intro γ ell hell hellsigma hshort
    obtain ⟨u, hu⟩ := hfill γ.1.toContinuousLoop (γ.1.isLipschitz g)
      (hshort.trans_le hellsigma)
    have hsq : loopLength g γ.1.toContinuousLoop ^ 2 ≤ ell ^ 2 := by
      nlinarith [loopLength_nonneg g γ.1.toContinuousLoop]
    exact (leastArea_le_competitor g γ.1.toContinuousLoop γ.2
      (γ.1.isLipschitz g) u).trans
      (hu.trans (mul_le_mul_of_nonneg_left hsq hK))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_essential_short_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_essential_short_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_essential_short_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_essential_short_family

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
