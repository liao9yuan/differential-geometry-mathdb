import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity
import Submission.DifferentialGeometry.Analysis.Spectral.Scalar.Resolvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def iteratedResolventL2 (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Nat.recAux (motive := fun _ =>
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (ContinuousLinearMap.id ℝ _)
    (fun _ prev => (resolventL2 (I := I) (M := M) g).comp prev) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2 ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2

@[simp] lemma iteratedResolventL2_zero (g : SmoothRiemannianMetric I M) :
    iteratedResolventL2 (I := I) (M := M) g 0 =
      ContinuousLinearMap.id ℝ _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero

@[simp] lemma iteratedResolventL2_succ (g : SmoothRiemannianMetric I M) (k : ℕ) :
    iteratedResolventL2 (I := I) (M := M) g (k + 1) =
      (resolventL2 (I := I) (M := M) g).comp
        (iteratedResolventL2 (I := I) (M := M) g k) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ

lemma iteratedResolventL2_one (g : SmoothRiemannianMetric I M) :
    iteratedResolventL2 (I := I) (M := M) g 1 =
      resolventL2 (I := I) (M := M) g := by
  rw [iteratedResolventL2_succ]
  rw [iteratedResolventL2_zero]
  exact ContinuousLinearMap.comp_id _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_one ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_one

@[simp] lemma iteratedResolventL2_zero_apply (g : SmoothRiemannianMetric I M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g 0 f = f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_zero_apply

lemma iteratedResolventL2_succ_apply (g : SmoothRiemannianMetric I M) (k : ℕ)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g (k + 1) f =
      resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply

lemma iteratedResolventL2_add (g : SmoothRiemannianMetric I M) (j k : ℕ) :
    iteratedResolventL2 (I := I) (M := M) g (j + k) =
      (iteratedResolventL2 (I := I) (M := M) g j).comp
        (iteratedResolventL2 (I := I) (M := M) g k) := by
  induction j with
  | zero => simp [iteratedResolventL2_zero]
  | succ j ih =>
    rw [Nat.succ_add, iteratedResolventL2_succ, iteratedResolventL2_succ, ih]
    rw [ContinuousLinearMap.comp_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add

noncomputable def laplacianDomainPow (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Submodule ℝ (H1Compl (I := I) (M := M) g) :=
  Nat.recAux (motive := fun _ => Submodule ℝ (H1Compl (I := I) (M := M) g))
    ⊤
    (fun k _ => LinearMap.range
      ((resolvent (I := I) (M := M) g).toLinearMap.comp
        (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap)) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow

@[simp] lemma laplacianDomainPow_zero (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 0 = ⊤ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero

lemma laplacianDomainPow_succ (g : SmoothRiemannianMetric I M) (k : ℕ) :
    laplacianDomainPow (I := I) (M := M) g (k + 1) =
      LinearMap.range
        ((resolvent (I := I) (M := M) g).toLinearMap.comp
          (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ

lemma laplacianDomainPow_one (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 1 =
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomainPow_succ]
  unfold laplacianDomain
  rw [iteratedResolventL2_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_one ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_one

lemma laplacianDomainPow_succ_mem_iff (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u : H1Compl (I := I) (M := M) g} :
    u ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ↔
      ∃ f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        u = resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k f) := by
  rw [laplacianDomainPow_succ]
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe] at hf
    exact hf.symm
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe]
    exact hf.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff

lemma laplacianDomainPow_succ_subset_laplacianDomain
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    (laplacianDomainPow (I := I) (M := M) g (k + 1) : Set (H1Compl g)) ⊆
      (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  intro u hu
  rw [SetLike.mem_coe, laplacianDomainPow_succ_mem_iff] at hu
  obtain ⟨f, hf⟩ := hu
  rw [SetLike.mem_coe]
  rw [laplacianDomain_mem_iff]
  exact ⟨iteratedResolventL2 (I := I) (M := M) g k f, hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain

lemma laplacianDomainPow_succ_preimage_in_range
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g k hu_h⟩ ∈
      LinearMap.range
        (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap := by
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  rw [LinearMap.mem_range]
  refine ⟨f, ?_⟩
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  exact hf.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_preimage_in_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_preimage_in_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_preimage_in_range ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_preimage_in_range

end Laplacian
end Analysis
end DifferentialGeometry

end
