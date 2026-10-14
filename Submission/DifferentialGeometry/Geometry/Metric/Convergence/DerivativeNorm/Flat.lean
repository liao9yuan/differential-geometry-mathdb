import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction

import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem codRestr_mdiffAt
    {A B : Type*} [TopologicalSpace A] [ChartedSpace H A]
    [TopologicalSpace B] [ChartedSpace H B]
    {W : _root_.TopologicalSpace.Opens B} {f : A → B} (hmem : ∀ y, f y ∈ W) {x : A}
    (hf : ContMDiffAt I I (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y => (⟨f y, hmem y⟩ : W)) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2
  funext y
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.codRestr_mdiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.codRestr_mdiffAt target :: scope.openDecls } }

def nestedOpen {U V : _root_.TopologicalSpace.Opens M} : _root_.TopologicalSpace.Opens U :=
  ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.nestedOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.nestedOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.nestedOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.nestedOpen

private def flatNestedEquiv {U V : _root_.TopologicalSpace.Opens M} (hVU : V ≤ U) :
    V ≃ nestedOpen (M := M) (U := U) (V := V) where
  toFun x := ⟨⟨x.1, hVU x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv _ := rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.flatNestedEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.flatNestedEquiv target :: scope.openDecls } }

noncomputable def flatNestedDiffeo {U V : _root_.TopologicalSpace.Opens M} (hVU : V ≤ U) :
    V ≃ₘ⟮I, I⟯ nestedOpen (M := M) (U := U) (V := V) where
  toEquiv := flatNestedEquiv (M := M) hVU
  contMDiff_toFun := by
    intro x
    exact codRestr_mdiffAt (fun y => y.2) (contMDiff_inclusion hVU).contMDiffAt
  contMDiff_invFun := by
    intro x
    apply codRestr_mdiffAt (fun y => y.2)
    exact ((contMDiff_subtype_val (I := I) (U := U)).comp
      (contMDiff_subtype_val (I := I)
        (U := nestedOpen (M := M) (U := U) (V := V)))).contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.flatNestedDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.flatNestedDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.flatNestedDiffeo ``Submission.DifferentialGeometry.CheegerGromovCompactness.flatNestedDiffeo

omit [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem flatNested_mfderiv {U V : _root_.TopologicalSpace.Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (flatNestedDiffeo (H := H) (I := I) (M := M) hVU :
      V → nestedOpen (M := M) (U := U) (V := V)) x =
      ContinuousLinearMap.id Real E := by
  let F := flatNestedDiffeo (H := H) (I := I) (M := M) hVU
  have hF : MDifferentiableAt I I
      (F : V → nestedOpen (M := M) (U := U) (V := V)) x :=
    F.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I
      (Subtype.val : nestedOpen (M := M) (U := U) (V := V) → U) (F x) :=
    (contMDiff_subtype_val (I := I)
      (U := nestedOpen (M := M) (U := U) (V := V))).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hF
  change mfderiv I I (Opens.inclusion hVU : V → U) x =
    (mfderiv I I (Subtype.val : nestedOpen (M := M) (U := U) (V := V) → U) (F x)).comp
      (mfderiv I I (F : V → nestedOpen (M := M) (U := U) (V := V)) x) at hcomp
  rw [mfderiv_opens_incl (I := I) hVU x,
    mfderiv_subtype_val (I := I) (nestedOpen (M := M) (U := U) (V := V)) (F x)] at hcomp
  ext v
  have hv := DFunLike.congr_fun hcomp v
  change v = mfderiv I I (F : V → nestedOpen (M := M) (U := U) (V := V)) x v at hv
  exact hv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.flatNested_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.flatNested_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.flatNested_mfderiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.flatNested_mfderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [SigmaCompactSpace M] in
private theorem metric_ext
    {U : _root_.TopologicalSpace.Opens M} {g g' : SmoothRiemannianMetric I U}
    (h : ∀ (x : U) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metric_ext
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metric_ext target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] in
theorem restrictSubset_pull
    {U V : _root_.TopologicalSpace.Opens M} (hVU : V ≤ U)
    [T2Space U]
    [T2Space V]
    [hSigmaNested : SigmaCompactSpace (nestedOpen (M := M) (U := U) (V := V))]
    (g : SmoothRiemannianMetric I U) :
    g.restrictOpenOfSubset (I := I) hVU =
      Diffeomorph.pullbackMetric (I := I)
        (g.restrictOpen (I := I) (nestedOpen (M := M) (U := U) (V := V)))
        (flatNestedDiffeo (H := H) (I := I) (M := M) hVU) := by
  let _ := hSigmaNested
  apply metric_ext
  intro x v w
  rw [SmoothRiemannianMetric.restrictSubset_inner,
    Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    flatNested_mfderiv (I := I)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.restrictSubset_pull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.restrictSubset_pull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.restrictSubset_pull ``Submission.DifferentialGeometry.CheegerGromovCompactness.restrictSubset_pull

omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_eq_of_pull
    {P Q : Type*} [TopologicalSpace P] [ChartedSpace H P]
    [TopologicalSpace Q] [ChartedSpace H Q]
    [IsManifold I ∞ P] [IsManifold I ∞ Q]
    [T2Space P]
    [T2Space Q]
    [IsManifold I 1 P] [IsManifold I 2 P]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    [IsManifold I 1 Q] [IsManifold I 2 Q]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) Q]
    (A B C : SmoothRiemannianMetric I P)
    (gk gInf gRef : SmoothRiemannianMetric I Q)
    (F : P ≃ₘ⟮I, I⟯ Q)
    (hA : A = Diffeomorph.pullbackMetric (I := I) gk F)
    (hB : B = Diffeomorph.pullbackMetric (I := I) gInf F)
    (hC : C = Diffeomorph.pullbackMetric (I := I) gRef F)
    (a : Nat) (x : P) :
    metricDerivNorm (I := I) a A B C x =
      metricDerivNorm (I := I) a gk gInf gRef (F x) := by
  subst A
  subst B
  subst C
  exact metricDerivNorm_pullback (E := E) (H := H) (I := I)
    (M := P) (N := Q) gk gInf gRef F a x

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.norm_eq_of_pull
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.norm_eq_of_pull target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDerivNorm_flat
    {U V : _root_.TopologicalSpace.Opens M} (hVU : V ≤ U)
    [SigmaCompactSpace U] [T2Space U]
    [T2Space V]
    (gk gInf gRef : SmoothRiemannianMetric I U) (a : Nat) (x : V) :
    metricDerivNorm (I := I) a
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricDerivNorm (I := I) a gk gInf gRef (Opens.inclusion hVU x) := by
  let W := nestedOpen (M := M) (U := U) (V := V)
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let : IsManifold I 1 V :=
    IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  let : IsManifold I 2 V :=
    IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) V := by
    change IsManifold I ∞ V
    infer_instance
  let : IsManifold I 1 W :=
    IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  let : IsManifold I 2 W :=
    IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) W := by
    change IsManifold I ∞ W
    infer_instance
  let F := flatNestedDiffeo (H := H) (I := I) (M := M) hVU
  calc
    metricDerivNorm (I := I) a
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricDerivNorm (I := I) a (gk.restrictOpen (I := I) W)
        (gInf.restrictOpen (I := I) W)
        (gRef.restrictOpen (I := I) W) (F x) :=
      norm_eq_of_pull (E := E) (H := H) (I := I)
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU)
        (gk.restrictOpen (I := I) W)
        (gInf.restrictOpen (I := I) W)
        (gRef.restrictOpen (I := I) W) F
        (restrictSubset_pull (I := I) hVU gk)
        (restrictSubset_pull (I := I) hVU gInf)
        (restrictSubset_pull (I := I) hVU gRef) a x
    _ = metricDerivNorm (I := I) a gk gInf gRef ((F x : W) : U) :=
      metricDerivNorm_restrictOpen (I := I) gk gInf gRef W a (F x)
    _ = metricDerivNorm (I := I) a gk gInf gRef (Opens.inclusion hVU x) := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_flat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_flat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_flat ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_flat

end CheegerGromovCompactness
end DifferentialGeometry
