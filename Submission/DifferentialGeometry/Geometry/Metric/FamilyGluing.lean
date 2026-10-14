import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private theorem family_contMDiffAt_of_inclusion {U V : TopologicalSpace.Opens M}
    (hUV : U ≤ V) (f : V → ℝ) (x : U)
    (hf : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : U => f (TopologicalSpace.Opens.inclusion hUV y)) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ f (TopologicalSpace.Opens.inclusion hUV x) := by
  classical
  let F : M → ℝ := fun y => if hy : y ∈ V then f ⟨y, hy⟩ else 0
  have hFU : (fun y : U => F (y : M)) =
      (fun y : U => f (TopologicalSpace.Opens.inclusion hUV y)) := by
    funext y
    simp only [F, dif_pos (hUV y.property)]
  have hFV : (fun y : V => F (y : M)) = f := by
    funext y
    simp only [F, dif_pos y.property]
  have hF : ContMDiffAt I 𝓘(ℝ) ∞ F (x : M) := by
    apply contMDiffAt_subtype_iff.mp
    rw [hFU]
    exact hf
  rw [← hFV]
  exact contMDiffAt_subtype_iff.mpr hF

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.family_contMDiffAt_of_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.family_contMDiffAt_of_inclusion target :: scope.openDecls } }

omit [T2Space M] in
private theorem family_contMDiff_tangent_inclusion {U V : TopologicalSpace.Opens M}
    (hUV : U ≤ V)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : V → Type _)) :
    ContMDiff I I.tangent ∞
      (fun y : U => (⟨y, Y (TopologicalSpace.Opens.inclusion hUV y)⟩ : TangentBundle I U)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hinv : ∀ y : U,
      (mfderiv I I (TopologicalSpace.Opens.inclusion hUV : U → V) y).IsInvertible := by
    intro y
    rw [mfderiv_opens_incl]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E)
  have hpb := Y.contMDiff.mpullback_vectorField
    (f := TopologicalSpace.Opens.inclusion hUV) (contMDiff_inclusion hUV) hinv
    (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  have heq : ∀ y : U,
      VectorField.mpullback I I (TopologicalSpace.Opens.inclusion hUV)
        (fun z : V => Y z) y = Y (TopologicalSpace.Opens.inclusion hUV y) := by
    intro y
    apply (hinv y).inverse_apply_eq.mpr
    rw [mfderiv_opens_incl]
    rfl
  simpa only [heq] using hpb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.family_contMDiff_tangent_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.family_contMDiff_tangent_inclusion target :: scope.openDecls } }

variable {ι : Type*} (U : ι → Opens M) (g : ∀ i, SmoothRiemannianMetric I (U i))

private def familyInner (x : ↥(⨆ i, U i)) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g (Opens.mem_iSup.mp x.property).choose).inner ⟨x.val, (Opens.mem_iSup.mp x.property).choose_spec⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.familyInner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.familyInner target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem familyInner_on
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : U i) : familyInner U g (Opens.inclusion (le_iSup U i) x) = (g i).inner x := by
  ext v w
  exact heq _ i x.val _ x.property v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.familyInner_on
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.familyInner_on target :: scope.openDecls } }

private theorem familyInner_contMDiff
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : ↥(⨆ i, U i) => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : ↥(⨆ i, U i) => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        x (familyInner U g x)) := by
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : ↥(⨆ i, U i) => TangentSpace I x →L[ℝ] ℝ)
    (φ := familyInner U g)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : ↥(⨆ i, U i) => ℝ) (φ := fun x => familyInner U g x (Y x))
  intro Z
  have hlocal (i : ι) : ContMDiff I 𝓘(ℝ) ∞ (fun x : U i =>
      familyInner U g (Opens.inclusion (le_iSup U i) x)
        (Y (Opens.inclusion (le_iSup U i) x)) (Z (Opens.inclusion (le_iSup U i) x))) := by
    have htotal := ContMDiff.clm_bundle_apply₂
      (E₁ := fun x : U i => TangentSpace I x) (E₂ := fun x : U i => TangentSpace I x)
      (E₃ := fun _ : U i => ℝ) (b := fun x : U i => x) (ψ := (g i).inner)
      (v := fun x => Y (Opens.inclusion (le_iSup U i) x))
      (w := fun x => Z (Opens.inclusion (le_iSup U i) x))
      (g i).contMDiff (family_contMDiff_tangent_inclusion (le_iSup U i) Y)
        (family_contMDiff_tangent_inclusion (le_iSup U i) Z)
    intro x
    have hat := htotal x
    rw [_root_.Bundle.contMDiffAt_totalSpace] at hat
    simp only [familyInner_on U g heq]
    simpa using! hat.2
  have hscalar : ContMDiff I 𝓘(ℝ) ∞ (fun x => familyInner U g x (Y x) (Z x)) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact family_contMDiffAt_of_inclusion (I := I) (U := U i) (V := ⨆ i, U i)
      (le_iSup U i) _ ⟨x.val, hi⟩ (hlocal i).contMDiffAt
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.familyInner_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.familyInner_contMDiff target :: scope.openDecls } }

def glueMetricFamily
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) :
    SmoothRiemannianMetric I ↥(⨆ i, U i) where
  inner := familyInner U g
  symm x v w := (g (Opens.mem_iSup.mp x.property).choose).symm _ v w
  pos x v hv := (g (Opens.mem_iSup.mp x.property).choose).pos _ v hv
  isVonNBounded x := (g (Opens.mem_iSup.mp x.property).choose).isVonNBounded _
  contMDiff := familyInner_contMDiff U g heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.glueMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.glueMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.glueMetricFamily ``Submission.DifferentialGeometry.Geometry.Metric.glueMetricFamily

theorem glueMetricFamily_inner
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : U i) (v w : TangentSpace I x) :
    (glueMetricFamily U g heq).inner (Opens.inclusion (le_iSup U i) x) v w = (g i).inner x v w := by
  change familyInner U g _ v w = _
  rw [familyInner_on U g heq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.glueMetricFamily_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.glueMetricFamily_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.glueMetricFamily_inner ``Submission.DifferentialGeometry.Geometry.Metric.glueMetricFamily_inner

theorem glueMetricFamily_restrict
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) (i : ι) :
    (glueMetricFamily U g heq).restrictOpenOfSubset (le_iSup U i) = g i := by
  apply SmoothRiemannianMetric.ext_inner
  exact glueMetricFamily_inner U g heq i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.glueMetricFamily_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.glueMetricFamily_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.glueMetricFamily_restrict ``Submission.DifferentialGeometry.Geometry.Metric.glueMetricFamily_restrict

theorem glueMetricFamily_unique
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (g' : SmoothRiemannianMetric I ↥(⨆ i, U i))
    (h : ∀ (i : ι) (x : U i) (v w : TangentSpace I x),
      g'.inner (Opens.inclusion (le_iSup U i) x) v w = (g i).inner x v w) :
    g' = glueMetricFamily U g heq := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
  exact (h i ⟨x.val, hi⟩ v w).trans (glueMetricFamily_inner U g heq i ⟨x.val, hi⟩ v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.glueMetricFamily_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.glueMetricFamily_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.glueMetricFamily_unique ``Submission.DifferentialGeometry.Geometry.Metric.glueMetricFamily_unique

def glueMetricFamilyOn (V : _root_.TopologicalSpace.Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) : SmoothRiemannianMetric I V := by
  have hsup : (⨆ i, U i) = V := le_antisymm (iSup_le hU) (fun x hx => Opens.mem_iSup.mpr (hcover ⟨x, hx⟩))
  exact hsup ▸ glueMetricFamily U g heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn ``Submission.DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn

theorem glueMetricFamilyOn_inner (V : _root_.TopologicalSpace.Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : U i) (v w : TangentSpace I x) :
    (glueMetricFamilyOn U g V hU hcover heq).inner (Opens.inclusion (hU i) x) v w = (g i).inner x v w := by
  have hsup : (⨆ i, U i) = V := le_antisymm (iSup_le hU) (fun x hx => Opens.mem_iSup.mpr (hcover ⟨x, hx⟩))
  subst V
  exact glueMetricFamily_inner U g heq i x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn_inner ``Submission.DifferentialGeometry.Geometry.Metric.glueMetricFamilyOn_inner

end DifferentialGeometry.Geometry.Metric
