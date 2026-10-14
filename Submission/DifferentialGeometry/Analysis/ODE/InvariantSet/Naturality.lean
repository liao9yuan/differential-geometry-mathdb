import Submission.DifferentialGeometry.Analysis.ODE.InvariantSet.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def pushForwardVectorField (e : E ≃L[ℝ] F) (f : ℝ → E → E) : ℝ → F → F :=
  fun t y ↦ e (f t (e.symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.pushForwardVectorField

@[simp]
theorem pushForwardVectorField_apply (e : E ≃L[ℝ] F) (f : ℝ → E → E) (t : ℝ) (y : F) :
    pushForwardVectorField e f t y = e (f t (e.symm y)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.pushForwardVectorField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_apply ``Submission.DifferentialGeometry.Analysis.ODE.pushForwardVectorField_apply

@[simp]
theorem pushForwardVectorField_refl (f : ℝ → E → E) :
    pushForwardVectorField (ContinuousLinearEquiv.refl ℝ E) f = f := by
  ext t x
  simp [pushForwardVectorField]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.pushForwardVectorField_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_refl ``Submission.DifferentialGeometry.Analysis.ODE.pushForwardVectorField_refl

@[simp]
theorem pushForwardVectorField_trans (e : E ≃L[ℝ] F) (e' : F ≃L[ℝ] G)
    (f : ℝ → E → E) :
    pushForwardVectorField (e.trans e') f =
      pushForwardVectorField e' (pushForwardVectorField e f) := by
  ext t x
  simp [pushForwardVectorField]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.pushForwardVectorField_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_trans ``Submission.DifferentialGeometry.Analysis.ODE.pushForwardVectorField_trans

@[simp]
theorem pushForwardVectorField_symm (e : E ≃L[ℝ] F) (f : ℝ → E → E) :
    pushForwardVectorField e.symm (pushForwardVectorField e f) = f := by
  rw [← pushForwardVectorField_trans]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.pushForwardVectorField_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.pushForwardVectorField_symm ``Submission.DifferentialGeometry.Analysis.ODE.pushForwardVectorField_symm

theorem ContinuousLinearEquiv.mapsTo_posTangentConeAt
    (e : E ≃L[ℝ] F) {C : Set E} {x : E} :
    MapsTo e (posTangentConeAt C x) (posTangentConeAt (e '' C) (e x)) := by
  intro v hv
  rcases exists_fun_of_mem_tangentConeAt hv with ⟨ι, l, hl, c, d, hd₀, hdC, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n ↦ e (d n)) ?_ ?_ ?_
  · change _root_.Filter.Tendsto (e ∘ d) l (𝓝 0)
    simpa only [map_zero] using e.continuous.continuousAt.tendsto.comp hd₀
  · filter_upwards [hdC] with n hn
    refine ⟨x + d n, hn, ?_⟩
    simp
  · apply Tendsto.congr' _ (e.continuous.continuousAt.tendsto.comp hcd)
    filter_upwards with n
    simp [NNReal.smul_def]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.mapsTo_posTangentConeAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.mapsTo_posTangentConeAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.mapsTo_posTangentConeAt ``Submission.DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.mapsTo_posTangentConeAt

theorem ContinuousLinearEquiv.image_posTangentConeAt
    (e : E ≃L[ℝ] F) (C : Set E) (x : E) :
    e '' posTangentConeAt C x = posTangentConeAt (e '' C) (e x) := by
  apply Set.Subset.antisymm
  · exact (ContinuousLinearEquiv.mapsTo_posTangentConeAt e).image_subset
  intro v hv
  have hmap := ContinuousLinearEquiv.mapsTo_posTangentConeAt e.symm hv
  refine ⟨e.symm v, ?_, by simp⟩
  simpa using hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.image_posTangentConeAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.image_posTangentConeAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.image_posTangentConeAt ``Submission.DifferentialGeometry.Analysis.ODE.ContinuousLinearEquiv.image_posTangentConeAt

theorem VectorFieldTangentTo.pushForwardVectorField
    {f : ℝ → E → E} {C : Set E} (h : VectorFieldTangentTo f C) (e : E ≃L[ℝ] F) :
    VectorFieldTangentTo (pushForwardVectorField e f) (e '' C) := by
  intro t y hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using ContinuousLinearEquiv.mapsTo_posTangentConeAt e (h t x hx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo.pushForwardVectorField

theorem IsIntegralCurveOn.pushForwardVectorField
    {f : ℝ → E → E} {s : Set ℝ} {gamma : ℝ → E}
    (h : IsIntegralCurveOn gamma f s) (e : E ≃L[ℝ] F) :
    IsIntegralCurveOn (fun t ↦ e (gamma t)) (pushForwardVectorField e f) s := by
  intro t ht
  simpa [Function.comp_def] using
    (e.toContinuousLinearMap.hasFDerivAt (x := gamma t)).comp_hasDerivWithinAt t (h t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.pushForwardVectorField

theorem IsIntegralCurve.pushForwardVectorField
    {f : ℝ → E → E} {gamma : ℝ → E}
    (h : IsIntegralCurve gamma f) (e : E ≃L[ℝ] F) :
    IsIntegralCurve (fun t ↦ e (gamma t)) (pushForwardVectorField e f) := by
  intro t
  simpa [Function.comp_def] using
    (e.toContinuousLinearMap.hasFDerivAt (x := gamma t)).comp_hasDerivAt t (h t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurve.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurve.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurve.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurve.pushForwardVectorField

theorem IsIntegralCurveAt.pushForwardVectorField
    {f : ℝ → E → E} {gamma : ℝ → E} {t₀ : ℝ}
    (h : IsIntegralCurveAt gamma f t₀) (e : E ≃L[ℝ] F) :
    IsIntegralCurveAt (fun t ↦ e (gamma t)) (pushForwardVectorField e f) t₀ := by
  filter_upwards [h] with t ht
  simpa [Function.comp_def] using
    (e.toContinuousLinearMap.hasFDerivAt (x := gamma t)).comp_hasDerivAt t ht

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurveAt.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurveAt.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurveAt.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveAt.pushForwardVectorField

theorem isIntegralCurveOn_pushForwardVectorField_iff
    {f : ℝ → E → E} {s : Set ℝ} {gamma : ℝ → E} (e : E ≃L[ℝ] F) :
    IsIntegralCurveOn (fun t ↦ e (gamma t)) (pushForwardVectorField e f) s ↔
      IsIntegralCurveOn gamma f s := by
  constructor
  · intro h
    have hback := IsIntegralCurveOn.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsIntegralCurveOn.pushForwardVectorField h e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_pushForwardVectorField_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_pushForwardVectorField_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_pushForwardVectorField_iff ``Submission.DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_pushForwardVectorField_iff

theorem isIntegralCurve_pushForwardVectorField_iff
    {f : ℝ → E → E} {gamma : ℝ → E} (e : E ≃L[ℝ] F) :
    IsIntegralCurve (fun t ↦ e (gamma t)) (pushForwardVectorField e f) ↔
      IsIntegralCurve gamma f := by
  constructor
  · intro h
    have hback := IsIntegralCurve.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsIntegralCurve.pushForwardVectorField h e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isIntegralCurve_pushForwardVectorField_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isIntegralCurve_pushForwardVectorField_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isIntegralCurve_pushForwardVectorField_iff ``Submission.DifferentialGeometry.Analysis.ODE.isIntegralCurve_pushForwardVectorField_iff

theorem isIntegralCurveAt_pushForwardVectorField_iff
    {f : ℝ → E → E} {gamma : ℝ → E} {t₀ : ℝ} (e : E ≃L[ℝ] F) :
    IsIntegralCurveAt (fun t ↦ e (gamma t)) (pushForwardVectorField e f) t₀ ↔
      IsIntegralCurveAt gamma f t₀ := by
  constructor
  · intro h
    have hback := IsIntegralCurveAt.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsIntegralCurveAt.pushForwardVectorField h e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isIntegralCurveAt_pushForwardVectorField_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isIntegralCurveAt_pushForwardVectorField_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isIntegralCurveAt_pushForwardVectorField_iff ``Submission.DifferentialGeometry.Analysis.ODE.isIntegralCurveAt_pushForwardVectorField_iff

theorem vectorFieldTangentTo_pushForwardVectorField_iff
    {f : ℝ → E → E} {C : Set E} (e : E ≃L[ℝ] F) :
    VectorFieldTangentTo (pushForwardVectorField e f) (e '' C) ↔
      VectorFieldTangentTo f C := by
  constructor
  · intro h
    have hback := VectorFieldTangentTo.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ VectorFieldTangentTo.pushForwardVectorField h e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.vectorFieldTangentTo_pushForwardVectorField_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.vectorFieldTangentTo_pushForwardVectorField_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.vectorFieldTangentTo_pushForwardVectorField_iff ``Submission.DifferentialGeometry.Analysis.ODE.vectorFieldTangentTo_pushForwardVectorField_iff

theorem IsForwardInvariantForODEOn.pushForwardVectorField
    {f : ℝ → E → E} {C : Set E} {J : Set ℝ}
    (h : IsForwardInvariantForODEOn f C J) (e : E ≃L[ℝ] F) :
    IsForwardInvariantForODEOn (pushForwardVectorField e f) (e '' C) J := by
  intro a b hab hJ gamma hgamma hgammaa
  have hback : IsIntegralCurveOn (fun t ↦ e.symm (gamma t)) f (_root_.Set.Icc a b) := by
    simpa using IsIntegralCurveOn.pushForwardVectorField hgamma e.symm
  have ha : e.symm (gamma a) ∈ C := by
    obtain ⟨x, hx, hxeq⟩ := hgammaa
    simpa [← hxeq] using hx
  have hmap := h a b hab hJ (fun t ↦ e.symm (gamma t)) hback ha
  intro t ht
  exact ⟨e.symm (gamma t), hmap ht, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.pushForwardVectorField

theorem isForwardInvariantForODEOn_pushForwardVectorField_iff
    {f : ℝ → E → E} {C : Set E} {J : Set ℝ} (e : E ≃L[ℝ] F) :
    IsForwardInvariantForODEOn (pushForwardVectorField e f) (e '' C) J ↔
      IsForwardInvariantForODEOn f C J := by
  constructor
  · intro h
    have hback := IsForwardInvariantForODEOn.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsForwardInvariantForODEOn.pushForwardVectorField h e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_pushForwardVectorField_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_pushForwardVectorField_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_pushForwardVectorField_iff ``Submission.DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_pushForwardVectorField_iff

theorem IsForwardInvariantForODE.pushForwardVectorField
    {f : ℝ → E → E} {C : Set E} (h : IsForwardInvariantForODE f C) (e : E ≃L[ℝ] F) :
    IsForwardInvariantForODE (pushForwardVectorField e f) (e '' C) :=
  isForwardInvariantForODEOn_univ.mp
    ((isForwardInvariantForODEOn_univ.mpr h).pushForwardVectorField e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.pushForwardVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.pushForwardVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.pushForwardVectorField ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.pushForwardVectorField

theorem isForwardInvariantForODE_pushForwardVectorField_iff
    {f : ℝ → E → E} {C : Set E} (e : E ≃L[ℝ] F) :
    IsForwardInvariantForODE (pushForwardVectorField e f) (e '' C) ↔
      IsForwardInvariantForODE f C := by
  simpa only [isForwardInvariantForODEOn_univ] using
    isForwardInvariantForODEOn_pushForwardVectorField_iff (J := _root_.Set.univ) (f := f) (C := C) e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_pushForwardVectorField_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_pushForwardVectorField_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_pushForwardVectorField_iff ``Submission.DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_pushForwardVectorField_iff

theorem IsForwardInvariantForODEOn.preimage
    {f : ℝ → F → F} {g : ℝ → E → E} {C : Set F} {J : Set ℝ}
    (h : IsForwardInvariantForODEOn f C J) (L : E →L[ℝ] F)
    (hL : ∀ t ∈ J, ∀ x, L (g t x) = f t (L x)) :
    IsForwardInvariantForODEOn g (L ⁻¹' C) J := by
  intro a b hab hJ γ hγ hinit
  have hcurve : IsIntegralCurveOn (fun t => L (γ t)) f (_root_.Set.Icc a b) := by
    intro t ht
    have hd := L.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
    simpa only [Function.comp_def, hL t (hJ ht)] using hd
  exact h a b hab hJ (fun t => L (γ t)) hcurve hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.preimage ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.preimage


end DifferentialGeometry.Analysis.ODE
