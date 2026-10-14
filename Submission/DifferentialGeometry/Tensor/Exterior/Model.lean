import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Submission.DifferentialGeometry.Tensor.Alternating.Wedge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousAlternatingMap _root_.Submission.ContinuousAlternatingMap
open scoped _root_.ContDiff

namespace DifferentialGeometry
namespace DifferentialForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m k l : ℕ}

theorem contDiffOn_extDeriv_infty {s : Set E} (alpha : E → E [⋀^Fin n]→L[ℝ] F)
    (hAlpha : ContDiffOn ℝ ∞ alpha s) (hs : IsOpen s) :
    ContDiffOn ℝ ∞ (fun x => extDeriv alpha x) s := by
  have hf : ContDiffOn ℝ ∞ (fderiv ℝ alpha) s := hAlpha.fderiv_of_isOpen hs (by simp)
  have hc : ContDiff ℝ ∞ (fun L : E →L[ℝ] E [⋀^Fin n]→L[ℝ] F =>
      alternatizeUncurryFinCLM ℝ E F L) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := E →L[ℝ] E [⋀^Fin n]→L[ℝ] F)
      (F := E [⋀^Fin (n + 1)]→L[ℝ] F)
      (_root_.ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := n) ℝ E F)
  exact hc.comp_contDiffOn hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv_infty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv_infty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv_infty ``Submission.DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv_infty

theorem contDiffOn_extDeriv {s : Set E} (alpha : E → E [⋀^Fin n]→L[ℝ] F)
    (hAlpha : ContDiffOn ℝ ⊤ alpha s) (hs : IsOpen s) :
    ContDiffOn ℝ ⊤ (fun x => extDeriv alpha x) s := by
  have hf : ContDiffOn ℝ ⊤ (fderiv ℝ alpha) s := hAlpha.fderiv_of_isOpen hs le_top
  have hc : ContDiff ℝ ⊤ (fun L : E →L[ℝ] E [⋀^Fin n]→L[ℝ] F =>
      alternatizeUncurryFinCLM ℝ E F L) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := E →L[ℝ] E [⋀^Fin n]→L[ℝ] F)
      (F := E [⋀^Fin (n + 1)]→L[ℝ] F)
      (_root_.ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := n) ℝ E F)
  exact hc.comp_contDiffOn hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv ``Submission.DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv

theorem contDiffOn_wedge_product_infty {s : Set E} (a : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (b : E → E [⋀^Fin l]→L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s) :
    ContDiffOn ℝ ∞ (fun x => a x ∧[ℝ] b x) s := by
  let hW := isBoundedBilinearMap_wedgeProduct (M := E) (m := k) (n := l)
    (ContinuousLinearMap.mul ℝ ℝ)
  have hWdiff : ContDiff ℝ ∞ (fun p : (E [⋀^Fin k]→L[ℝ] ℝ) ×
      (E [⋀^Fin l]→L[ℝ] ℝ) => wedgeProduct p.1 p.2 (ContinuousLinearMap.mul ℝ ℝ)) :=
    IsBoundedBilinearMap.contDiff (n := ∞) hW
  convert hWdiff.comp_contDiffOn (ha.prodMk hb) using 1
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product_infty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product_infty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product_infty ``Submission.DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product_infty

theorem contDiffOn_wedge_product {s : Set E} (a : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (b : E → E [⋀^Fin l]→L[ℝ] ℝ) (ha : ContDiffOn ℝ ⊤ a s) (hb : ContDiffOn ℝ ⊤ b s) :
    ContDiffOn ℝ ⊤ (fun x => a x ∧[ℝ] b x) s := by
  let hW := isBoundedBilinearMap_wedgeProduct (M := E) (m := k) (n := l)
    (ContinuousLinearMap.mul ℝ ℝ)
  have hWdiff : ContDiff ℝ ⊤ (fun p : (E [⋀^Fin k]→L[ℝ] ℝ) ×
      (E [⋀^Fin l]→L[ℝ] ℝ) => wedgeProduct p.1 p.2 (ContinuousLinearMap.mul ℝ ℝ)) :=
    IsBoundedBilinearMap.contDiff (n := ⊤) hW
  convert hWdiff.comp_contDiffOn (ha.prodMk hb) using 1
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product ``Submission.DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product

theorem contDiffOn_pullback_infty {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {s : Set E} {t : Set E'} (f : E → E')
    (alpha : E' → E' [⋀^Fin n]→L[ℝ] F) (hf : ContDiffOn ℝ ∞ f s)
    (hAlpha : ContDiffOn ℝ ∞ alpha t)
    (hst : Set.MapsTo f s t) (hs : IsOpen s) :
    ContDiffOn ℝ ∞ (fun x => (alpha (f x)).compContinuousLinearMap (fderiv ℝ f x)) s := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  have h₁ : ContDiffOn ℝ ∞ (fun x =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ f x) : (E' [⋀^Fin n]→L[ℝ] F) →L[ℝ]
        (E [⋀^Fin n]→L[ℝ] F))) s :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real
      (F₁ := E) (F₁' := E') (F₂ := F) (ι := Fin n)).of_le (by simp) |>.comp_contDiffOn hfd
  have h₂ : ContDiffOn ℝ ∞ (fun x => alpha (f x)) s := hAlpha.comp hf hst
  change ContDiffOn ℝ ∞
    (fun x => (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ f x)) (alpha (f x))) s
  exact h₁.clm_apply h₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.contDiffOn_pullback_infty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.contDiffOn_pullback_infty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.contDiffOn_pullback_infty ``Submission.DifferentialGeometry.DifferentialForm.contDiffOn_pullback_infty

theorem contDiffOn_pullback {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {s : Set E} {t : Set E'} (f : E → E')
    (alpha : E' → E' [⋀^Fin n]→L[ℝ] F) (hf : ContDiffOn ℝ ⊤ f s)
    (hAlpha : ContDiffOn ℝ ⊤ alpha t)
    (hst : Set.MapsTo f s t) (hs : IsOpen s) :
    ContDiffOn ℝ ⊤ (fun x => (alpha (f x)).compContinuousLinearMap (fderiv ℝ f x)) s := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs le_top
  have h₁ : ContDiffOn ℝ ⊤ (fun x =>
      (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ f x) : (E' [⋀^Fin n]→L[ℝ] F) →L[ℝ]
        (E [⋀^Fin n]→L[ℝ] F))) s :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real
      (F₁ := E) (F₁' := E') (F₂ := F) (ι := Fin n)).comp_contDiffOn hfd
  have h₂ : ContDiffOn ℝ ⊤ (fun x => alpha (f x)) s := hAlpha.comp hf hst
  change ContDiffOn ℝ ⊤
    (fun x => (_root_.ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ f x)) (alpha (f x))) s
  exact h₁.clm_apply h₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.contDiffOn_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.contDiffOn_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.contDiffOn_pullback ``Submission.DifferentialGeometry.DifferentialForm.contDiffOn_pullback

theorem wedge_product_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (g : E [⋀^Fin k]→L[ℝ] ℝ) (h : E [⋀^Fin l]→L[ℝ] ℝ)
    (A : E' →L[ℝ] E) :
    (g ∧[ℝ] h).compContinuousLinearMap A =
      (g.compContinuousLinearMap A) ∧[ℝ] (h.compContinuousLinearMap A) := by
  ext v
  simp only [_root_.ContinuousAlternatingMap.compContinuousLinearMap_apply, wedge_product_def]
  change uncurryFinAdd (ContinuousLinearMap.compContinuousAlternatingMap₂
    (ContinuousLinearMap.mul ℝ ℝ) g h) (A ∘ v) =
      uncurryFinAdd (ContinuousLinearMap.compContinuousAlternatingMap₂
        (ContinuousLinearMap.mul ℝ ℝ) (g.compContinuousLinearMap A)
        (h.compContinuousLinearMap A)) v
  rw [uncurryFinAdd, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  refine Quotient.inductionOn' σ ?_
  intro σ'
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    _root_.ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap ``Submission.DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap

theorem domDomCongr_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (σ : Fin m ≃ Fin n) (L : E [⋀^Fin m]→L[ℝ] F) (A : E' →L[ℝ] E) :
    (domDomCongr σ L).compContinuousLinearMap A =
      domDomCongr σ (L.compContinuousLinearMap A) := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.domDomCongr_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.domDomCongr_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.domDomCongr_compContinuousLinearMap ``Submission.DifferentialGeometry.DifferentialForm.domDomCongr_compContinuousLinearMap

theorem constOfIsEmpty_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (y : F) (A : E' →L[ℝ] E) :
    (_root_.ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) y).compContinuousLinearMap A =
      constOfIsEmpty ℝ E' (Fin 0) y := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.constOfIsEmpty_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.constOfIsEmpty_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.constOfIsEmpty_compContinuousLinearMap ``Submission.DifferentialGeometry.DifferentialForm.constOfIsEmpty_compContinuousLinearMap

private theorem ofSubsingleton_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (g : E →L[ℝ] F) (A : E' →L[ℝ] E) :
    (_root_.ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) g).compContinuousLinearMap A =
      ofSubsingleton ℝ E' F (0 : Fin 1) (g.comp A) := by
  ext v
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.ofSubsingleton_compContinuousLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.ofSubsingleton_compContinuousLinearMap target :: scope.openDecls } }

end DifferentialForm
end DifferentialGeometry

end
