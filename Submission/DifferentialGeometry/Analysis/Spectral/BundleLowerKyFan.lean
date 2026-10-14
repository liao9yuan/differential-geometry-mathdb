import Submission.DifferentialGeometry.Analysis.Spectral.LowerKyFan
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.SpectralBounds
import Submission.DifferentialGeometry.Bundle.OrthonormalFrame
import Mathlib.Analysis.Matrix.Hermitian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Filter _root_.Set
open scoped _root_.Topology _root_.InnerProductSpace _root_.BigOperators

private def matrixToCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap

run_cmd do
  let target := ``Submission.matrixToCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `matrixToCLM target :: scope.openDecls } }

private theorem continuous_matrixToCLM (n : ℕ) : Continuous (matrixToCLM n) :=
  (matrixToCLM n).continuous_of_finiteDimensional

run_cmd do
  let target := ``Submission.continuous_matrixToCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `continuous_matrixToCLM target :: scope.openDecls } }

private theorem continuousWithinAt_lowerKyFanSum
    {Z : Type*} [TopologicalSpace Z] {s : Set Z} {z : Z} {n k : ℕ}
    {A : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hA : ContinuousWithinAt A s z) (hsymm : ∀ y, (A y).IsSymmetric)
    (hk : k ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    ContinuousWithinAt (fun y => (hsymm y).lowerKyFanSum k) s z := by
  have hsub : ContinuousWithinAt (fun y =>
      (⟨A y, hsymm y⟩ : {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) //
        T.IsSymmetric})) s z := tendsto_subtype_rng.mpr hA
  exact (LinearMap.IsSymmetric.continuous_lowerKyFanSum k hk).continuousAt.comp_continuousWithinAt hsub

run_cmd do
  let target := ``Submission.continuousWithinAt_lowerKyFanSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `continuousWithinAt_lowerKyFanSum target :: scope.openDecls } }

private theorem toEuclideanLin_toMatrix_repr
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {n : ℕ} (basis : OrthonormalBasis (Fin n) ℝ W) (A : W →ₗ[ℝ] W) (x : W) :
    Matrix.toEuclideanLin (LinearMap.toMatrix basis.toBasis basis.toBasis A)
      (basis.repr x) = basis.repr (A x) := by
  apply PiLp.ext
  intro i
  exact congrFun (LinearMap.toMatrix_mulVec_repr basis.toBasis basis.toBasis A x) i

run_cmd do
  let target := ``Submission.toEuclideanLin_toMatrix_repr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `toEuclideanLin_toMatrix_repr target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
  [∀ x, FiniteDimensional ℝ (V x)]

open _root_.ContinuousWithinAt in
theorem ContinuousWithinAt.lowerKyFanSum_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z} {z₀ : Z}
    {A : ∀ z, V (b z) →L[ℝ] V (b z)}
    (hA : ContinuousWithinAt (fun z =>
      (TotalSpace.mk' (F →L[ℝ] F) (b z) (A z) :
        _root_.Bundle.TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) s z₀)
    (hsymm : ∀ z, (A z).IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ (V (b z₀))) :
    ContinuousWithinAt (fun z => (hsymm z).lowerKyFanSum k) s z₀ := by
  classical
  have hb : ContinuousWithinAt b s z₀ := by
    rw [continuousWithinAt_hom_bundle] at hA
    exact hA.1
  let n := Module.finrank ℝ (V (b z₀))
  let v := stdOrthonormalBasis ℝ (V (b z₀))
  obtain ⟨U, hU, hbU, e, heCont, he, -⟩ :=
    exists_continuous_orthonormal_sections (F := F) (b z₀) v v.orthonormal
  let C : Z → Matrix (Fin n) (Fin n) ℝ :=
    fun z i j => ⟪e i (b z), A z (e j (b z))⟫_ℝ
  let B : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun z => matrixToCLM n (C z)
  have hC : ContinuousWithinAt C s z₀ := by
    apply continuousWithinAt_pi.2
    intro i
    apply continuousWithinAt_pi.2
    intro j
    have hei := ((heCont i).continuousAt (hU.mem_nhds hbU)).comp_continuousWithinAt hb
    have hej := ((heCont j).continuousAt (hU.mem_nhds hbU)).comp_continuousWithinAt hb
    exact hei.inner_bundle (hA.clm_bundle_apply hej)
  have hB : ContinuousWithinAt B s z₀ :=
    (continuous_matrixToCLM n).continuousAt.comp_continuousWithinAt hC
  have hBsymm : ∀ z, (B z).IsSymmetric := by
    intro z
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ext i j
    change ⟪e j (b z), A z (e i (b z))⟫_ℝ = ⟪e i (b z), A z (e j (b z))⟫_ℝ
    rw [real_inner_comm]
    exact hsymm z _ _
  have hkB : k ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hk
  have hspec : ContinuousWithinAt (fun z => (hBsymm z).lowerKyFanSum k) s z₀ :=
    continuousWithinAt_lowerKyFanSum hB hBsymm hkB
  have heq : ∀ z, b z ∈ U →
      (hsymm z).lowerKyFanSum k = (hBsymm z).lowerKyFanSum k := by
    intro z hz
    have hdim : Module.finrank ℝ (V (b z)) = n := by
      let ex := (_root_.FiberBundle.trivializationAt F V (b z)).continuousLinearEquivAt ℝ (b z)
        (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b z))
      let ey := (_root_.FiberBundle.trivializationAt F V (b z₀)).continuousLinearEquivAt ℝ (b z₀)
        (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b z₀))
      exact ex.toLinearEquiv.finrank_eq.trans ey.toLinearEquiv.finrank_eq.symm
    let basis : OrthonormalBasis (Fin n) ℝ (V (b z)) :=
      OrthonormalBasis.mk (he (b z) hz)
        ((he (b z) hz).linearIndependent.span_eq_top_of_card_eq_finrank'
          (by simp only [Fintype.card_fin, hdim]; rfl)).ge
    have hmat : C z = LinearMap.toMatrix basis.toBasis basis.toBasis (A z).toLinearMap := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
      simp only [C, basis, OrthonormalBasis.coe_mk]
      rfl
    have hcomm : ∀ x, B z (basis.repr x) = basis.repr (A z x) := by
      intro x
      change Matrix.toEuclideanLin (C z) (basis.repr x) = basis.repr (A z x)
      rw [hmat]
      exact toEuclideanLin_toMatrix_repr basis (A z).toLinearMap x
    exact (hsymm z).lowerKyFanSum_eq_of_intertwining (hBsymm z) basis.repr hcomm
      (hk.trans_eq hdim.symm)
  apply hspec.congr_of_eventuallyEq
  · filter_upwards [hb.eventually (hU.mem_nhds hbU)] with z hz
    exact heq z hz
  · exact heq z₀ hbU

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousWithinAt
  let env ← Lean.getEnv
  if env.contains `ContinuousWithinAt.lowerKyFanSum_bundle then
    throwError "Refusing to shadow existing declaration ContinuousWithinAt.lowerKyFanSum_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousWithinAt.lowerKyFanSum_bundle ``Submission.ContinuousWithinAt.lowerKyFanSum_bundle

open _root_.ContinuousOn in
theorem ContinuousOn.lowerKyFanSum_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z}
    {A : ∀ z, V (b z) →L[ℝ] V (b z)}
    (hA : ContinuousOn (fun z =>
      (TotalSpace.mk' (F →L[ℝ] F) (b z) (A z) :
        _root_.Bundle.TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) s)
    (hsymm : ∀ z, (A z).IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ F) :
    ContinuousOn (fun z => (hsymm z).lowerKyFanSum k) s := by
  intro z hz
  let e := (_root_.FiberBundle.trivializationAt F V (b z)).continuousLinearEquivAt ℝ (b z)
    (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b z))
  exact (hA z hz).lowerKyFanSum_bundle hsymm
    (hk.trans_eq e.toLinearEquiv.finrank_eq.symm)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.lowerKyFanSum_bundle then
    throwError "Refusing to shadow existing declaration ContinuousOn.lowerKyFanSum_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.lowerKyFanSum_bundle ``Submission.ContinuousOn.lowerKyFanSum_bundle

open _root_.ContinuousWithinAt in
theorem ContinuousWithinAt.iInf_rayleighQuotient_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z} {z₀ : Z}
    {A : ∀ z, V (b z) →L[ℝ] V (b z)}
    (hA : ContinuousWithinAt (fun z =>
      (TotalSpace.mk' (F →L[ℝ] F) (b z) (A z) :
        _root_.Bundle.TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) s z₀) :
    ContinuousWithinAt (fun z => ⨅ v : {v : V (b z) // v ≠ 0},
      (A z).rayleighQuotient v) s z₀ := by
  classical
  have hb : ContinuousWithinAt b s z₀ := by
    rw [continuousWithinAt_hom_bundle] at hA
    exact hA.1
  let n := Module.finrank ℝ (V (b z₀))
  let v := stdOrthonormalBasis ℝ (V (b z₀))
  obtain ⟨U, hU, hbU, e, heCont, he, -⟩ :=
    exists_continuous_orthonormal_sections (F := F) (b z₀) v v.orthonormal
  let C : Z → Matrix (Fin n) (Fin n) ℝ :=
    fun z i j => ⟪e i (b z), A z (e j (b z))⟫_ℝ
  let B : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun z => matrixToCLM n (C z)
  have hC : ContinuousWithinAt C s z₀ := by
    apply continuousWithinAt_pi.2
    intro i
    apply continuousWithinAt_pi.2
    intro j
    have hei := ((heCont i).continuousAt (hU.mem_nhds hbU)).comp_continuousWithinAt hb
    have hej := ((heCont j).continuousAt (hU.mem_nhds hbU)).comp_continuousWithinAt hb
    exact hei.inner_bundle (hA.clm_bundle_apply hej)
  have hB : ContinuousWithinAt B s z₀ :=
    (continuous_matrixToCLM n).continuousAt.comp_continuousWithinAt hC
  have hspec : ContinuousWithinAt (fun z => ⨅ v : {v : EuclideanSpace ℝ (Fin n) // v ≠ 0},
      (B z).rayleighQuotient v) s z₀ :=
    (ContinuousLinearMap.continuous_iInf_rayleighQuotient
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))).continuousAt.comp_continuousWithinAt hB
  have heq : ∀ z, b z ∈ U →
      (⨅ v : {v : V (b z) // v ≠ 0}, (A z).rayleighQuotient v) =
        ⨅ v : {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}, (B z).rayleighQuotient v := by
    intro z hz
    have hdim : Module.finrank ℝ (V (b z)) = n := by
      let ex := (_root_.FiberBundle.trivializationAt F V (b z)).continuousLinearEquivAt ℝ (b z)
        (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b z))
      let ey := (_root_.FiberBundle.trivializationAt F V (b z₀)).continuousLinearEquivAt ℝ (b z₀)
        (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b z₀))
      exact ex.toLinearEquiv.finrank_eq.trans ey.toLinearEquiv.finrank_eq.symm
    let basis : OrthonormalBasis (Fin n) ℝ (V (b z)) :=
      OrthonormalBasis.mk (he (b z) hz)
        ((he (b z) hz).linearIndependent.span_eq_top_of_card_eq_finrank'
          (by simp only [Fintype.card_fin, hdim]; rfl)).ge
    have hmat : C z = LinearMap.toMatrix basis.toBasis basis.toBasis (A z).toLinearMap := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
      simp only [C, basis, OrthonormalBasis.coe_mk]
      rfl
    have hcomm : ∀ x, B z (basis.repr x) = basis.repr (A z x) := by
      intro x
      change Matrix.toEuclideanLin (C z) (basis.repr x) = basis.repr (A z x)
      rw [hmat]
      exact toEuclideanLin_toMatrix_repr basis (A z).toLinearMap x
    let en : {v : V (b z) // v ≠ 0} ≃
        {v : EuclideanSpace ℝ (Fin n) // v ≠ 0} :=
      basis.repr.toEquiv.subtypeEquiv (fun v => by
        change v ≠ 0 ↔ basis.repr v ≠ 0
        exact not_congr basis.repr.map_eq_zero_iff.symm)
    apply en.iInf_congr
    intro v
    change (B z).rayleighQuotient (basis.repr v.1) = (A z).rayleighQuotient v.1
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      hcomm, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]
  apply hspec.congr_of_eventuallyEq
  · filter_upwards [hb.eventually (hU.mem_nhds hbU)] with z hz
    exact heq z hz
  · exact heq z₀ hbU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousWithinAt.iInf_rayleighQuotient_bundle then
    throwError "Refusing to shadow existing declaration ContinuousWithinAt.iInf_rayleighQuotient_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousWithinAt.iInf_rayleighQuotient_bundle ``Submission.ContinuousWithinAt.iInf_rayleighQuotient_bundle

open _root_.ContinuousOn in
theorem ContinuousOn.iInf_rayleighQuotient_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z}
    {A : ∀ z, V (b z) →L[ℝ] V (b z)}
    (hA : ContinuousOn (fun z =>
      (TotalSpace.mk' (F →L[ℝ] F) (b z) (A z) :
        _root_.Bundle.TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) s) :
    ContinuousOn (fun z => ⨅ v : {v : V (b z) // v ≠ 0},
      (A z).rayleighQuotient v) s :=
  fun z hz => (hA z hz).iInf_rayleighQuotient_bundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.iInf_rayleighQuotient_bundle then
    throwError "Refusing to shadow existing declaration ContinuousOn.iInf_rayleighQuotient_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.iInf_rayleighQuotient_bundle ``Submission.ContinuousOn.iInf_rayleighQuotient_bundle


end
