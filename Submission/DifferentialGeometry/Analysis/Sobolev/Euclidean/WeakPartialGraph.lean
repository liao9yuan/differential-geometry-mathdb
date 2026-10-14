import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Product
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.WeakCompactness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "X" => _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω))

theorem ae_hasWeakPartialDeriv_of_tendsto_Lp
    (hp : p ≠ ⊤) (k : Fin d)
    {U V : ℕ → X} {u v : X}
    (hU : _root_.Filter.Tendsto U _root_.Filter.atTop (𝓝 u)) (hV : _root_.Filter.Tendsto V _root_.Filter.atTop (𝓝 v))
    (hweak : ∀ n, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V n (t, x)) (fun x => U n (t, x)) Ω) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω := by
  obtain ⟨σ, hσ, hσU⟩ := Lp.exists_subseq_tendsto_eLpNorm_prodMk_left hp hU
  obtain ⟨τ, hτ, hτV⟩ := Lp.exists_subseq_tendsto_eLpNorm_prodMk_left hp
    (hV.comp hσ.tendsto_atTop)
  have hUi := ae_all_iff.mpr (fun n => (Lp.memLp (U n)).prodMk_left hp)
  have hVi := ae_all_iff.mpr (fun n => (Lp.memLp (V n)).prodMk_left hp)
  have hwi := ae_all_iff.mpr hweak
  filter_upwards [hσU, hτV, hUi, hVi, hwi,
    (Lp.memLp u).prodMk_left hp, (Lp.memLp v).prodMk_left hp]
    with t htU htV htUi htVi htweak htu htv
  exact hasWeakPartialDeriv_of_tendsto_eLpNorm (Fact.out : 1 ≤ p) k
    (fun n => htUi (σ (τ n))) (fun n => htVi (σ (τ n))) htu htv
    (fun n => htweak (σ (τ n))) (htU.comp hτ.tendsto_atTop) htV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_Lp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_Lp

theorem isClosed_setOf_ae_hasWeakPartialDeriv
    (hp : p ≠ ⊤) (k : Fin d) :
    IsClosed {w : X × X | ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => w.2 (t, x)) (fun x => w.1 (t, x)) Ω} := by
  apply isSeqClosed_iff_isClosed.mp
  intro w v hw hlim
  exact ae_hasWeakPartialDeriv_of_tendsto_Lp hp k
    ((continuous_fst.tendsto v).comp hlim) ((continuous_snd.tendsto v).comp hlim) hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_ae_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_ae_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_ae_hasWeakPartialDeriv ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_ae_hasWeakPartialDeriv

end DifferentialGeometry.Analysis.Sobolev.Euclidean


namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω))

omit [Fact (1 ≤ p)] in
private theorem coeFn_smul_add (a b : ℝ) (u v : X) :
    (a • u + b • v : X) =ᵐ[μ.prod (volume.restrict Ω)]
      fun z => a * u z + b * v z := by
  filter_upwards [Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u, Lp.coeFn_smul b v]
    with z hz ha hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz ha hb
  rw [hz, ha, hb]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.coeFn_smul_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.coeFn_smul_add target :: scope.openDecls } }

private theorem integral_linear_combination_mul
    {f g : E → ℝ}
    (hf : _root_.MeasureTheory.MemLp f p (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g p (volume.restrict Ω))
    {φ : E → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (a b : ℝ) :
    (∫ x in Ω, (a * f x + b * g x) * φ x) =
      a * (∫ x in Ω, f x * φ x) + b * (∫ x in Ω, g x * φ x) := by
  have hfφ : _root_.MeasureTheory.Integrable (fun x => f x * φ x) (volume.restrict Ω) :=
    (hf.locallyIntegrable (Fact.out : 1 ≤ p)).integrable_smul_right_of_hasCompactSupport hφ hφc
  have hgφ : _root_.MeasureTheory.Integrable (fun x => g x * φ x) (volume.restrict Ω) :=
    (hg.locallyIntegrable (Fact.out : 1 ≤ p)).integrable_smul_right_of_hasCompactSupport hφ hφc
  simp_rw [add_mul, mul_assoc]
  rw [_root_.MeasureTheory.integral_add (hfφ.const_mul a) (hgφ.const_mul b), _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_linear_combination_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_linear_combination_mul target :: scope.openDecls } }

theorem convex_setOf_ae_hasWeakPartialDeriv
    (hp : p ≠ ⊤) (k : Fin d) :
    Convex ℝ {w : X × X | ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => w.2 (t, x)) (fun x => w.1 (t, x)) Ω} := by
  intro A hA B hB a b _ _ _
  have hleft := Measure.ae_ae_of_ae_prod (coeFn_smul_add a b A.1 B.1)
  have hright := Measure.ae_ae_of_ae_prod (coeFn_smul_add a b A.2 B.2)
  filter_upwards [hA, hB, hleft, hright,
    (Lp.memLp A.1).prodMk_left hp, (Lp.memLp A.2).prodMk_left hp,
    (Lp.memLp B.1).prodMk_left hp, (Lp.memLp B.2).prodMk_left hp]
    with t htA htB htleft htright hA₁ hA₂ hB₁ hB₂
  intro φ hφ hφc hφs
  have hdφ : Continuous (fun x : E => fderiv ℝ φ x (EuclideanSpace.single k 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc := hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  change (∫ x in Ω, (a • A.1 + b • B.1 : X) (t, x) *
    fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      -∫ x in Ω, (a • A.2 + b • B.2 : X) (t, x) * φ x
  calc
    _ = ∫ x in Ω, (a * A.1 (t, x) + b * B.1 (t, x)) *
        fderiv ℝ φ x (EuclideanSpace.single k 1) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [htleft] with x hx
      rw [hx]
    _ = a * (∫ x in Ω, A.1 (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) +
        b * (∫ x in Ω, B.1 (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) :=
      integral_linear_combination_mul hA₁ hB₁ hdφ hdφc a b
    _ = -(a * (∫ x in Ω, A.2 (t, x) * φ x) + b * (∫ x in Ω, B.2 (t, x) * φ x)) := by
      rw [htA φ hφ hφc hφs, htB φ hφ hφc hφs]
      ring
    _ = -(∫ x in Ω, (a * A.2 (t, x) + b * B.2 (t, x)) * φ x) := by
      rw [integral_linear_combination_mul hA₂ hB₂ hφ.continuous hφc a b]
    _ = _ := by
      congr 1
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [htright] with x hx
      rw [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.convex_setOf_ae_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.convex_setOf_ae_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.convex_setOf_ae_hasWeakPartialDeriv ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.convex_setOf_ae_hasWeakPartialDeriv

theorem isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv
    (hp : p ≠ ⊤) (k : Fin d) :
    IsClosed ((toWeakSpace ℝ (X × X)) ''
      {w : X × X | ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => w.2 (t, x)) (fun x => w.1 (t, x)) Ω}) := by
  rw [← closure_eq_iff_isClosed]
  rw [← (convex_setOf_ae_hasWeakPartialDeriv hp k).toWeakSpace_closure ℝ,
    (isClosed_setOf_ae_hasWeakPartialDeriv hp k).closure_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv

theorem ae_hasWeakPartialDeriv_of_tendsto_weak
    (hp : p ≠ ⊤) (k : Fin d)
    {A : Type*} {l : Filter A} [_root_.Filter.NeBot l]
    {U V : A → X} {u v : X}
    (hlim : _root_.Filter.Tendsto (fun a => toWeakSpace ℝ (X × X) (U a, V a)) l
      (𝓝 (toWeakSpace ℝ (X × X) (u, v))))
    (hweak : ∀ᶠ a in l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V a (t, x)) (fun x => U a (t, x)) Ω) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω := by
  have hmem := (isClosed_toWeakSpace_setOf_ae_hasWeakPartialDeriv hp k).mem_of_tendsto hlim
    (hweak.mono fun a ha => ⟨(U a, V a), ha, rfl⟩)
  obtain ⟨w, hw, heq⟩ := hmem
  have hEq : w = (u, v) := (toWeakSpace ℝ (X × X)).injective heq
  subst w
  exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_weak then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_weak"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_weak ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_hasWeakPartialDeriv_of_tendsto_weak

end DifferentialGeometry.Analysis.Sobolev.Euclidean


namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "X" => _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))

private theorem tendsto_weak_prod_of_tendsto_inner
    {A : Type*} {l : Filter A} {U V : A → X} {u v : X}
    (hU : _root_.Filter.Tendsto U l (𝓝 u))
    (hV : ∀ z, _root_.Filter.Tendsto (fun a => _root_.Inner.inner ℝ (V a) z) l (𝓝 (_root_.Inner.inner ℝ v z))) :
    _root_.Filter.Tendsto (fun a => toWeakSpace ℝ (X × X) (U a, V a)) l
      (𝓝 (toWeakSpace ℝ (X × X) (u, v))) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _
    (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℝ (X × X)))).mpr
  intro F
  change _root_.Filter.Tendsto (fun a => F (U a, V a)) l (𝓝 (F (u, v)))
  let F₁ : X →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ X X)
  let F₂ : X →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inr ℝ X X)
  have hF₂ (w : X) : F₂ w = _root_.Inner.inner ℝ w ((_root_.InnerProductSpace.toDual ℝ X).symm F₂) := by
    rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
  have h₂ : _root_.Filter.Tendsto (fun a => F₂ (V a)) l (𝓝 (F₂ v)) := by
    simpa only [hF₂] using hV ((_root_.InnerProductSpace.toDual ℝ X).symm F₂)
  have hsplit (x y : X) : F (x, y) = F₁ x + F₂ y := by
    change F (x, y) = F (x, 0) + F (0, y)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simpa only [hsplit, Function.comp_apply] using ((F₁.continuous.tendsto u).comp hU).add h₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_weak_prod_of_tendsto_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_weak_prod_of_tendsto_inner target :: scope.openDecls } }

theorem exists_ae_hasWeakPartialDeriv_of_norm_bounded
    [TopologicalSpace.SeparableSpace X]
    (k : Fin d) {U V : ℕ → X} {u : X} {C : ℝ}
    (hU : _root_.Filter.Tendsto U _root_.Filter.atTop (𝓝 u)) (hV : ∀ n, ‖V n‖ ≤ C)
    (hweak : ∀ n, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V n (t, x)) (fun x => U n (t, x)) Ω) :
    ∃ v : X, ‖v‖ ≤ C ∧ ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω := by
  obtain ⟨σ, v, hσ, hlim⟩ :=
    DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded V hV
  have hC : 0 ≤ C := (norm_nonneg (V 0)).trans (hV 0)
  have hvC : ‖v‖ ≤ C := by
    have hvv : _root_.Inner.inner ℝ v v ≤ C * ‖v‖ := le_of_tendsto (hlim v) (Eventually.of_forall fun n =>
      (real_inner_le_norm (V (σ n)) v).trans (mul_le_mul_of_nonneg_right (hV (σ n)) (norm_nonneg v)))
    rw [real_inner_self_eq_norm_sq] at hvv
    nlinarith [norm_nonneg v]
  refine ⟨v, hvC, ?_⟩
  apply ae_hasWeakPartialDeriv_of_tendsto_weak (by norm_num) k
    (tendsto_weak_prod_of_tendsto_inner (hU.comp hσ.tendsto_atTop) hlim)
  exact Eventually.of_forall fun n => hweak (σ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_ae_hasWeakPartialDeriv_of_norm_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_ae_hasWeakPartialDeriv_of_norm_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_ae_hasWeakPartialDeriv_of_norm_bounded ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_ae_hasWeakPartialDeriv_of_norm_bounded

end DifferentialGeometry.Analysis.Sobolev.Euclidean

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "X" => _root_.MeasureTheory.Lp ℝ p (volume.restrict Ω)

theorem isClosed_setOf_hasWeakPartialDeriv (i : Fin d) :
    IsClosed {w : X × X | DeGiorgi.HasWeakPartialDeriv i w.2 w.1 Ω} := by
  apply isSeqClosed_iff_isClosed.mp
  intro w v hw hlim
  exact hasWeakPartialDeriv_of_tendsto_eLpNorm (Fact.out : 1 ≤ p) i
    (fun n => Lp.memLp (w n).1) (fun n => Lp.memLp (w n).2)
    (Lp.memLp v.1) (Lp.memLp v.2) hw
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (w n).1) v.1).mp
      ((continuous_fst.tendsto v).comp hlim))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (w n).2) v.2).mp
      ((continuous_snd.tendsto v).comp hlim))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_hasWeakPartialDeriv ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_setOf_hasWeakPartialDeriv

theorem hasWeakPartialDeriv_of_tendsto_Lp
    (i : Fin d) {A : Type*} {l : Filter A} [_root_.Filter.NeBot l] {U V : A → X} {u v : X}
    (hU : _root_.Filter.Tendsto U l (𝓝 u)) (hV : _root_.Filter.Tendsto V l (𝓝 v))
    (hweak : ∀ᶠ a in l, DeGiorgi.HasWeakPartialDeriv i (V a) (U a) Ω) :
    DeGiorgi.HasWeakPartialDeriv i v u Ω :=
  (isClosed_setOf_hasWeakPartialDeriv i).mem_of_tendsto (hU.prodMk_nhds hV) hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_Lp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_Lp

private theorem mapsTo_of_continuousOn_of_ae_mem
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [TopologicalSpace B]
    {μ : _root_.MeasureTheory.Measure A} [μ.IsOpenPosMeasure] {s : Set A} {C : Set B} {f : A → B}
    (hC : IsClosed C) (hf : ContinuousOn f s) (hs : s ⊆ closure (interior s))
    (hae : ∀ᵐ t ∂μ.restrict s, f t ∈ C) : _root_.Set.MapsTo f s C := by
  have hi : _root_.Set.MapsTo f (interior s) C := by
    have hbad : IsOpen (interior s ∩ f ⁻¹' Cᶜ) := by
      apply isOpen_iff_mem_nhds.mpr
      intro x hx
      exact _root_.Filter.inter_mem (isOpen_interior.mem_nhds hx.1)
        ((hf.continuousAt (_root_.Filter.mem_of_superset (isOpen_interior.mem_nhds hx.1) interior_subset))
          (hC.isOpen_compl.mem_nhds hx.2))
    have hnull : μ (interior s ∩ f ⁻¹' Cᶜ) = 0 := by
      have h := _root_.MeasureTheory.ae_imp_of_ae_restrict hae
      have hh : ∀ᵐ x ∂μ, x ∉ interior s ∩ f ⁻¹' Cᶜ := by
        filter_upwards [h] with x hx
        exact fun hx' => hx'.2 (hx (interior_subset hx'.1))
      simpa only [_root_.MeasureTheory.ae_iff, _root_.Classical.not_not, _root_.Set.ofPred_mem_eq] using hh
    have hempty := hbad.eq_empty_of_measure_zero hnull
    intro x hx
    by_contra hnot
    have : x ∈ interior s ∩ f ⁻¹' Cᶜ := ⟨hx, hnot⟩
    simp only [hempty, _root_.Set.mem_empty_iff_false] at this
  intro x hx
  have : _root_.Filter.NeBot (𝓝[interior s] x) := mem_closure_iff_nhdsWithin_neBot.mp (hs hx)
  exact hC.mem_of_tendsto ((hf x hx).mono interior_subset)
    (by
      filter_upwards [self_mem_nhdsWithin (a := x) (s := interior s)] with y hy
      exact hi hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.mapsTo_of_continuousOn_of_ae_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.mapsTo_of_continuousOn_of_ae_mem target :: scope.openDecls } }

theorem hasWeakPartialDeriv_of_continuousOn_Lp
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    {μ : _root_.MeasureTheory.Measure A} [μ.IsOpenPosMeasure] {s : Set A}
    (hs : s ⊆ closure (interior s)) (i : Fin d) (U V : A → X)
    (hU : ContinuousOn U s) (hV : ContinuousOn V s)
    (hweak : ∀ᵐ t ∂μ.restrict s, DeGiorgi.HasWeakPartialDeriv i (V t) (U t) Ω) :
    ∀ t ∈ s, DeGiorgi.HasWeakPartialDeriv i (V t) (U t) Ω :=
  mapsTo_of_continuousOn_of_ae_mem (isClosed_setOf_hasWeakPartialDeriv i)
    (hU.prodMk hV) hs hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_continuousOn_Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_continuousOn_Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_continuousOn_Lp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_continuousOn_Lp

end DifferentialGeometry.Analysis.Sobolev.Euclidean
