import Submission.DifferentialGeometry.Analysis.Integration.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem tendsto_dual_of_tendsto_inner
    {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {l : Filter A} {u : A → H} {u₀ : H}
    (hu : ∀ z, _root_.Filter.Tendsto (fun a => _root_.Inner.inner ℝ (u a) z) l (𝓝 (_root_.Inner.inner ℝ u₀ z)))
    (F : H →L[ℝ] ℝ) :
    Tendsto (fun a => F (u a)) l (𝓝 (F u₀)) := by
  have hF (w : H) : F w = _root_.Inner.inner ℝ w ((_root_.InnerProductSpace.toDual ℝ H).symm F) := by
    rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
  simpa only [hF] using hu ((_root_.InnerProductSpace.toDual ℝ H).symm F)

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.tendsto_dual_of_tendsto_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.tendsto_dual_of_tendsto_inner target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem tendsto_dual_piLpEquiv_symm_of_tendsto_inner
    {P A ι : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)]
    [∀ i, InnerProductSpace ℝ (X i)] [∀ i, CompleteSpace (X i)]
    {l : Filter A} (u : ∀ i, A → _root_.MeasureTheory.Lp (X i) 2 μ)
    (u₀ : ∀ i, _root_.MeasureTheory.Lp (X i) 2 μ)
    (hu : ∀ i (z : _root_.MeasureTheory.Lp (X i) 2 μ),
      _root_.Filter.Tendsto (fun a => _root_.Inner.inner ℝ (u i a) z) l (𝓝 (_root_.Inner.inner ℝ (u₀ i) z)))
    (F : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ →L[ℝ] ℝ) :
    _root_.Filter.Tendsto
      (fun a => F ((piLpEquiv (𝕜 := ℝ) μ).symm (WithLp.toLp 2 (fun i => u i a)))) l
      (𝓝 (F ((piLpEquiv (𝕜 := ℝ) μ).symm (WithLp.toLp 2 u₀)))) := by
  let V : A → PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ) :=
    fun a => WithLp.toLp 2 (fun i => u i a)
  let V₀ : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ) := WithLp.toLp 2 u₀
  have hV (z : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) :
      Tendsto (fun a => _root_.Inner.inner ℝ (V a) z) l (𝓝 (_root_.Inner.inner ℝ V₀ z)) := by
    change _root_.Filter.Tendsto (fun a => ∑ i, _root_.Inner.inner ℝ (u i a) (z i)) l
      (𝓝 (∑ i, _root_.Inner.inner ℝ (u₀ i) (z i)))
    exact tendsto_finsetSum _ fun i _ => hu i (z i)
  exact tendsto_dual_of_tendsto_inner hV
    (F.comp (piLpEquiv (𝕜 := ℝ) (X := X) μ).symm.toContinuousLinearEquiv.toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.tendsto_dual_piLpEquiv_symm_of_tendsto_inner then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.tendsto_dual_piLpEquiv_symm_of_tendsto_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.tendsto_dual_piLpEquiv_symm_of_tendsto_inner ``Submission.MeasureTheory.Lp.tendsto_dual_piLpEquiv_symm_of_tendsto_inner

variable {P ι κ : Type*} [MeasurableSpace P] {μ : Measure P}
  [Fintype ι] [Fintype κ]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def euclideanColumn (u : ι → _root_.MeasureTheory.Lp (EuclideanSpace ℝ κ) 2 μ) (j : κ) :
    Lp (EuclideanSpace ℝ ι) 2 μ :=
  (piLpEquiv (𝕜 := ℝ) (X := fun _ : ι => ℝ) μ).symm
    (WithLp.toLp 2 (fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.euclideanColumn then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.euclideanColumn"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.euclideanColumn ``Submission.MeasureTheory.Lp.euclideanColumn

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem euclideanColumn_coeFn
    (u : ι → _root_.MeasureTheory.Lp (EuclideanSpace ℝ κ) 2 μ) (j : κ) :
    (euclideanColumn u j : P → EuclideanSpace ℝ ι) =ᵐ[μ]
      (fun x => WithLp.toLp 2 (fun i => u i x j)) := by
  have he : ∀ᵐ x ∂μ, ∀ i,
      ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i)) x = u i x j :=
    ae_all_iff.mpr fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (u i)
  filter_upwards [piLpEquiv_symm_apply (𝕜 := ℝ) μ
    (WithLp.toLp 2 (fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i))), he]
    with x hx he
  exact hx.trans (PiLp.ext he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.euclideanColumn_coeFn then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.euclideanColumn_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.euclideanColumn_coeFn ``Submission.MeasureTheory.Lp.euclideanColumn_coeFn

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem tendsto_dual_euclideanColumn_of_tendsto_inner
    {A : Type*} {l : Filter A}
    (u : ι → A → _root_.MeasureTheory.Lp (EuclideanSpace ℝ κ) 2 μ)
    (u₀ : ι → _root_.MeasureTheory.Lp (EuclideanSpace ℝ κ) 2 μ)
    (hu : ∀ i (z : _root_.MeasureTheory.Lp (EuclideanSpace ℝ κ) 2 μ),
      _root_.Filter.Tendsto (fun a => _root_.Inner.inner ℝ (u i a) z) l (𝓝 (_root_.Inner.inner ℝ (u₀ i) z)))
    (j : κ) (F : _root_.MeasureTheory.Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] ℝ) :
    _root_.Filter.Tendsto (fun a => F (euclideanColumn (fun i => u i a) j)) l
      (𝓝 (F (euclideanColumn u₀ j))) := by
  have hc (i : ι) (z : _root_.MeasureTheory.Lp ℝ 2 μ) :
      _root_.Filter.Tendsto
        (fun a => _root_.Inner.inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i a)) z) l
        (𝓝 (_root_.Inner.inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u₀ i)) z)) := by
    have h := tendsto_dual_of_tendsto_inner (hu i)
      ((innerSL ℝ z).comp ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ))
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using h
  exact tendsto_dual_piLpEquiv_symm_of_tendsto_inner
    (fun i a => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i a))
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u₀ i)) hc F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.tendsto_dual_euclideanColumn_of_tendsto_inner then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.tendsto_dual_euclideanColumn_of_tendsto_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.tendsto_dual_euclideanColumn_of_tendsto_inner ``Submission.MeasureTheory.Lp.tendsto_dual_euclideanColumn_of_tendsto_inner

end MeasureTheory.Lp
