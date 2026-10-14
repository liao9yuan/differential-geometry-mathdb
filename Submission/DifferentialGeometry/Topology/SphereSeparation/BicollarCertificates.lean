import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarSliceSeparation
import Submission.DifferentialGeometry.Topology.SphereSeparation.TubularExcision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set _root_.Topology
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation


noncomputable def axialRecenterRadius {a : ℝ} (c : AxialInterval a) : ℝ :=
  _root_.Min.min ((c : ℝ) + a) (a - (c : ℝ)) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius

theorem axialRecenterRadius_pos {a : ℝ} (c : AxialInterval a) :
    0 < axialRecenterRadius c := by
  apply div_pos
  · exact lt_min (by linarith [c.2.1]) (by linarith [c.2.2])
  · norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_pos ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_pos

private theorem axialRecenterRadius_lt_leftMargin
    {a : ℝ} (c : AxialInterval a) :
    axialRecenterRadius c < (c : ℝ) + a := by
  have hm : 0 < _root_.Min.min ((c : ℝ) + a) (a - (c : ℝ)) :=
    lt_min (by linarith [c.2.1]) (by linarith [c.2.2])
  have hh : _root_.Min.min ((c : ℝ) + a) (a - (c : ℝ)) / 2 <
      min ((c : ℝ) + a) (a - (c : ℝ)) := by linarith
  exact lt_of_lt_of_le hh (min_le_left _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_lt_leftMargin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_lt_leftMargin target :: scope.openDecls } }

private theorem axialRecenterRadius_lt_rightMargin
    {a : ℝ} (c : AxialInterval a) :
    axialRecenterRadius c < a - (c : ℝ) := by
  have hm : 0 < _root_.Min.min ((c : ℝ) + a) (a - (c : ℝ)) :=
    lt_min (by linarith [c.2.1]) (by linarith [c.2.2])
  have hh : _root_.Min.min ((c : ℝ) + a) (a - (c : ℝ)) / 2 <
      min ((c : ℝ) + a) (a - (c : ℝ)) := by linarith
  exact lt_of_lt_of_le hh (min_le_right _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_lt_rightMargin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.axialRecenterRadius_lt_rightMargin target :: scope.openDecls } }

def axialRecenter {a : ℝ} (c : AxialInterval a) :
    AxialInterval (axialRecenterRadius c) → AxialInterval a :=
  fun t ↦ ⟨(c : ℝ) + (t : ℝ),
    by
      have ht := t.2.1
      have hb := axialRecenterRadius_lt_leftMargin c
      linarith,
    by
      have ht := t.2.2
      have hb := axialRecenterRadius_lt_rightMargin c
      linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialRecenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialRecenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialRecenter ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenter

@[simp]
theorem axialRecenter_coe {a : ℝ} (c : AxialInterval a)
    (t : AxialInterval (axialRecenterRadius c)) :
    (axialRecenter c t : ℝ) = (c : ℝ) + (t : ℝ) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialRecenter_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialRecenter_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialRecenter_coe ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenter_coe


theorem axialRecenter_isOpenEmbedding {a : ℝ} (c : AxialInterval a) :
    IsOpenEmbedding (axialRecenter c) := by
  let g : AxialInterval (axialRecenterRadius c) → ℝ :=
    fun t ↦ (c : ℝ) + (t : ℝ)
  have hg : _root_.Topology.IsOpenEmbedding g := by
    exact (Homeomorph.addLeft (c : ℝ)).isOpenEmbedding.comp
      isOpen_Ioo.isOpenEmbedding_subtypeVal
  apply IsOpenEmbedding.of_comp (axialRecenter c)
    (AxialInterval a).2.isOpenEmbedding_subtypeVal
  convert hg using 1
  funext t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialRecenter_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialRecenter_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialRecenter_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialRecenter_isOpenEmbedding


def recenteredBicollar
    {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    SphereTwo × AxialInterval (axialRecenterRadius c) → N :=
  fun x ↦ Φ (x.1, axialRecenter c x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar ``Submission.DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar


theorem recenteredBicollar_isOpenEmbedding
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ) :
    IsOpenEmbedding (recenteredBicollar Φ c) := by
  have hsource : _root_.Topology.IsOpenEmbedding
      (Prod.map (id : SphereTwo → SphereTwo) (axialRecenter c)) :=
    IsOpenEmbedding.id.prodMap (axialRecenter_isOpenEmbedding c)
  convert hΦ.comp hsource using 1
  funext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_isOpenEmbedding

@[simp]
theorem recenteredBicollar_zeroSlice
    {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a)
    (p : SphereTwo) :
    recenteredBicollar Φ c
        (p, axialZero (axialRecenterRadius_pos c)) = Φ (p, c) := by
  apply congrArg Φ
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [axialRecenter, axialZero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_zeroSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_zeroSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_zeroSlice ``Submission.DifferentialGeometry.Topology.SphereSeparation.recenteredBicollar_zeroSlice

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ) (c : AxialInterval a)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) := by
  apply hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    (axialRecenterRadius_pos c) (bicollarSliceMap Φ c)
    (recenteredBicollar Φ c)
    (recenteredBicollar_isOpenEmbedding Φ c hΦ)
  · intro p
    exact recenteredBicollar_zeroSlice Φ c p
  · exact hSphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ) (c : AxialInterval a)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) :=
  hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1
    Φ hΦ c
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding

theorem smoothBicollar_isOpenEmbedding
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ) :
    IsOpenEmbedding Φ := by
  refine ⟨hΦ.isEmbedding, ?_⟩
  have hrank :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
        Module.finrank ℝ EuclideanThree := by
    norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
  exact Manifold.isOpen_range_of_isSmoothEmbedding
    (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
    (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothBicollar_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothBicollar_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothBicollar_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothBicollar_isOpenEmbedding

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1))
    (c : AxialInterval a) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) :=
  hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1
    Φ (smoothBicollar_isOpenEmbedding Φ hΦ) c hSphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex)
    (c : AxialInterval a) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) :=
  hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
    Φ hΦ
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)
    c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding

end DifferentialGeometry.Topology.SphereSeparation
