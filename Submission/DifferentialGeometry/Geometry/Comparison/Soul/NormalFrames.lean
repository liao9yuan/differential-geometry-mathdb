import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SoulExists

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tangentFinite (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.tangentFinite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.tangentFinite target :: scope.openDecls } }

def normalSpace (g : SmoothRiemannianMetric I M) (S : Set M) (x : M) :
    Submodule ℝ (TangentSpace I x) :=
  (sliceTangent I S x).dualAnnihilator.comap (metricFlatLinear (I := I) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.normalSpace

omit [FiniteDimensional ℝ E] in
@[simp] theorem mem_normalSpace_iff (g : SmoothRiemannianMetric I M)
    (S : Set M) (x : M) (v : TangentSpace I x) :
    v ∈ normalSpace (I := I) g S x ↔
      ∀ w ∈ sliceTangent I S x, g.inner x v w = 0 := by
  simp only [normalSpace, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    metricFlatLinear_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.mem_normalSpace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.mem_normalSpace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.mem_normalSpace_iff ``Submission.DifferentialGeometry.Geometry.Topology.mem_normalSpace_iff

def normalFlatEquiv (g : SmoothRiemannianMetric I M) (S : Set M) (x : M) :
    normalSpace (I := I) g S x ≃ₗ[ℝ] (sliceTangent I S x).dualAnnihilator where
  toFun v := ⟨metricFlatMap (I := I) g x v, v.property⟩
  invFun a := ⟨(metricFlatMap (I := I) g x).symm a, by
    change metricFlatMap (I := I) g x ((metricFlatMap (I := I) g x).symm a) ∈
      (sliceTangent I S x).dualAnnihilator
    simpa only [LinearEquiv.apply_symm_apply] using a.property⟩
  left_inv v := by
    apply Subtype.ext
    exact (metricFlatMap (I := I) g x).symm_apply_apply v
  right_inv a := by
    apply Subtype.ext
    exact (metricFlatMap (I := I) g x).apply_symm_apply a
  map_add' v w := by
    apply Subtype.ext
    exact map_add (metricFlatMap (I := I) g x)
      (v : TangentSpace I x) (w : TangentSpace I x)
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul (metricFlatMap (I := I) g x) c (v : TangentSpace I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalFlatEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalFlatEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalFlatEquiv ``Submission.DifferentialGeometry.Geometry.Topology.normalFlatEquiv

theorem finrank_sliceTangent_add_normalSpace (g : SmoothRiemannianMetric I M)
    (S : Set M) (x : M) :
    Module.finrank ℝ (sliceTangent I S x) +
      Module.finrank ℝ (normalSpace (I := I) g S x) = Module.finrank ℝ E := by
  rw [(normalFlatEquiv (I := I) g S x).finrank_eq]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq (sliceTangent I S x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.finrank_sliceTangent_add_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.finrank_sliceTangent_add_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.finrank_sliceTangent_add_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.finrank_sliceTangent_add_normalSpace

theorem finrank_normalSpace (g : SmoothRiemannianMetric I M)
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S) {x : M} (hx : x ∈ S) :
    Module.finrank ℝ (normalSpace (I := I) g S x) = Module.finrank ℝ E - d := by
  have hsum := finrank_sliceTangent_add_normalSpace (I := I) g S x
  rw [finrank_sliceTangent hS hx] at hsum
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.finrank_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.finrank_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.finrank_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.finrank_normalSpace

omit [FiniteDimensional ℝ E] in
theorem eq_zero_of_mem_sliceTangent_of_mem_normalSpace
    (g : SmoothRiemannianMetric I M) {S : Set M} {x : M} {v : TangentSpace I x}
    (ht : v ∈ sliceTangent I S x) (hn : v ∈ normalSpace (I := I) g S x) : v = 0 := by
  have hzero := (mem_normalSpace_iff (I := I) g S x v).mp hn v ht
  by_contra hne
  exact (ne_of_gt (g.pos x v hne)) hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.eq_zero_of_mem_sliceTangent_of_mem_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.eq_zero_of_mem_sliceTangent_of_mem_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.eq_zero_of_mem_sliceTangent_of_mem_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.eq_zero_of_mem_sliceTangent_of_mem_normalSpace

omit [FiniteDimensional ℝ E] in
theorem sliceTangent_inf_normalSpace (g : SmoothRiemannianMetric I M)
    (S : Set M) (x : M) :
    sliceTangent I S x ⊓ normalSpace (I := I) g S x = ⊥ := by
  apply (Submodule.eq_bot_iff _).2
  intro v hv
  exact eq_zero_of_mem_sliceTangent_of_mem_normalSpace (I := I) g hv.1 hv.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sliceTangent_inf_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sliceTangent_inf_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sliceTangent_inf_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.sliceTangent_inf_normalSpace


theorem sliceTangent_sup_normalSpace (g : SmoothRiemannianMetric I M)
    (S : Set M) (x : M) :
    sliceTangent I S x ⊔ normalSpace (I := I) g S x = ⊤ := by
  apply Submodule.eq_top_of_disjoint
  · exact (finrank_sliceTangent_add_normalSpace (I := I) g S x).ge
  · rw [disjoint_iff, sliceTangent_inf_normalSpace (I := I) g S x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sliceTangent_sup_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sliceTangent_sup_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sliceTangent_sup_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.sliceTangent_sup_normalSpace


def normalFrameSynthesis (g : SmoothRiemannianMetric I M)
    {m : ℕ} (F : Fin m → M → ℝ) (x : M) :
    (Fin m → ℝ) →ₗ[ℝ] TangentSpace I x where
  toFun c := ∑ i, c i • gradFun (I := I) g (F i) x
  map_add' c b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, _root_.SemigroupAction.mul_smul, Finset.smul_sum, RingHom.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalFrameSynthesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalFrameSynthesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalFrameSynthesis ``Submission.DifferentialGeometry.Geometry.Topology.normalFrameSynthesis


@[simp] theorem normalFrameSynthesis_apply (g : SmoothRiemannianMetric I M)
    {m : ℕ} (F : Fin m → M → ℝ) (x : M) (c : Fin m → ℝ) :
    normalFrameSynthesis (I := I) g F x c =
      ∑ i, c i • gradFun (I := I) g (F i) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalFrameSynthesis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalFrameSynthesis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalFrameSynthesis_apply ``Submission.DifferentialGeometry.Geometry.Topology.normalFrameSynthesis_apply


def normalFramePairing (g : SmoothRiemannianMetric I M)
    {m : ℕ} (F : Fin m → M → ℝ) (x : M) :
    TangentSpace I x →ₗ[ℝ] (Fin m → ℝ) where
  toFun v i := g.inner x (gradFun (I := I) g (F i) x) v
  map_add' v w := by
    ext i
    exact map_add (g.inner x (gradFun (I := I) g (F i) x)) v w
  map_smul' c v := by
    ext i
    exact map_smul (g.inner x (gradFun (I := I) g (F i) x)) c v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalFramePairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalFramePairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalFramePairing ``Submission.DifferentialGeometry.Geometry.Topology.normalFramePairing

end Algebra

section DefiningFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem normalFramePairing_synthesis (g : SmoothRiemannianMetric I M)
    {m : ℕ} (F : Fin m → M → ℝ) (x : M) (c : Fin m → ℝ) :
    normalFramePairing (I := I) g F x (normalFrameSynthesis (I := I) g F x c) =
      Matrix.toLin' (sliceGram (I := I) g F x) c := by
  ext i
  change g.inner x (gradFun (I := I) g (F i) x)
      (∑ j, c j • gradFun (I := I) g (F j) x) = _
  rw [map_sum, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  change c j * g.inner x (gradFun (I := I) g (F i) x)
      (gradFun (I := I) g (F j) x) =
    g.inner x (gradFun (I := I) g (F i) x)
      (gradFun (I := I) g (F j) x) * c j
  exact mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalFramePairing_synthesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalFramePairing_synthesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalFramePairing_synthesis ``Submission.DifferentialGeometry.Geometry.Topology.normalFramePairing_synthesis

namespace IsSliceDefiningFamilyOn

variable {g : SmoothRiemannianMetric I M} {C : Set M} {m : ℕ}
  {F : Fin m → M → ℝ} {W : Set M}


theorem synthesis_mem_normalSpace (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) (c : Fin m → ℝ) :
    normalFrameSynthesis (I := I) g F x c ∈
      normalSpace (I := I) g (maxSliceLocus I C) x := by
  rw [mem_normalSpace_iff]
  intro w hw
  rw [normalFrameSynthesis_apply, g.symm, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, smul_eq_mul, g.symm, (hfam.mem_iff x hxW hxN w).mp hw i, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_mem_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_mem_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_mem_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_mem_normalSpace

theorem gram_injective (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    Function.Injective (Matrix.toLin' (sliceGram (I := I) g F x)) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).2
  intro c hc
  have hc0 : Matrix.toLin' (sliceGram (I := I) g F x) c = 0 := hc
  have ht : normalFrameSynthesis (I := I) g F x c ∈
      sliceTangent I (maxSliceLocus I C) x := by
    apply (hfam.mem_iff x hxW hxN _).2
    intro i
    have hp := congrFun (normalFramePairing_synthesis (I := I) g F x c) i
    rw [hc0] at hp
    exact hp
  have hz := eq_zero_of_mem_sliceTangent_of_mem_normalSpace (I := I) g ht
    (hfam.synthesis_mem_normalSpace hxW hxN c)
  exact hfam.indep x hxW hxN c hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gram_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gram_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gram_injective ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gram_injective


def gramEquiv (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (sliceGram (I := I) g F x))
    ⟨hfam.gram_injective hxW hxN,
      LinearMap.injective_iff_surjective.1 (hfam.gram_injective hxW hxN)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv


@[simp] theorem gramEquiv_apply (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) (c : Fin m → ℝ) :
    hfam.gramEquiv hxW hxN c = Matrix.toLin' (sliceGram (I := I) g F x) c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv_apply ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.gramEquiv_apply


theorem synthesis_gramEquiv_symm_pairing
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C)
    (v : normalSpace (I := I) g (maxSliceLocus I C) x) :
    normalFrameSynthesis (I := I) g F x
      ((hfam.gramEquiv hxW hxN).symm (normalFramePairing (I := I) g F x v)) = v := by
  let c := (hfam.gramEquiv hxW hxN).symm (normalFramePairing (I := I) g F x v)
  have hpair : normalFramePairing (I := I) g F x
      (normalFrameSynthesis (I := I) g F x c) = normalFramePairing (I := I) g F x v := by
    rw [normalFramePairing_synthesis, ← hfam.gramEquiv_apply hxW hxN]
    exact (hfam.gramEquiv hxW hxN).apply_symm_apply _
  have ht : (v : TangentSpace I x) - normalFrameSynthesis (I := I) g F x c ∈
      sliceTangent I (maxSliceLocus I C) x := by
    apply (hfam.mem_iff x hxW hxN _).2
    intro i
    have hi := congrFun hpair i
    change g.inner x (gradFun (I := I) g (F i) x)
        (normalFrameSynthesis (I := I) g F x c) =
      g.inner x (gradFun (I := I) g (F i) x) v at hi
    rw [map_sub, hi, sub_self]
  have hn : (v : TangentSpace I x) - normalFrameSynthesis (I := I) g F x c ∈
      normalSpace (I := I) g (maxSliceLocus I C) x :=
    (normalSpace (I := I) g (maxSliceLocus I C) x).sub_mem v.property
      (hfam.synthesis_mem_normalSpace hxW hxN c)
  exact (sub_eq_zero.mp
    (eq_zero_of_mem_sliceTangent_of_mem_normalSpace (I := I) g ht hn)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_gramEquiv_symm_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_gramEquiv_symm_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_gramEquiv_symm_pairing ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.synthesis_gramEquiv_symm_pairing

def normalEquiv (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    (Fin m → ℝ) ≃ₗ[ℝ] normalSpace (I := I) g (maxSliceLocus I C) x where
  toFun c := ⟨normalFrameSynthesis (I := I) g F x c,
    hfam.synthesis_mem_normalSpace hxW hxN c⟩
  invFun v := (hfam.gramEquiv hxW hxN).symm (normalFramePairing (I := I) g F x v)
  left_inv c := by
    change (hfam.gramEquiv hxW hxN).symm
      (normalFramePairing (I := I) g F x (normalFrameSynthesis (I := I) g F x c)) = c
    rw [normalFramePairing_synthesis, ← hfam.gramEquiv_apply hxW hxN]
    exact (hfam.gramEquiv hxW hxN).symm_apply_apply c
  right_inv v := by
    apply Subtype.ext
    exact hfam.synthesis_gramEquiv_symm_pairing hxW hxN v
  map_add' c b := by
    apply Subtype.ext
    exact map_add (normalFrameSynthesis (I := I) g F x) c b
  map_smul' a c := by
    apply Subtype.ext
    exact map_smul (normalFrameSynthesis (I := I) g F x) a c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv


def normalBasis (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    Module.Basis (Fin m) ℝ (normalSpace (I := I) g (maxSliceLocus I C) x) :=
  (Pi.basisFun ℝ (Fin m)).map (hfam.normalEquiv hxW hxN)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis


@[simp] theorem normalBasis_coe (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) (i : Fin m) :
    ((hfam.normalBasis hxW hxN i) : TangentSpace I x) =
      gradFun (I := I) g (F i) x := by
  classical
  simp [normalBasis, normalEquiv, normalFrameSynthesis, Pi.basisFun_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis_coe ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalBasis_coe


theorem normalEquiv_symm_apply (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C)
    (v : normalSpace (I := I) g (maxSliceLocus I C) x) :
    (hfam.normalEquiv hxW hxN).symm v =
      (hfam.gramEquiv hxW hxN).symm (normalFramePairing (I := I) g F x v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv_symm_apply ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalEquiv_symm_apply


theorem card_eq_finrank_normalSpace (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    m = Module.finrank ℝ (normalSpace (I := I) g (maxSliceLocus I C) x) := by
  simpa only [Fintype.card_fin] using
    (Module.finrank_eq_card_basis (hfam.normalBasis hxW hxN)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.card_eq_finrank_normalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.card_eq_finrank_normalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.card_eq_finrank_normalSpace ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.card_eq_finrank_normalSpace

end IsSliceDefiningFamilyOn

private def matrixContinuousMap (m : ℕ) :
    (Fin m → Fin m → ℝ) →ₗ[ℝ] ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) where
  toFun A := (Matrix.toLin' A).toContinuousLinearMap
  map_add' A B := by
    ext c i
    change (∑ j, (A i j + B i j) * c j) =
      (∑ j, A i j * c j) + ∑ j, B i j * c j
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' a A := by
    ext c i
    change (∑ j, (a * A i j) * c j) = a * ∑ j, A i j * c j
    simp only [mul_assoc, Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.matrixContinuousMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.matrixContinuousMap target :: scope.openDecls } }

def normalGramOperator (g : SmoothRiemannianMetric I M)
    {m : ℕ} (F : Fin m → M → ℝ) (x : M) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  matrixContinuousMap m (sliceGram (I := I) g F x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalGramOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalGramOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalGramOperator ``Submission.DifferentialGeometry.Geometry.Topology.normalGramOperator

def normalGramInverse (g : SmoothRiemannianMetric I M)
    {m : ℕ} (F : Fin m → M → ℝ) (x : M) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.inverse (normalGramOperator (I := I) g F x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalGramInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalGramInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalGramInverse ``Submission.DifferentialGeometry.Geometry.Topology.normalGramInverse

theorem IsSliceDefiningFamilyOn.normalGramInverse_apply
    {g : SmoothRiemannianMetric I M} {C : Set M} {m : ℕ}
    {F : Fin m → M → ℝ} {W : Set M}
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) (c : Fin m → ℝ) :
    normalGramInverse (I := I) g F x c = (hfam.gramEquiv hxW hxN).symm c := by
  have he : normalGramOperator (I := I) g F x =
      (hfam.gramEquiv hxW hxN).toContinuousLinearEquiv.toContinuousLinearMap := rfl
  rw [normalGramInverse, he, ContinuousLinearMap.inverse_equiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_apply ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_apply

omit [FiniteDimensional ℝ E] in
private theorem inner_contMDiff_of_sections
    (g : SmoothRiemannianMetric I M)
    {Y Z : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (T% Y))
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => g.inner x (Y x) (Z x)) := by
  have happ : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, g.inner x (Y x) (Z x)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) g.contMDiff hY hZ
  intro x
  have hx := happ x
  rw [Bundle.contMDiffAt_totalSpace] at hx
  exact hx.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.inner_contMDiff_of_sections
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.inner_contMDiff_of_sections target :: scope.openDecls } }

theorem normalGramOperator_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {m : ℕ} {F : Fin m → M → ℝ}
    (hF : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (F i)) :
    ContMDiff I 𝓘(ℝ, (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) ∞
      (normalGramOperator (I := I) g F) := by
  have hgrad : ∀ i, ContMDiff I I.tangent ∞
      (T% fun x => gradFun (I := I) g (F i) x) :=
    fun i => gradFun_contMDiff_total_section (I := I) g (hF i)
  have hG : ContMDiff I 𝓘(ℝ, Fin m → Fin m → ℝ) ∞
      (fun x i j => sliceGram (I := I) g F x i j) := by
    apply contMDiff_pi_space.2
    intro i
    apply contMDiff_pi_space.2
    intro j
    exact inner_contMDiff_of_sections (I := I) g (hgrad i) (hgrad j)
  exact (matrixContinuousMap m).toContinuousLinearMap.contMDiff.comp hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalGramOperator_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalGramOperator_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalGramOperator_contMDiff ``Submission.DifferentialGeometry.Geometry.Topology.normalGramOperator_contMDiff

theorem IsSliceDefiningFamilyOn.normalGramInverse_contMDiffAt [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {C : Set M} {m : ℕ}
    {F : Fin m → M → ℝ} {W : Set M}
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    ContMDiffAt I 𝓘(ℝ, (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) ∞
      (normalGramInverse (I := I) g F) x := by
  have hinv : (normalGramOperator (I := I) g F x).IsInvertible :=
    ⟨(hfam.gramEquiv hxW hxN).toContinuousLinearEquiv, rfl⟩
  exact hinv.contDiffAt_map_inverse.contMDiffAt.comp x
    (normalGramOperator_contMDiff (I := I) g hfam.contMDiff x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_contMDiffAt ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalGramInverse_contMDiffAt

theorem IsSliceDefiningFamilyOn.normalCoordinates_contMDiffAt [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {C : Set M} {m : ℕ}
    {F : Fin m → M → ℝ} {W : Set M}
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C)
    {V : ∀ y : M, TangentSpace I y} (hV : ContMDiff I I.tangent ∞ (T% V)) :
    ContMDiffAt I 𝓘(ℝ, Fin m → ℝ) ∞
      (fun y => normalGramInverse (I := I) g F y
        (normalFramePairing (I := I) g F y (V y))) x := by
  have hp : ContMDiff I 𝓘(ℝ, Fin m → ℝ) ∞
      (fun y => normalFramePairing (I := I) g F y (V y)) := by
    apply contMDiff_pi_space.2
    intro i
    exact inner_contMDiff_of_sections (I := I) g
      (gradFun_contMDiff_total_section (I := I) g (hfam.contMDiff i)) hV
  exact (hfam.normalGramInverse_contMDiffAt hxW hxN).clm_apply (hp x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalCoordinates_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalCoordinates_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalCoordinates_contMDiffAt ``Submission.DifferentialGeometry.Geometry.Topology.IsSliceDefiningFamilyOn.normalCoordinates_contMDiffAt

end DefiningFamily

section LocalSoulFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_smooth_normal_frame
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S)
    (hboundary : relBoundary I S = ∅) {x : M} (hx : x ∈ S) :
    ∃ (m : ℕ) (F : Fin m → M → ℝ) (W : Set M),
      x ∈ W ∧ IsSliceDefiningFamilyOn (I := I) g S F W ∧
      m = Module.finrank ℝ E - maxSliceDim I S ∧
      (∀ i, ContMDiff I I.tangent ∞ (T% fun y => gradFun (I := I) g (F i) y)) ∧
      ∀ y ∈ W, y ∈ S →
        ∃ b : Module.Basis (Fin m) ℝ (normalSpace (I := I) g S y),
          ∀ i, (b i : TangentSpace I y) = gradFun (I := I) g (F i) y := by
  have hN : maxSliceLocus I S = S := relBoundary_eq_empty_iff.mp hboundary
  have hxN : x ∈ maxSliceLocus I S := by rwa [hN]
  obtain ⟨m, F, W, hxW, hfam⟩ :=
    hasSliceDefiningFamilies_of_totallyConvex (I := I) hEnorm hconv x hxN
  have hdim := hfam.card_eq_finrank_normalSpace hxW hxN
  rw [hN, finrank_normalSpace (I := I) g
    (isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hboundary) hx] at hdim
  refine ⟨m, F, W, hxW, hfam, hdim, ?_, ?_⟩
  · intro i
    exact gradFun_contMDiff_total_section (I := I) g (hfam.contMDiff i)
  · intro y hyW hyS
    have hyN : y ∈ maxSliceLocus I S := by rwa [hN]
    have hb := hfam.normalBasis_coe hyW hyN
    have hresult : ∃ b : Module.Basis (Fin m) ℝ
        (normalSpace (I := I) g (maxSliceLocus I S) y),
        ∀ i, (b i : TangentSpace I y) = gradFun (I := I) g (F i) y :=
      ⟨hfam.normalBasis hyW hyN, hb⟩
    rw [hN] at hresult
    exact hresult

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_smooth_normal_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_smooth_normal_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_smooth_normal_frame ``Submission.DifferentialGeometry.Geometry.Topology.exists_smooth_normal_frame

end LocalSoulFrame

end DifferentialGeometry.Geometry.Topology

end
