import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

private theorem adjunction_cell_injective {A B X : Type*} (i : A → B) (φ : A → X)
    (hφ : Function.Injective φ) : Function.Injective (adjunctionCell i φ) := by
  intro b b' h
  let f : B ⊕ X → Prop := Sum.elim (fun z => z = b) (fun x => ∃ a, φ a = x ∧ i a = b)
  have hf (a : A) : f (Sum.inl (i a)) = f (Sum.inr (φ a)) := by
    simp [f, hφ.eq_iff]
  let g : AdjunctionSpace i φ → Prop := Quot.lift f (by
    intro u v huv
    rcases huv with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hf a
    · exact (hf a).symm)
  have hh := congrArg g h
  change (b = b) = (b' = b) at hh
  exact (Eq.mp hh rfl).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunction_cell_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunction_cell_injective target :: scope.openDecls } }

private theorem adjunction_lower_injective {A B X : Type*} (i : A → B) (φ : A → X)
    (hi : Function.Injective i) : Function.Injective (adjunctionLower (i := i) φ) := by
  intro x x' h
  let f : B ⊕ X → Prop := Sum.elim (fun b => ∃ a, i a = b ∧ φ a = x) (fun z => z = x)
  have hf (a : A) : f (Sum.inl (i a)) = f (Sum.inr (φ a)) := by
    simp [f, hi.eq_iff]
  let g : AdjunctionSpace i φ → Prop := Quot.lift f (by
    intro u v huv
    rcases huv with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hf a
    · exact (hf a).symm)
  have hh := congrArg g h
  change (x = x) = (x' = x) at hh
  exact (Eq.mp hh rfl).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.adjunction_lower_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.adjunction_lower_injective target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

structure BallChart (n : ℕ) (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  chart : PartialDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I
    (EuclideanSpace ℝ (Fin n)) M ∞
  closedBall_subset_source : Metric.closedBall 0 2 ⊆ chart.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart ``Submission.DifferentialGeometry.Topology.BallChart

namespace BallChart

variable {n : ℕ} {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (c : BallChart n I M)

theorem ball_subset_source : Metric.ball 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change _root_.Dist.dist x 0 ≤ 2
  exact le_trans (le_of_lt (Metric.mem_ball.mp hx)) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.ball_subset_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.ball_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.ball_subset_source ``Submission.DifferentialGeometry.Topology.BallChart.ball_subset_source

theorem sphere_subset_source : Metric.sphere 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change _root_.Dist.dist x 0 ≤ 2
  rw [Metric.mem_sphere.mp hx]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.sphere_subset_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.sphere_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.sphere_subset_source ``Submission.DifferentialGeometry.Topology.BallChart.sphere_subset_source

abbrev Punctured := {x : M // x ∉ c.chart '' Metric.ball 0 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.Punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.Punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.Punctured ``Submission.DifferentialGeometry.Topology.BallChart.Punctured

def boundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : c.Punctured :=
  ⟨c.chart z, by
    rintro ⟨x, hx, h⟩
    have heq : x = (z : EuclideanSpace ℝ (Fin n)) :=
      c.chart.toPartialEquiv.injOn (c.ball_subset_source hx)
        (c.sphere_subset_source z.2) h
    subst x
    have hz := Metric.mem_sphere.mp z.2
    exact (not_lt_of_ge (le_of_eq hz.symm)) hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.boundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.boundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.boundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.boundaryMap

@[simp]
theorem boundaryMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.boundaryMap z : M) = c.chart z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.boundaryMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.boundaryMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.boundaryMap_val ``Submission.DifferentialGeometry.Topology.BallChart.boundaryMap_val

theorem boundaryMap_injective : Function.Injective c.boundaryMap := by
  intro x y h
  apply Subtype.ext
  exact c.chart.toPartialEquiv.injOn (c.sphere_subset_source x.2)
    (c.sphere_subset_source y.2) (congrArg Subtype.val h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.boundaryMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.boundaryMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.boundaryMap_injective ``Submission.DifferentialGeometry.Topology.BallChart.boundaryMap_injective

theorem continuous_boundaryMap : Continuous c.boundaryMap := by
  apply Continuous.subtype_mk
  exact c.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun x => c.sphere_subset_source x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_boundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_boundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_boundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.continuous_boundaryMap

theorem continuous_inclusion : Continuous (Subtype.val : c.Punctured → M) :=
  continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_inclusion ``Submission.DifferentialGeometry.Topology.BallChart.continuous_inclusion

theorem inclusion_injective : Function.Injective (Subtype.val : c.Punctured → M) :=
  Subtype.val_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.inclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.inclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.inclusion_injective ``Submission.DifferentialGeometry.Topology.BallChart.inclusion_injective

theorem isOpen_chart_image_ball : IsOpen (c.chart '' Metric.ball 0 1) := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ c.chart.toPartialEquiv.source :=
    c.ball_subset_source
  have hcont : ContinuousOn (⇑c.chart.toPartialEquiv.symm) c.chart.toPartialEquiv.target :=
    c.chart.contMDiffOn_invFun.continuousOn
  have hopen : IsOpen (c.chart.toPartialEquiv.target ∩
      (⇑c.chart.toPartialEquiv.symm) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    hcont.isOpen_inter_preimage c.chart.open_target
      (Metric.isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1))
  rw [PartialEquiv.image_eq_target_inter_inv_preimage _ hsub]
  exact hopen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isOpen_chart_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isOpen_chart_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isOpen_chart_image_ball ``Submission.DifferentialGeometry.Topology.BallChart.isOpen_chart_image_ball

theorem isClosed_punctured : IsClosed {x : M | x ∉ c.chart '' Metric.ball 0 1} :=
  c.isOpen_chart_image_ball.isClosed_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isClosed_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isClosed_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isClosed_punctured ``Submission.DifferentialGeometry.Topology.BallChart.isClosed_punctured

instance instCompactSpacePunctured [CompactSpace M] : CompactSpace c.Punctured :=
  isCompact_iff_compactSpace.mp c.isClosed_punctured.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.instCompactSpacePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.instCompactSpacePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.instCompactSpacePunctured ``Submission.DifferentialGeometry.Topology.BallChart.instCompactSpacePunctured

end BallChart

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K]
  {n : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]

abbrev ConnectedSumQuotient (c : BallChart n I M) (d : BallChart n J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  AdjunctionSpace c.boundaryMap (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient

namespace ConnectedSumQuotient

variable (c : BallChart n I M) (d : BallChart n J N)
  (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

def mk : c.Punctured ⊕ d.Punctured → ConnectedSumQuotient c d a :=
  adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mk ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mk

def inl : c.Punctured → ConnectedSumQuotient c d a :=
  adjunctionCell c.boundaryMap (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inl ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl

def inr : d.Punctured → ConnectedSumQuotient c d a :=
  adjunctionLower (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inr ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inr

@[simp]
theorem mk_inl (x : c.Punctured) : mk c d a (Sum.inl x) = inl c d a x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inl ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inl

@[simp]
theorem mk_inr (x : d.Punctured) : mk c d a (Sum.inr x) = inr c d a x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inr ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mk_inr

theorem boundary_eq (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    inl c d a (c.boundaryMap z) = inr c d a (d.boundaryMap (a z)) :=
  adjunction_coherence c.boundaryMap (d.boundaryMap ∘ a) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.boundary_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.boundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.boundary_eq ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.boundary_eq

theorem continuous_inl : Continuous (inl c d a) :=
  continuous_adjunctionCell c.boundaryMap (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inl ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inl

theorem continuous_inr : Continuous (inr c d a) :=
  continuous_adjunctionLower c.boundaryMap (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inr ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_inr

theorem inl_injective : Function.Injective (inl c d a) :=
  adjunction_cell_injective c.boundaryMap (d.boundaryMap ∘ a)
    (d.boundaryMap_injective.comp a.injective)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inl_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_injective ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl_injective

theorem inr_injective : Function.Injective (inr c d a) :=
  adjunction_lower_injective c.boundaryMap (d.boundaryMap ∘ a) c.boundaryMap_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inr_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_injective ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inr_injective

theorem isQuotientMap_mk : _root_.Topology.IsQuotientMap (mk c d a) :=
  isQuotientMap_adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isQuotientMap_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isQuotientMap_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isQuotientMap_mk ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isQuotientMap_mk

theorem jointly_surjective (z : ConnectedSumQuotient c d a) :
    (∃ x, inl c d a x = z) ∨ (∃ y, inr c d a y = z) := by
  refine Quot.induction_on z ?_
  intro s
  rcases s with x | y
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.jointly_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.jointly_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.jointly_surjective ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.jointly_surjective

theorem inl_eq_inr_iff (p : c.Punctured) (q : d.Punctured) :
    inl c d a p = inr c d a q ↔
      ∃ z, c.boundaryMap z = p ∧ d.boundaryMap (a z) = q :=
  adjunction_cell_eq_lower_iff c.boundaryMap (d.boundaryMap ∘ a)
    (d.boundaryMap_injective.comp a.injective) p q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_eq_inr_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inl_eq_inr_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_eq_inr_iff ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl_eq_inr_iff

theorem inl_ne_inr_of_forall (p : c.Punctured) (q : d.Punctured)
    (h : ∀ z, c.boundaryMap z = p → d.boundaryMap (a z) ≠ q) :
    inl c d a p ≠ inr c d a q := by
  intro hpq
  obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a p q).mp hpq
  exact h z hz hz'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_ne_inr_of_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inl_ne_inr_of_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_ne_inr_of_forall ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl_ne_inr_of_forall

theorem nonempty_sphere_of_neZero [NeZero n] :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  let ⟨z, hz⟩ := NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)
  ⟨⟨z, hz⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.nonempty_sphere_of_neZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.nonempty_sphere_of_neZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.nonempty_sphere_of_neZero ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.nonempty_sphere_of_neZero

instance instT2Space [T2Space M] [T2Space N] : T2Space (ConnectedSumQuotient c d a) :=
  DifferentialGeometry.Topology.Manifold.Attachment.adjunction_t2Space c.boundaryMap
    (d.boundaryMap ∘ a)
    c.boundaryMap_injective (d.boundaryMap_injective.comp a.injective)
    c.continuous_boundaryMap (d.continuous_boundaryMap.comp a.continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.instT2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.instT2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.instT2Space ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.instT2Space

instance instCompactSpace [CompactSpace c.Punctured] [CompactSpace d.Punctured] :
    CompactSpace (ConnectedSumQuotient c d a) :=
  Quot.compactSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.instCompactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.instCompactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.instCompactSpace ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.instCompactSpace

instance instConnectedSpace [ConnectedSpace c.Punctured] [ConnectedSpace d.Punctured]
    [Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    ConnectedSpace (ConnectedSumQuotient c d a) :=
  DifferentialGeometry.Topology.connectedSpace_adjunctionSpace c.boundaryMap
    (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.instConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.instConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.instConnectedSpace ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.instConnectedSpace

instance instPathConnectedSpace [PathConnectedSpace c.Punctured]
    [PathConnectedSpace d.Punctured]
    [Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    PathConnectedSpace (ConnectedSumQuotient c d a) :=
  DifferentialGeometry.Topology.pathConnectedSpace_adjunctionSpace c.boundaryMap
    (d.boundaryMap ∘ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.instPathConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.instPathConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.instPathConnectedSpace ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.instPathConnectedSpace

theorem isOpen_image_inl {U : Set c.Punctured} (hU : IsOpen U)
    (hdisj : ∀ z, c.boundaryMap z ∉ U) :
    IsOpen (inl c d a '' U) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inl c d a '' U) = Sum.inl '' U := by
    ext s
    constructor
    · rintro ⟨p, hpU, hp⟩
      cases s with
      | inl x =>
          refine ⟨x, ?_, rfl⟩
          rwa [← (inl_injective c d a hp)]
      | inr y =>
          obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c d a p y).mp hp
          exact absurd (hz.symm ▸ hpU) (hdisj z)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance] (inl c d a '' U)
  rw [isOpen_coinduced, hcoe]
  exact isOpenMap_inl U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inl ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inl

theorem isOpen_image_inr {V : Set d.Punctured} (hV : IsOpen V)
    (hdisj : ∀ z, d.boundaryMap z ∉ V) :
    IsOpen (inr c d a '' V) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inr c d a '' V) = Sum.inr '' V := by
    ext s
    constructor
    · rintro ⟨q, hqV, hq⟩
      cases s with
      | inr y =>
          refine ⟨y, ?_, rfl⟩
          rwa [← (inr_injective c d a hq)]
      | inl x =>
          obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c d a x q).mp hq.symm
          exact absurd (hz.symm ▸ hqV) (hdisj (a z))
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance] (inr c d a '' V)
  rw [isOpen_coinduced, hcoe]
  exact isOpenMap_inr V hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inr ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_inr

theorem isOpen_image_union {U : Set c.Punctured} {V : Set d.Punctured} (hU : IsOpen U)
    (hV : IsOpen V) (hdisjU : ∀ z, c.boundaryMap z ∉ U)
    (hdisjV : ∀ z, d.boundaryMap z ∉ V) :
    IsOpen (inl c d a '' U ∪ inr c d a '' V) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inl c d a '' U ∪ inr c d a '' V) = Sum.inl '' U ∪ Sum.inr '' V := by
    ext s
    constructor
    · rintro (⟨p, hpU, hp⟩ | ⟨q, hqV, hq⟩)
      · cases s with
        | inl x =>
            refine Or.inl ⟨x, ?_, rfl⟩
            rwa [← (inl_injective c d a hp)]
        | inr y =>
            obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c d a p y).mp hp
            exact absurd (hz.symm ▸ hpU) (hdisjU z)
      · cases s with
        | inl x =>
            obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c d a x q).mp hq.symm
            exact absurd (hz.symm ▸ hqV) (hdisjV (a z))
        | inr y =>
            refine Or.inr ⟨y, ?_, rfl⟩
            rwa [← (inr_injective c d a hq)]
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance]
    (inl c d a '' U ∪ inr c d a '' V)
  rw [isOpen_coinduced, hcoe]
  exact (isOpenMap_inl U hU).union (isOpenMap_inr V hV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_union ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_image_union

end ConnectedSumQuotient

theorem frontier_half_le_subset_eq_zero {α : Type*} [TopologicalSpace α] (f : α → ℝ)
    (hf : Continuous f) : frontier {p : α | 0 ≤ f p} ⊆ {p | f p = 0} := by
  intro p hp
  have hcl : p ∈ closure {q : α | 0 ≤ f q} := frontier_subset_closure hp
  have hcl' : p ∈ closure ({q : α | 0 ≤ f q}ᶜ) := by
    have h : p ∈ frontier ({q : α | 0 ≤ f q}ᶜ) := by
      rwa [frontier_compl]
    exact frontier_subset_closure h
  have hge : 0 ≤ f p :=
    closure_minimal (fun q hq => hq) (isClosed_le continuous_const hf) hcl
  have hle : f p ≤ 0 := by
    refine closure_minimal (fun q hq => ?_) (isClosed_le hf continuous_const) hcl'
    have hq' : ¬ (0 ≤ f q) := hq
    exact le_of_lt (not_le.mp hq')
  exact le_antisymm hle hge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.frontier_half_le_subset_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.frontier_half_le_subset_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.frontier_half_le_subset_eq_zero ``Submission.DifferentialGeometry.Topology.frontier_half_le_subset_eq_zero

end DifferentialGeometry.Topology
