import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalCoorientation
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.BoundaryNormalDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E2 target :: scope.openDecls } }
private abbrev EC := E2 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.EC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.EC target :: scope.openDecls } }

private theorem deriv_nonpos_of_eventually_le_on_right
    {f : ℝ → ℝ} {r : ℝ} (hf : DifferentiableAt ℝ f r)
    (hside : ∀ᶠ t in 𝓝 r, r ≤ t → f t ≤ f r) : deriv f r ≤ 0 := by
  have hmax : IsLocalMaxOn f (_root_.Set.Ici r) r := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hside]
      with t ht hs
    exact hs ht
  have ht : (1 : ℝ) ∈ posTangentConeAt (_root_.Set.Ici r) r := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with t ht
    change r ≤ r + t * 1
    change 0 < t at ht
    linarith
  have h := hmax.hasFDerivWithinAt_nonpos hf.hasDerivAt.hasFDerivAt.hasFDerivWithinAt ht
  simpa using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.deriv_nonpos_of_eventually_le_on_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.deriv_nonpos_of_eventually_le_on_right target :: scope.openDecls } }

private theorem deriv_nonpos_of_eventually_ge_on_left
    {f : ℝ → ℝ} {r : ℝ} (hf : DifferentiableAt ℝ f r)
    (hside : ∀ᶠ t in 𝓝 r, t ≤ r → f r ≤ f t) : deriv f r ≤ 0 := by
  have hmin : IsLocalMinOn f (_root_.Set.Iic r) r := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hside]
      with t ht hs
    exact hs ht
  have ht : (-1 : ℝ) ∈ posTangentConeAt (_root_.Set.Iic r) r := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with t ht
    change r + t * (-1) ≤ r
    change 0 < t at ht
    linarith
  have h := hmin.hasFDerivWithinAt_nonneg hf.hasDerivAt.hasFDerivAt.hasFDerivWithinAt ht
  simpa using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.deriv_nonpos_of_eventually_ge_on_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.deriv_nonpos_of_eventually_ge_on_left target :: scope.openDecls } }

theorem axial_derivative_neg_at_lower_of_slab_avoidance
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, (A (p, 0)).2 = 0)
    (havoid : ∀ q ∈ A.source, q.2 ∈ _root_.Set.Ioo (0 : ℝ) 1 → (A q).2 ∉ _root_.Set.Icc (0 : ℝ) 1)
    (p : S2) : deriv (fun t => (A (p, t)).2) 0 < 0 := by
  have hdiff : DifferentiableAt ℝ (fun t => (A (p, t)).2) 0 := by
    apply mdifferentiableAt_iff_differentiableAt.mp
    exact (mdifferentiableAt_snd.comp (p, (0 : ℝ))
      (A.mdifferentiableAt (by simp) (hsource p))).comp 0
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hcont := hdiff.continuousAt
  have hsource' : ∀ᶠ t in 𝓝 (0 : ℝ), (p, t) ∈ A.source :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (A.open_source.mem_nhds (hsource p))
  have hheight : ∀ᶠ t in 𝓝 (0 : ℝ), (A (p, t)).2 < 1 :=
    hcont.eventually (Iio_mem_nhds (by simpa only [hzero] using (show (0 : ℝ) < 1 by norm_num)))
  have hside : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t → (A (p, t)).2 ≤ (A (p, 0)).2 := by
    filter_upwards [hsource', hheight, Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)]
      with t ht hheight ht1 ht0
    rw [hzero]
    rcases eq_or_lt_of_le ht0 with ht0 | ht0
    · simpa only [← ht0] using (hzero p).le
    · by_contra h
      exact havoid (p, t) ht ⟨ht0, ht1⟩ ⟨(lt_of_not_ge h).le, hheight.le⟩
  exact lt_of_le_of_ne (deriv_nonpos_of_eventually_le_on_right hdiff hside)
    (axial_derivative_ne_zero_of_constant_section A 0 hsource hzero p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_lower_of_slab_avoidance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_lower_of_slab_avoidance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_lower_of_slab_avoidance ``Submission.DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_lower_of_slab_avoidance

theorem axial_derivative_neg_at_upper_of_slab_avoidance
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 1) ∈ A.source)
    (hone : ∀ p : S2, (A (p, 1)).2 = 1)
    (havoid : ∀ q ∈ A.source, q.2 ∈ _root_.Set.Ioo (0 : ℝ) 1 → (A q).2 ∉ _root_.Set.Icc (0 : ℝ) 1)
    (p : S2) : deriv (fun t => (A (p, t)).2) 1 < 0 := by
  have hdiff : DifferentiableAt ℝ (fun t => (A (p, t)).2) 1 := by
    apply mdifferentiableAt_iff_differentiableAt.mp
    exact (mdifferentiableAt_snd.comp (p, (1 : ℝ))
      (A.mdifferentiableAt (by simp) (hsource p))).comp 1
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hcont := hdiff.continuousAt
  have hsource' : ∀ᶠ t in 𝓝 (1 : ℝ), (p, t) ∈ A.source :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (A.open_source.mem_nhds (hsource p))
  have hheight : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < (A (p, t)).2 :=
    hcont.eventually (Ioi_mem_nhds (by simpa only [hone] using (show (0 : ℝ) < 1 by norm_num)))
  have hside : ∀ᶠ t in 𝓝 (1 : ℝ), t ≤ 1 → (A (p, 1)).2 ≤ (A (p, t)).2 := by
    filter_upwards [hsource', hheight, Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)]
      with t ht hheight ht0 ht1
    rw [hone]
    rcases eq_or_lt_of_le ht1 with ht1 | ht1
    · simpa only [ht1] using (hone p).ge
    · by_contra h
      exact havoid (p, t) ht ⟨ht0, ht1⟩ ⟨hheight.le, (lt_of_not_ge h).le⟩
  exact lt_of_le_of_ne (deriv_nonpos_of_eventually_ge_on_left hdiff hside)
    (axial_derivative_ne_zero_of_constant_section A 1 hsource hone p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_upper_of_slab_avoidance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_upper_of_slab_avoidance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_upper_of_slab_avoidance ``Submission.DifferentialGeometry.Topology.Manifold.axial_derivative_neg_at_upper_of_slab_avoidance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem axial_derivative_neg_of_closed_slab_overlap
    (a c : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (ha : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ c.source)
    (hoverlap : (a '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩
      (c '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ⊆
      (c '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∪ (c '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))))
    (f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞)
    (hzero : ∀ z : S2, a (z, 0) = c (z, 0))
    (hone : ∀ z : S2, a (z, 1) = c (f.symm z, 1)) :
    (∀ z : S2, deriv (fun t => (c.symm (a (z, t))).2) 0 < 0) ∧
      (∀ z : S2, deriv (fun t => (c.symm (a (z, t))).2) 1 < 0) := by
  let A := a.trans c.symm
  have hA0 (p : S2) : (p, 0) ∈ A.source := by
    refine ⟨ha ⟨mem_univ _, by norm_num⟩, ?_⟩
    change a (p, 0) ∈ c.target
    rw [hzero]
    exact c.map_source' (hc ⟨mem_univ _, by norm_num⟩)
  have hA1 (p : S2) : (p, 1) ∈ A.source := by
    refine ⟨ha ⟨mem_univ _, by norm_num⟩, ?_⟩
    change a (p, 1) ∈ c.target
    rw [hone]
    exact c.map_source' (hc ⟨mem_univ _, by norm_num⟩)
  have hzero' (p : S2) : (A (p, 0)).2 = 0 := by
    change (c.symm (a (p, 0))).2 = 0
    rw [hzero]
    exact congrArg Prod.snd (c.left_inv' (hc (show (p, 0) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 from
      ⟨mem_univ _, by norm_num⟩)))
  have hone' (p : S2) : (A (p, 1)).2 = 1 := by
    change (c.symm (a (p, 1))).2 = 1
    rw [hone]
    exact congrArg Prod.snd (c.left_inv' (hc (show (f.symm p, 1) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 from
      ⟨mem_univ _, by norm_num⟩)))
  have havoid : ∀ q ∈ A.source, q.2 ∈ _root_.Set.Ioo (0 : ℝ) 1 → (A q).2 ∉ _root_.Set.Icc (0 : ℝ) 1 := by
    intro q hq hq2 hheight
    have hac : a q ∈ (a '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩
        (c '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
      refine ⟨⟨q, ⟨mem_univ _, hq2.1.le, hq2.2.le⟩, rfl⟩, ?_⟩
      exact ⟨c.symm (a q), ⟨mem_univ _, hheight⟩, c.right_inv' hq.2⟩
    rcases hoverlap hac with h | h
    · rcases h with ⟨⟨p, t⟩, ⟨_, ht⟩, heq⟩
      have ht : t = 0 := ht
      subst t
      have he : (p, (0 : ℝ)) = q :=
        a.toPartialEquiv.injOn (ha ⟨mem_univ _, by norm_num⟩) hq.1
          ((hzero p).trans heq)
      have he' := congrArg Prod.snd he
      exact (ne_of_gt hq2.1) he'.symm
    · rcases h with ⟨⟨p, t⟩, ⟨_, ht⟩, heq⟩
      have ht : t = 1 := ht
      subst t
      have heq' : a (f p, 1) = a q := by
        rw [hone, f.symm_apply_apply]
        exact heq
      have he : (f p, (1 : ℝ)) = q :=
        a.toPartialEquiv.injOn (ha ⟨mem_univ _, by norm_num⟩) hq.1 heq'
      have he' := congrArg Prod.snd he
      exact (ne_of_lt hq2.2) he'.symm
  exact ⟨axial_derivative_neg_at_lower_of_slab_avoidance A hA0 hzero' havoid,
    axial_derivative_neg_at_upper_of_slab_avoidance A hA1 hone' havoid⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.axial_derivative_neg_of_closed_slab_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.axial_derivative_neg_of_closed_slab_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.axial_derivative_neg_of_closed_slab_overlap ``Submission.DifferentialGeometry.Topology.Manifold.axial_derivative_neg_of_closed_slab_overlap

end DifferentialGeometry.Topology.Manifold
