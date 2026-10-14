import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.SlabMatching

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private structure MatchedSlab
    (P : PartialDiffeomorph IC I (S2 × ℝ) M ∞) where
  map : PartialDiffeomorph IC I (S2 × ℝ) M ∞
  source : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ map.source
  image : map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)
  upperParam : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2
  upper : ∀ z, map (z, 1) = P (upperParam z, 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.MatchedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.MatchedSlab target :: scope.openDecls } }

private theorem MatchedSlab.exists_next
    {P Q : PartialDiffeomorph IC I (S2 × ℝ) M ∞}
    (S : MatchedSlab P) (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hQ : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q.source)
    (hseam : ∀ z, Q (z, 0) = P (η z, 1))
    (hmeet : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ T : MatchedSlab Q,
      ∃ V : Set (S2 × ℝ), IsOpen V ∧ _root_.Set.univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
        ∀ z ∈ V, T.map z = S.map (z.1, z.2 + 1) := by
  let μ := S.upperParam.trans η.symm
  let D := μ.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let Q' := D.toPartialDiffeomorph.trans Q
  have hD (z : S2 × ℝ) : D z = (μ z.1, z.2) := rfl
  have hband : D '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, hx.2⟩
    · intro hz
      refine ⟨(μ.symm z.1, z.2), ⟨mem_univ _, hz.2⟩, ?_⟩
      exact Prod.ext (μ.apply_symm_apply _) rfl
  have hQ'source : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q'.source := by
    intro z hz
    refine ⟨mem_univ _, hQ ?_⟩
    exact ⟨mem_univ _, hz.2⟩
  have hQ'image : Q' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    calc
      Q' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
          Q '' (D '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
        rw [_root_.Set.image_image]
        rfl
      _ = _ := by rw [hband]
  have hQ'zero (z) : Q' (z, 0) = S.map (z, 1) := by
    change Q (η.symm (S.upperParam z), 0) = S.map (z, 1)
    rw [hseam]
    exact (congrArg (fun q => P (q, 1))
      (show η (η.symm (S.upperParam z)) = S.upperParam z from
        η.apply_symm_apply _)).trans (S.upper z).symm
  have hface : S.map '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) = P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩
      have : t = 1 := ht
      subst t
      exact ⟨(S.upperParam z, 1), ⟨mem_univ _, rfl⟩, (S.upper z).symm.trans hzx⟩
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩
      have : t = 1 := ht
      subst t
      refine ⟨(S.upperParam.symm z, 1), ⟨mem_univ _, rfl⟩, (S.upper _).trans ?_⟩
      exact (congrArg (fun q => P (q, 1))
        (show S.upperParam (S.upperParam.symm z) = z from
          S.upperParam.apply_symm_apply z)).trans hzx
  have hmeet' : S.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      S.map '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by rw [S.image, hQ'image, hface]; exact hmeet
  obtain ⟨r, hr, F, hF, _, hfix, hFband⟩ :=
    exists_slab_collar_matching S.map Q' S.source hQ'source hQ'zero hmeet'
  let R := F.toPartialDiffeomorph.trans Q'
  have hRsource : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ R.source := by
    intro z hz
    exact ⟨mem_univ _, hQ'source (hFband ▸ _root_.Set.mem_image_of_mem F hz)⟩
  have hRimage : R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    calc
      R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
          Q' '' (F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
        rw [_root_.Set.image_image]
        rfl
      _ = _ := by rw [hFband, hQ'image]
  have hRupper (z) : R (z, 1) = Q (μ z, 1) := by
    change Q' (F (z, 1)) = _
    rw [hfix (z, 1) (by norm_num)]
    rfl
  let T : MatchedSlab Q := ⟨R, hRsource, hRimage, μ, hRupper⟩
  refine ⟨T, _root_.Set.univ ×ˢ _root_.Set.Ioo (-r) r, isOpen_univ.prod isOpen_Ioo, ?_, ?_⟩
  · rintro ⟨z, t⟩ ⟨_, ht⟩
    have : t = 0 := ht
    subst t
    exact ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩
  · intro z hz
    have hh := (hF z (abs_le.mpr ⟨hz.2.1.le, hz.2.2.le⟩)).2
    exact hh.trans (congrArg S.map (Prod.ext rfl (add_comm 1 z.2)))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.Manifold.MatchedSlab
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.MatchedSlab.exists_next
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.MatchedSlab.exists_next target :: scope.openDecls } }

theorem exists_compatible_slab_parametrizations
    (P : ℕ → PartialDiffeomorph IC I (S2 × ℝ) M ∞)
    (η : ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hmeet : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ Q : ℕ → PartialDiffeomorph IC I (S2 × ℝ) M ∞,
      Q 0 = P 0 ∧
      (∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (Q n).source) ∧
      (∀ n, Q n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      (∀ n, ∃ μ : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2, ∀ z, Q n (z, 1) = P n (μ z, 1)) ∧
      ∀ n, ∃ V : Set (S2 × ℝ), IsOpen V ∧ _root_.Set.univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
        ∀ z ∈ V, Q (n + 1) z = Q n (z.1, z.2 + 1) := by
  classical
  let S₀ : MatchedSlab (P 0) :=
    ⟨P 0, hsource 0, rfl, Diffeomorph.refl (𝓡 2) S2 ∞, fun _ => rfl⟩
  have hnext (n : ℕ) (S : MatchedSlab (P n)) :=
    S.exists_next (η n) (hsource (n + 1)) (hseam n) (hmeet n)
  let next (n : ℕ) (S : MatchedSlab (P n)) : MatchedSlab (P (n + 1)) :=
    Classical.choose (hnext n S)
  let seq : ∀ n, MatchedSlab (P n) := fun n => Nat.rec S₀ next n
  refine ⟨fun n => (seq n).map, rfl, fun n => (seq n).source,
    fun n => (seq n).image, fun n => ⟨(seq n).upperParam, (seq n).upper⟩, ?_⟩
  intro n
  exact Classical.choose_spec (hnext n (seq n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_compatible_slab_parametrizations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_compatible_slab_parametrizations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_compatible_slab_parametrizations ``Submission.DifferentialGeometry.Topology.Manifold.exists_compatible_slab_parametrizations

end DifferentialGeometry.Topology.Manifold
