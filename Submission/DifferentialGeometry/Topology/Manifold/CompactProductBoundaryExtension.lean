import Submission.DifferentialGeometry.Topology.Manifold.HalfClosedIntervalExtension
import Submission.DifferentialGeometry.Topology.Manifold.ProductBoundaryExtension
import Submission.DifferentialGeometry.Topology.Manifold.SmoothExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

variable {F HS S E HM M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HS] {J : ModelWithCorners ℝ F HS} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace HS S] [IsManifold J ∞ S]
  [T2Space S] [CompactSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

theorem exists_contMDiffOn_extension_prod_Ico {r w : ℝ}
    (hr : 0 ≤ r) (hrw : r < w) (c : S × _root_.Set.Ico (0 : ℝ) w → M)
    (hc : letI := Manifold.halfClosedIntervalChartedSpace (hr.trans_lt hrw)
      ContMDiff (J.prod (𝓡∂ 1)) I ∞ c) :
    ∃ Φ : C(S × ℝ, M), ∃ N : Set (S × ℝ), IsOpen N ∧
      (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) r) ⊆ N ∧ ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ Φ N ∧
      ∀ (s : S) (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) r),
        Φ (s, t) = c (s, ⟨t, ht.1, ht.2.trans_lt hrw⟩) := by
  let a := (r + w) / 2
  have hra : r < a := by dsimp only [a]; linarith
  have ha : 0 < a := hr.trans_lt hra
  have haw : a < w := by dsimp only [a]; linarith
  obtain ⟨g, hg, hgc⟩ := Manifold.exists_contMDiffOn_extension_prod_Icc ha.le haw c hc
  let K : Set (S × ℝ) := _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) r
  have hK : IsCompact K := isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hloc : ∀ x ∈ K, ∃ U : S × ℝ → M, ∃ V : Set (S × ℝ),
      IsOpen V ∧ x ∈ V ∧ ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ U V ∧ _root_.Set.EqOn U g (K ∩ V) := by
    intro x hx
    by_cases ht : x.2 = 0
    · let A : Set (S × ℝ) := _root_.Set.univ ×ˢ _root_.Set.Iio a
      have hA : IsOpen A := isOpen_univ.prod isOpen_Iio
      have hxA : (x.1, (0 : ℝ)) ∈ A := ⟨mem_univ _, ha⟩
      have hgA : ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ g
          (A ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) :=
        hg.mono (fun y hy => ⟨mem_univ _, hy.2.2, hy.1.2.le⟩)
      obtain ⟨V, hV, hxV, _, U, hU, heq⟩ :=
        exists_contMDiffOn_extension_across_product_boundary hA hxA hgA
      refine ⟨U, V, hV, ?_, hU, ?_⟩
      · exact (show x = (x.1, (0 : ℝ)) from Prod.ext rfl ht).symm ▸ hxV
      · intro y hy
        exact heq ⟨hy.2, _root_.Set.mem_univ _, hy.1.2.1⟩
    · have htpos : 0 < x.2 := lt_of_le_of_ne hx.2.1 (Ne.symm ht)
      let V : Set (S × ℝ) := _root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) a
      refine ⟨g, V, isOpen_univ.prod isOpen_Ioo,
        ⟨mem_univ _, htpos, hx.2.2.trans_lt hra⟩,
        hg.mono (fun y hy => ⟨mem_univ _, hy.2.1.le, hy.2.2.le⟩), ?_⟩
      exact fun _ _ => rfl
  obtain ⟨Φ, hΦ, hΦg, N, hN, hKN, hΦN⟩ :=
    exists_contMDiffOn_eqOn_of_locally_extendable (J := J.prod 𝓘(ℝ)) (I := I)
      (n := ⊤) g.continuous hK hloc
  refine ⟨⟨Φ, hΦ⟩, N, hN, hKN, hΦN, ?_⟩
  intro s t ht
  exact (hΦg ⟨mem_univ _, ht⟩).trans (hgc s t ⟨ht.1, ht.2.trans hra.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiffOn_extension_prod_Ico then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiffOn_extension_prod_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiffOn_extension_prod_Ico ``Submission.DifferentialGeometry.Topology.exists_contMDiffOn_extension_prod_Ico

end DifferentialGeometry.Topology
