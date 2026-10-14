import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentCarrierBandStep
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentMotionComposition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34RetainedTraceNonempty

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_singleton_carrier_family_of_current_trace
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (I : Set (Fin (cnt e)))
    (Ψ : M₂ ≃ₜ M₂) {K : Set M₂}
    (hK : IsCompact K) (hKS : K ⊆ interior (Sp e)) (hfix : _root_.Set.EqOn Ψ id Kᶜ)
    (hΨ : IsPLOn 3 3 Ψ (interior (G (ends e).1 '' Cc (ends e).1)))
    (hArim : Disjoint K (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)))
    (hBrim : Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hout : Disjoint K
      (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)))
    (hkeep : ∀ i : I, Disjoint K (Pg e i.1.val))
    (hcarry : ∀ i : I, CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e))
    (htrace : G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) =
      ⋃ i : I, Pg e i.1.val) :
    ∃ (J : Set (Fin (cnt e))) (K' : Set M₂) (Φ : M₂ ≃ₜ M₂),
      J ⊆ I ∧ Nat.card J = 1 ∧ IsCompact K' ∧ K' ⊆ interior (Sp e) ∧
      _root_.Set.EqOn Φ id K'ᶜ ∧ IsPLOn 3 3 Φ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
      Disjoint K' (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint K' (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      Disjoint K' (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) ∧
      (∀ j : J, Disjoint K' (Pg e j.1.val)) ∧
      (∀ j : J, ∀ x ∈ Pg e j.1.val, Φ =ᶠ[𝓝 x] id) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ Φ '' (G (ends e).2 '' CpBd (ends e).2) =
        ⋃ j : J, Pg e j.1.val := by
  classical
  by_cases hlt : 1 < Nat.card I
  · obtain ⟨J, Φ, K₁, hdec, hK₁, hK₁S, hfix₁, hΦ, hArim₁, hBrim₁, hout₁,
        hkeep₁, -, htrace₁⟩ :=
      exists_section34_current_carrier_band_step hprep hpack e I hlt Ψ hK hKS hfix hΨ
        hBrim hout hkeep hcarry htrace
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
    obtain ⟨-, -, -, htube, -⟩ := id hpack
    have hSpCc : Sp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
      rw [(htube e).1]
      exact _root_.Set.image_mono (hSnCc e _ (Or.inl rfl))
    have hZ := disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨hArim, hBrim⟩, hout⟩
    have hZ₁ := disjoint_union_right.mpr
      ⟨disjoint_union_right.mpr ⟨hArim₁, hBrim₁⟩, hout₁⟩
    obtain ⟨hIsub, -, hK', hK'S, hfix', hPL', -, -, hkeep', -, htrace'⟩ :=
      supported_second_trace_motion_comp (Γ := fun k : Fin (cnt e) => Pg e k.val)
        Ψ Φ hK hK₁ hKS hK₁S (interior_mono hSpCc)
        hfix hfix₁ hΨ hΦ hZ hZ₁ I J hkeep hkeep₁ htrace₁
    have hArim' := disjoint_union_left.mpr ⟨hArim, hArim₁⟩
    have hBrim' := disjoint_union_left.mpr ⟨hBrim, hBrim₁⟩
    have hout' := disjoint_union_left.mpr ⟨hout, hout₁⟩
    have hcarry' (i : Subtype.val '' J) :
        CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e) := hcarry ⟨i.1, hIsub i.2⟩
    obtain ⟨J', K', Φ', hJ', hrest⟩ :=
      exists_section34_singleton_carrier_family_of_current_trace hprep hpack e
        (Subtype.val '' J) (Ψ.trans Φ) hK' hK'S hfix' hPL' hArim' hBrim' hout'
        hkeep' hcarry' htrace'
    exact ⟨J', K', Φ', hJ'.trans hIsub, hrest⟩
  · have hfixA : _root_.Set.EqOn Ψ id (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) :=
      fun _ hx => hfix (disjoint_right.mp hArim hx)
    have hne := section34_retained_trace_nonempty hprep hpack e Ψ hfixA
      (Γ := fun k : Fin (cnt e) => Pg e k.val) I htrace
    let _ : Nonempty I := hne.to_subtype
    have hpos : 0 < Nat.card I := Nat.card_pos
    refine ⟨I, K, Ψ, Subset.rfl, by omega, hK, hKS, hfix, hΨ, hArim, hBrim, hout,
      hkeep, ?_, htrace⟩
    intro i x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds
      (disjoint_right.mp (hkeep i) hx)] with y hy
    exact hfix hy
termination_by Nat.card I
decreasing_by
  simpa only [Nat.card_image_of_injective Subtype.val_injective] using hdec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_singleton_carrier_family_of_current_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_singleton_carrier_family_of_current_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_singleton_carrier_family_of_current_trace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_singleton_carrier_family_of_current_trace

theorem exists_section34_single_carrier_trace_of_current_family
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (I : Set (Fin (cnt e)))
    (Ψ : M₂ ≃ₜ M₂) {K : Set M₂}
    (hK : IsCompact K) (hKS : K ⊆ interior (Sp e)) (hfix : _root_.Set.EqOn Ψ id Kᶜ)
    (hΨ : IsPLOn 3 3 Ψ (interior (G (ends e).1 '' Cc (ends e).1)))
    (hArim : Disjoint K (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)))
    (hBrim : Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hout : Disjoint K
      (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)))
    (hkeep : ∀ i : I, Disjoint K (Pg e i.1.val))
    (hcarry : ∀ i : I, CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e))
    (htrace : G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) =
      ⋃ i : I, Pg e i.1.val) :
    ∃ (i : I) (K' : Set M₂) (Φ : M₂ ≃ₜ M₂),
      IsCompact K' ∧ K' ⊆ interior (Sp e) ∧ _root_.Set.EqOn Φ id K'ᶜ ∧
      IsPLOn 3 3 Φ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
      Disjoint K' (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint K' (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      Disjoint K' (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) ∧
      Disjoint K' (Pg e i.1.val) ∧ (∀ x ∈ Pg e i.1.val, Φ =ᶠ[𝓝 x] id) ∧
      CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ Φ '' (G (ends e).2 '' CpBd (ends e).2) =
        Pg e i.1.val := by
  obtain ⟨J, K', Φ, hJI, hcard, hK', hK'S, hfix', hΦ, hArim', hBrim', hout',
      hkeep', hgerm, htrace'⟩ :=
    exists_section34_singleton_carrier_family_of_current_trace hprep hpack e I Ψ hK hKS
      hfix hΨ hArim hBrim hout hkeep hcarry htrace
  obtain ⟨i, hi⟩ := Nat.card_eq_one_iff_exists.mp hcard
  refine ⟨⟨i.1, hJI i.2⟩, K', Φ, hK', hK'S, hfix', hΦ, hArim', hBrim', hout',
    hkeep' i, hgerm i, hcarry ⟨i.1, hJI i.2⟩, htrace'.trans ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact hi j ▸ hj
  · exact _root_.Set.subset_iUnion (fun j : J => Pg e j.1.val) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_single_carrier_trace_of_current_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_single_carrier_trace_of_current_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_single_carrier_trace_of_current_family ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_single_carrier_trace_of_current_family

end DifferentialGeometry.Topology.PiecewiseLinear
