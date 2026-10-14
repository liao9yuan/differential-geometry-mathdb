import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {f : ℝ → ∀ x, V x} {m n : WithTop ℕ∞}

open _root_.ContMDiffAt in
theorem ContMDiffAt.fiberwise_time_deriv {p₀ : ℝ × M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : _root_.Bundle.TotalSpace F V)) p₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, deriv (fun t => f t p.2) p.1⟩ : _root_.Bundle.TotalSpace F V)) p₀ := by
  rw [_root_.Bundle.contMDiffAt_totalSpace] at hf ⊢
  refine ⟨contMDiffAt_snd, ?_⟩
  let e := _root_.FiberBundle.trivializationAt F V p₀.2
  have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun p : ℝ × M => (e ⟨p.2, f p.1 p.2⟩).2) p₀ := hf.2
  have hd := DifferentialGeometry.timeDeriv_smoothAt hcoord hmn
  apply hd.congr_of_eventuallyEq
  have hbase : ∀ᶠ p : ℝ × M in 𝓝 p₀, p.2 ∈ e.baseSet :=
    continuous_snd.continuousAt (e.open_baseSet.mem_nhds
      (_root_.FiberBundle.mem_baseSet_trivializationAt F V p₀.2))
  filter_upwards [hbase] with p hp
  let L := e.continuousLinearEquivAt ℝ p.2 hp
  have hL : ∀ v : V p.2, L v = (e ⟨p.2, v⟩).2 := by
    intro v
    rw [show (L : V p.2 → F) = e.continuousLinearMapAt ℝ p.2 from
      e.coe_continuousLinearEquivAt_eq hp]
    exact e.continuousLinearMapAt_apply_of_mem ℝ hp v
  have heq : (fun t => (e ⟨p.2, f t p.2⟩).2) = L ∘ (fun t => f t p.2) := by
    funext t
    exact (hL _).symm
  change (e ⟨p.2, deriv (fun t => f t p.2) p.1⟩).2 =
    deriv (fun t => (e ⟨p.2, f t p.2⟩).2) p.1
  rw [heq, ← hL]
  change L (fderiv ℝ (fun t => f t p.2) p.1 1) =
    fderiv ℝ (L ∘ (fun t => f t p.2)) p.1 1
  rw [L.comp_fderiv]
  rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.fiberwise_time_deriv then
    throwError "Refusing to shadow existing declaration ContMDiffAt.fiberwise_time_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.fiberwise_time_deriv ``Submission.ContMDiffAt.fiberwise_time_deriv

open _root_.ContMDiffOn in
theorem ContMDiffOn.fiberwise_time_deriv {s : Set (ℝ × M)}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : _root_.Bundle.TotalSpace F V)) s)
    (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, deriv (fun t => f t p.2) p.1⟩ : _root_.Bundle.TotalSpace F V)) s := by
  intro p hp
  exact ((hf.contMDiffAt (hs.mem_nhds hp)).fiberwise_time_deriv hmn).contMDiffWithinAt

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.fiberwise_time_deriv then
    throwError "Refusing to shadow existing declaration ContMDiffOn.fiberwise_time_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.fiberwise_time_deriv ``Submission.ContMDiffOn.fiberwise_time_deriv

open _root_.ContMDiff in
theorem ContMDiff.fiberwise_time_deriv
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : _root_.Bundle.TotalSpace F V)))
    (hmn : m + 1 ≤ n) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, deriv (fun t => f t p.2) p.1⟩ : _root_.Bundle.TotalSpace F V)) := by
  intro p
  exact hf.contMDiffAt.fiberwise_time_deriv hmn

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiff
  let env ← Lean.getEnv
  if env.contains `ContMDiff.fiberwise_time_deriv then
    throwError "Refusing to shadow existing declaration ContMDiff.fiberwise_time_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.fiberwise_time_deriv ``Submission.ContMDiff.fiberwise_time_deriv

open _root_.ContMDiffOn in
theorem ContMDiffOn.fiberwise_time_derivWithin {s : Set ℝ} {u : Set M}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : _root_.Bundle.TotalSpace F V)) (s ×ˢ u))
    (hs : UniqueDiffOn ℝ s) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, derivWithin (fun t => f t p.2) s p.1⟩ : _root_.Bundle.TotalSpace F V))
      (s ×ˢ u) := by
  intro p₀ hp₀
  have hf₀ := hf p₀ hp₀
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace] at hf₀ ⊢
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let e := _root_.FiberBundle.trivializationAt F V p₀.2
  let C : ℝ × M → F := fun p => (e ⟨p.2, f p.1 p.2⟩).2
  have hcoord : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n C (s ×ˢ u) p₀ := hf₀.2
  have harg : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) n (fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      ((s ×ˢ u) ×ˢ s) (p₀, p₀.1) :=
    contMDiffWithinAt_snd.prodMk contMDiffWithinAt_fst.snd
  have hC : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, F) n (fun q : (ℝ × M) × ℝ => C (q.2, q.1.2))
      ((s ×ˢ u) ×ˢ s) (p₀, p₀.1) :=
    hcoord.comp (f := fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      (g := C) (p₀, p₀.1) harg (fun q hq => ⟨hq.2, hq.1.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F))
    (f := fun (p : ℝ × M) (t : ℝ) => C (t, p.2))
    (g := fun p : ℝ × M => p.1) (g₁ := fun p : ℝ × M => p)
    (g₂ := fun _ : ℝ × M => (1 : ℝ)) (x₀ := p₀)
    hC contMDiffWithinAt_fst contMDiffWithinAt_id contMDiffWithinAt_const hmn
    (_root_.Set.mapsTo_id _) hp₀ (fun _ hp => hp.1) hs.uniqueMDiffOn
  have hd' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) m
      (fun p : ℝ × M => derivWithin (fun t => C (t, p.2)) s p.1) (s ×ˢ u) p₀ := by
    simpa only [inTangentCoordinates_model_space, mfderivWithin_eq_fderivWithin,
      derivWithin] using hd
  have heq (p : ℝ × M) (hp : p ∈ s ×ˢ u) (hb : p.2 ∈ e.baseSet) :
      (e ⟨p.2, derivWithin (fun t => f t p.2) s p.1⟩).2 =
        derivWithin (fun t => C (t, p.2)) s p.1 := by
    let L := e.continuousLinearEquivAt ℝ p.2 hb
    have hL : ∀ v : V p.2, L v = (e ⟨p.2, v⟩).2 := by
      intro v
      rw [show (L : V p.2 → F) = e.continuousLinearMapAt ℝ p.2 from
        e.coe_continuousLinearEquivAt_eq hb]
      exact e.continuousLinearMapAt_apply_of_mem ℝ hb v
    have hcomp : (fun t => C (t, p.2)) = L ∘ (fun t => f t p.2) := by
      funext t
      exact (hL _).symm
    rw [hcomp, ← hL]
    change L (fderivWithin ℝ (fun t => f t p.2) s p.1 1) =
      fderivWithin ℝ (L ∘ (fun t => f t p.2)) s p.1 1
    rw [L.comp_fderivWithin (hs p.1 hp.1)]
    rfl
  apply hd'.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p : ℝ × M in 𝓝[s ×ˢ u] p₀, p.2 ∈ e.baseSet :=
      continuousWithinAt_snd (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt F V p₀.2))
    filter_upwards [self_mem_nhdsWithin, hbase] with p hp hb
    exact heq p hp hb
  · exact heq p₀ hp₀ (_root_.FiberBundle.mem_baseSet_trivializationAt F V p₀.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.fiberwise_time_derivWithin then
    throwError "Refusing to shadow existing declaration ContMDiffOn.fiberwise_time_derivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.fiberwise_time_derivWithin ``Submission.ContMDiffOn.fiberwise_time_derivWithin

omit [IsManifold I 1 M] in
open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.fiberwise_time_contDiffWithinAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {f : ℝ → ∀ x, V x} {t : ℝ} {x : M} {n : WithTop ℕ∞}
    {s : Set ℝ} {u : Set M}
    (hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : _root_.Bundle.TotalSpace F V)) (s ×ˢ u) (t, x)) (hxU : x ∈ u) :
    ContDiffWithinAt ℝ n (fun r => f r x) s t := by
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace] at hf
  let e := _root_.FiberBundle.trivializationAt F V x
  have hx : x ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V x
  have hcoord : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun p : ℝ × M => (e ⟨p.2, f p.1 p.2⟩).2) (s ×ˢ u) (t, x) := hf.2
  have hmaps : _root_.Set.MapsTo (fun r : ℝ => (r, x)) s (s ×ˢ u) := fun r hr => ⟨hr, hxU⟩
  have hfixed := hcoord.comp (f := fun r : ℝ => (r, x)) t
    (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const) hmaps
  have hback := (e.symmL ℝ x).contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt t hfixed
  rw [← contMDiffWithinAt_iff_contDiffWithinAt]
  have heq (r : ℝ) : f r x = e.symmL ℝ x (e ⟨x, f r x⟩).2 := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hx]
    exact (e.symmL_continuousLinearMapAt hx _).symm
  exact hback.congr (fun r _ => heq r) (heq t)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffWithinAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.fiberwise_time_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.fiberwise_time_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.fiberwise_time_contDiffWithinAt ``Submission.ContMDiffWithinAt.fiberwise_time_contDiffWithinAt

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

open _root_.ContMDiffOn in
theorem ContMDiffOn.time_mfderivWithin {s : Set ℝ} {u : Set M}
    {γ : ℝ → M → N}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I' n (fun p : ℝ × M => γ p.1 p.2) (s ×ˢ u))
    (hs : UniqueDiffOn ℝ s) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I'.prod 𝓘(ℝ, E')) m
      (fun p : ℝ × M => (⟨γ p.1 p.2,
        mfderivWithin 𝓘(ℝ, ℝ) I' (fun t => γ t p.2) s p.1
          ((NormedSpace.fromTangentSpace p.1).symm 1)⟩ : TangentBundle I' N))
      (s ×ˢ u) := by
  intro p₀ hp₀
  have harg : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) n (fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      ((s ×ˢ u) ×ˢ s) (p₀, p₀.1) :=
    contMDiffWithinAt_snd.prodMk contMDiffWithinAt_fst.snd
  have hC : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) I' n
      (fun q : (ℝ × M) × ℝ => γ q.2 q.1.2) ((s ×ˢ u) ×ˢ s) (p₀, p₀.1) :=
    (hγ p₀ hp₀).comp (f := fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      (g := fun p : ℝ × M => γ p.1 p.2) (p₀, p₀.1) harg
      (fun _ hq => ⟨hq.2, hq.1.2⟩)
  have hD := ContMDiffWithinAt.mfderivWithin
    (I := 𝓘(ℝ, ℝ)) (I' := I')
    (f := fun (p : ℝ × M) (t : ℝ) => γ t p.2) (g := fun p : ℝ × M => p.1)
    hC contMDiffWithinAt_fst hp₀ (fun _ hp => hp.1) hmn hs.uniqueMDiffOn
  have hv : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) m
      (fun p : ℝ × M => (⟨p.1, (NormedSpace.fromTangentSpace p.1).symm 1⟩ :
        TangentBundle 𝓘(ℝ, ℝ) ℝ)) (s ×ˢ u) p₀ := by
    rw [_root_.Bundle.contMDiffWithinAt_totalSpace]
    refine ⟨contMDiffWithinAt_fst, ?_⟩
    convert (contMDiffWithinAt_const (c := (1 : ℝ)) :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) m
        (fun _ : ℝ × M => (1 : ℝ)) (s ×ˢ u) p₀) using 1
    funext p
    simp only [TangentBundle.trivializationAt_apply, mfld_simps, chartAt_self_eq,
      fderivWithin_univ, fderiv_id]
    rfl
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates
    (F₁ := ℝ) (E₁ := TangentSpace 𝓘(ℝ, ℝ))
    (F₂ := E') (E₂ := TangentSpace I')
    (b₁ := fun p : ℝ × M => p.1) (b₂ := fun p : ℝ × M => γ p.1 p.2)
    (ϕ := fun p : ℝ × M => mfderivWithin 𝓘(ℝ, ℝ) I' (fun t => γ t p.2) s p.1)
    hD hv ((hγ p₀ hp₀).of_le (le_self_add.trans hmn))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.time_mfderivWithin then
    throwError "Refusing to shadow existing declaration ContMDiffOn.time_mfderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.time_mfderivWithin ``Submission.ContMDiffOn.time_mfderivWithin

open _root_.ContMDiffOn in
theorem ContMDiffOn.mfderivWithin_snd {s u : Set ℝ} {γ : ℝ → ℝ → N}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I' n
      (fun p : ℝ × ℝ => γ p.1 p.2) (s ×ˢ u))
    (hu : UniqueDiffOn ℝ u) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, E')) m
      (fun p : ℝ × ℝ => (⟨γ p.1 p.2,
        mfderivWithin 𝓘(ℝ, ℝ) I' (fun t => γ p.1 t) u p.2
          ((NormedSpace.fromTangentSpace p.2).symm 1)⟩ : TangentBundle I' N))
      (s ×ˢ u) := by
  intro p₀ hp₀
  have harg : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) n (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2))
      ((s ×ˢ u) ×ˢ u) (p₀, p₀.2) :=
    contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd
  have hC : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) I' n
      (fun q : (ℝ × ℝ) × ℝ => γ q.1.1 q.2) ((s ×ˢ u) ×ˢ u) (p₀, p₀.2) :=
    (hγ p₀ hp₀).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2))
      (g := fun p : ℝ × ℝ => γ p.1 p.2) (p₀, p₀.2) harg
      (fun _ hq => ⟨hq.1.1, hq.2⟩)
  have hD := ContMDiffWithinAt.mfderivWithin
    (I := 𝓘(ℝ, ℝ)) (I' := I')
    (f := fun (p : ℝ × ℝ) (t : ℝ) => γ p.1 t) (g := fun p : ℝ × ℝ => p.2)
    hC contMDiffWithinAt_snd hp₀ (fun _ hp => hp.2) hmn hu.uniqueMDiffOn
  have hv : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) m
      (fun p : ℝ × ℝ => (⟨p.2, (NormedSpace.fromTangentSpace p.2).symm 1⟩ :
        TangentBundle 𝓘(ℝ, ℝ) ℝ)) (s ×ˢ u) p₀ := by
    rw [_root_.Bundle.contMDiffWithinAt_totalSpace]
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    convert (contMDiffWithinAt_const (c := (1 : ℝ)) :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) m
        (fun _ : ℝ × ℝ => (1 : ℝ)) (s ×ˢ u) p₀) using 1
    funext p
    simp only [TangentBundle.trivializationAt_apply, mfld_simps, chartAt_self_eq,
      fderivWithin_univ, fderiv_id]
    rfl
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates
    (F₁ := ℝ) (E₁ := TangentSpace 𝓘(ℝ, ℝ))
    (F₂ := E') (E₂ := TangentSpace I')
    (b₁ := fun p : ℝ × ℝ => p.2) (b₂ := fun p : ℝ × ℝ => γ p.1 p.2)
    (ϕ := fun p : ℝ × ℝ => mfderivWithin 𝓘(ℝ, ℝ) I' (fun t => γ p.1 t) u p.2)
    hD hv ((hγ p₀ hp₀).of_le (le_self_add.trans hmn))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.mfderivWithin_snd then
    throwError "Refusing to shadow existing declaration ContMDiffOn.mfderivWithin_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.mfderivWithin_snd ``Submission.ContMDiffOn.mfderivWithin_snd

open _root_.ContMDiffAt in
theorem ContMDiffAt.time_mfderiv {γ : ℝ → N} {t₀ : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I' n γ t₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I'.prod 𝓘(ℝ, E')) m
      (fun t => (⟨γ t, mfderiv 𝓘(ℝ, ℝ) I' γ t
        ((NormedSpace.fromTangentSpace t).symm 1)⟩ : TangentBundle I' N)) t₀ := by
  have hD := hγ.mfderiv_const hmn
  have hv : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) m
      (fun t => (⟨t, (NormedSpace.fromTangentSpace t).symm 1⟩ :
        TangentBundle 𝓘(ℝ, ℝ) ℝ)) t₀ := by
    rw [_root_.Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    convert (contMDiffAt_const (c := (1 : ℝ)) :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) m (fun _ : ℝ => (1 : ℝ)) t₀) using 1
    funext t
    simp only [TangentBundle.trivializationAt_apply, mfld_simps, chartAt_self_eq,
      fderivWithin_univ, fderiv_id]
    rfl
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := ℝ) (E₁ := TangentSpace 𝓘(ℝ, ℝ))
    (F₂ := E') (E₂ := TangentSpace I')
    (b₁ := id) (b₂ := γ) (ϕ := fun t => mfderiv 𝓘(ℝ, ℝ) I' γ t)
    hD hv (hγ.of_le (le_self_add.trans hmn))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.time_mfderiv then
    throwError "Refusing to shadow existing declaration ContMDiffAt.time_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.time_mfderiv ``Submission.ContMDiffAt.time_mfderiv
