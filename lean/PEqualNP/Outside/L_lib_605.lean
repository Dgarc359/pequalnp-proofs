import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_605_kid.held : ∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j)) := by
  intro m r
  dsimp only
  intro label
  have hinj : (∀ x : Fin m → Fin r → Bool, ∃ a : Fin (m+1), ∀ i, x i ≠ label i a) →
      ∀ i, Function.Injective (label i) := by
    intro hc i0
    by_contra hni
    obtain ⟨a1, a2, heq, hne⟩ := Function.not_injective_iff.mp hni
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
    obtain ⟨a, ha⟩ := hc (fun i => label i (a2.succAbove (Equiv.swap i0 k i)))
    by_cases hab : a = a2
    · apply ha i0
      simp only [Equiv.swap_apply_left, hk, heq, hab]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hab
      apply ha (Equiv.swap i0 k z)
      simp only [Equiv.swap_apply_self, hz]
  have hcov : (∀ i, Function.Injective (label i)) →
      ∀ x : Fin m → Fin r → Bool, ∃ a : Fin (m+1), ∀ i, x i ≠ label i a := by
    intro hi x
    by_contra hne
    push_neg at hne
    choose f hf using hne
    have finj : Function.Injective f := by
      intro a a' h
      apply hi (f a)
      rw [← hf a, h]
      exact hf a'
    have hcard := Fintype.card_le_of_injective f finj
    simp only [Fintype.card_fin] at hcard
    omega
  refine ⟨⟨hinj, hcov⟩, ?_⟩
  intro hc b
  have hi := hinj hc
  refine ⟨b.succAbove, Fin.succAbove_right_injective, fun i => Fin.succAbove_ne b i, ?_⟩
  intro flags v
  constructor
  · intro h
    by_cases hvb : v = b
    · left
      refine ⟨hvb, ?_⟩
      intro j
      by_contra hj
      have hj' : flags j = true := by simpa using hj
      apply h j
      rw [if_pos hj', hvb]
    · right
      obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hvb
      refine ⟨z, ?_, hz.symm⟩
      by_contra hz'
      apply h z
      rw [if_neg hz', hz]
  · rintro (⟨hvb, hf⟩ | ⟨j, hj, hv⟩) i heq
    · have h1 := hi i heq
      split_ifs at h1 with hfi
      · rw [hf i] at hfi
        exact absurd hfi (by decide)
      · exact Fin.succAbove_ne b i (h1.trans hvb)
    · have h1 := hi i heq
      subst hv
      split_ifs at h1 with hfi
      · exact Fin.succAbove_ne b j h1.symm
      · have hij := Fin.succAbove_right_injective h1
        subst hij
        exact hfi hj

theorem PEqualNP.Outside.L_lib_605 :
∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j)) :=
  PEqualNP.Outside.L_lib_605_kid.held
