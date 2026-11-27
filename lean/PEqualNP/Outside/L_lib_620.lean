import Mathlib
import PEqualNP.Defs

private theorem L620_step {n : ℕ} (G : Fin n → Fin n → Bool)
    (U V A B : Finset (Fin n)) (f : Fin n → Fin n) (g : Fin n → ℕ) (c : ℕ) (col : Bool)
    (h2 : ∀ x ∈ U, f x ∈ V)
    (h3 : ∀ x ∈ U, ∀ y ∈ U, f x = f y → x = y)
    (h4 : ∀ x ∈ U, g x < c)
    (h5 : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, ∀ w ∈ U, g x = g y → g x = g z → g x = g w →
      G x (f y) = G z (f w))
    (hAU : Disjoint A U) (hBV : Disjoint B V) (hAB : A.card = B.card)
    (hmono : ∀ a ∈ A, ∀ b ∈ B, G a b = col) :
    ∃ (f' : Fin n → Fin n) (g' : Fin n → ℕ),
      (∀ x ∈ U ∪ A, f' x ∈ V ∪ B) ∧
      (∀ x ∈ U ∪ A, ∀ y ∈ U ∪ A, f' x = f' y → x = y) ∧
      (∀ x ∈ U ∪ A, g' x < c + 1) ∧
      (∀ x ∈ U ∪ A, ∀ y ∈ U ∪ A, ∀ z ∈ U ∪ A, ∀ w ∈ U ∪ A,
        g' x = g' y → g' x = g' z → g' x = g' w → G x (f' y) = G z (f' w)) := by
  classical
  have hcard : Fintype.card A = Fintype.card B := by
    rw [Fintype.card_coe, Fintype.card_coe, hAB]
  obtain ⟨e⟩ : Nonempty (A ≃ B) := ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨f', hf1, hf2⟩ : ∃ f' : Fin n → Fin n,
      (∀ x (h : x ∈ A), f' x = (e ⟨x, h⟩ : Fin n)) ∧ (∀ x, x ∉ A → f' x = f x) :=
    ⟨fun x => if h : x ∈ A then (e ⟨x, h⟩ : Fin n) else f x,
      fun x h => dif_pos h, fun x h => dif_neg h⟩
  obtain ⟨g', hg1, hg2⟩ : ∃ g' : Fin n → ℕ,
      (∀ x, x ∈ A → g' x = c) ∧ (∀ x, x ∉ A → g' x = g x) :=
    ⟨fun x => if x ∈ A then c else g x, fun x h => if_pos h, fun x h => if_neg h⟩
  have hfB : ∀ x ∈ A, f' x ∈ B := by
    intro x hx
    rw [hf1 x hx]
    exact (e ⟨x, hx⟩).2
  have hinjA : ∀ x ∈ A, ∀ y ∈ A, f' x = f' y → x = y := by
    intro x hx y hy hxy
    rw [hf1 x hx, hf1 y hy] at hxy
    have := e.injective (Subtype.ext hxy)
    exact congrArg Subtype.val this
  have hUA : ∀ x ∈ U ∪ A, x ∉ A → x ∈ U := by
    intro x hx h
    rcases Finset.mem_union.mp hx with h' | h'
    · exact h'
    · exact absurd h' h
  have hBnV : ∀ b ∈ B, b ∉ V := fun b hb => Finset.disjoint_left.mp hBV hb
  refine ⟨f', g', ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases h : x ∈ A
    · exact Finset.mem_union_right _ (hfB x h)
    · rw [hf2 x h]
      exact Finset.mem_union_left _ (h2 x (hUA x hx h))
  · intro x hx y hy hxy
    by_cases ha : x ∈ A <;> by_cases hb : y ∈ A
    · exact hinjA x ha y hb hxy
    · have hV : f' x ∈ V := by
        rw [hxy, hf2 y hb]
        exact h2 y (hUA y hy hb)
      exact absurd hV (hBnV _ (hfB x ha))
    · have hV : f' y ∈ V := by
        rw [← hxy, hf2 x ha]
        exact h2 x (hUA x hx ha)
      exact absurd hV (hBnV _ (hfB y hb))
    · rw [hf2 x ha, hf2 y hb] at hxy
      exact h3 x (hUA x hx ha) y (hUA y hy hb) hxy
  · intro x hx
    by_cases h : x ∈ A
    · rw [hg1 x h]
      omega
    · rw [hg2 x h]
      have := h4 x (hUA x hx h)
      omega
  · intro x hx y hy z hz w hw hxy hxz hxw
    by_cases ha : x ∈ A
    · rw [hg1 x ha] at hxy hxz hxw
      have hyA : y ∈ A := by
        by_contra hb
        rw [hg2 y hb] at hxy
        have := h4 y (hUA y hy hb)
        omega
      have hwA : w ∈ A := by
        by_contra hb
        rw [hg2 w hb] at hxw
        have := h4 w (hUA w hw hb)
        omega
      have hzA : z ∈ A := by
        by_contra hb
        rw [hg2 z hb] at hxz
        have := h4 z (hUA z hz hb)
        omega
      rw [hmono x ha (f' y) (hfB y hyA), hmono z hzA (f' w) (hfB w hwA)]
    · rw [hg2 x ha] at hxy hxz hxw
      have hgx := h4 x (hUA x hx ha)
      have hyA : y ∉ A := by
        intro hb
        rw [hg1 y hb] at hxy
        omega
      have hzA : z ∉ A := by
        intro hb
        rw [hg1 z hb] at hxz
        omega
      have hwA : w ∉ A := by
        intro hb
        rw [hg1 w hb] at hxw
        omega
      rw [hg2 y hyA] at hxy
      rw [hg2 z hzA] at hxz
      rw [hg2 w hwA] at hxw
      rw [hf2 y hyA, hf2 w hwA]
      exact h5 x (hUA x hx ha) y (hUA y hy hyA) z (hUA z hz hzA) w (hUA w hw hwA) hxy hxz hxw

private theorem L620_block {n : ℕ} (G : Fin n → Fin n → Bool) (m : ℕ) (R S : Finset (Fin n))
    (hR : 2 * m ≤ R.card) (hS : 4 ^ m * m ≤ S.card) :
    ∃ A ⊆ R, ∃ B ⊆ S, A.card = m ∧ B.card = m ∧
      ∃ col : Bool, ∀ a ∈ A, ∀ b ∈ B, G a b = col := by
  classical
  obtain ⟨A0, hA0R, hA0⟩ := Finset.exists_subset_card_eq hR
  have hpow : A0.powerset.card = 4 ^ m := by
    rw [Finset.card_powerset, hA0, pow_mul]
    norm_num
  have hmaps : ∀ c ∈ S, (fun c => A0.filter (fun a => G a c = true)) c ∈ A0.powerset := by
    intro c _
    exact Finset.mem_powerset.mpr (fun x hx => (Finset.mem_filter.mp hx).1)
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps
    ⟨∅, Finset.empty_mem_powerset _⟩ (show A0.powerset.card * m ≤ S.card by rw [hpow]; exact hS)
  rw [Finset.mem_powerset] at hT
  obtain ⟨B, hBB0, hB⟩ := Finset.exists_subset_card_eq hTcard
  have hBS : B ⊆ S := fun x hx => (Finset.mem_filter.mp (hBB0 hx)).1
  have key : ∀ b ∈ B, ∀ a ∈ A0, (G a b = true ↔ a ∈ T) := by
    intro b hb a ha
    have hb' : A0.filter (fun a => G a b = true) = T := (Finset.mem_filter.mp (hBB0 hb)).2
    rw [← hb', Finset.mem_filter]
    simp [ha]
  have hsplit := Finset.card_sdiff_add_card_eq_card hT
  rw [hA0] at hsplit
  by_cases hTm : m ≤ T.card
  · obtain ⟨A, hAT, hA⟩ := Finset.exists_subset_card_eq hTm
    refine ⟨A, fun x hx => hA0R (hT (hAT hx)), B, hBS, hA, hB, true, ?_⟩
    intro a ha b hb
    exact (key b hb a (hT (hAT ha))).mpr (hAT ha)
  · have hm' : m ≤ (A0 \ T).card := by omega
    obtain ⟨A, hAT, hA⟩ := Finset.exists_subset_card_eq hm'
    refine ⟨A, fun x hx => hA0R (Finset.mem_sdiff.mp (hAT hx)).1, B, hBS, hA, hB, false, ?_⟩
    intro a ha b hb
    have haA0 := Finset.mem_sdiff.mp (hAT ha)
    have hk := key b hb a haA0.1
    cases h : G a b
    · rfl
    · exact absurd (hk.mp h) haA0.2

private theorem L620_main {n : ℕ} (G : Fin n → Fin n → Bool) (m : ℕ) (hm : 0 < m)
    (hn : m * (m * 4 ^ m) ≤ n) :
    ∀ r : ℕ, ∀ (U V : Finset (Fin n)) (f : Fin n → Fin n) (g : Fin n → ℕ) (c : ℕ),
      n - U.card = r → U.card = V.card →
      (∀ x ∈ U, f x ∈ V) →
      (∀ x ∈ U, ∀ y ∈ U, f x = f y → x = y) →
      (∀ x ∈ U, g x < c) →
      (∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, ∀ w ∈ U, g x = g y → g x = g z → g x = g w →
        G x (f y) = G z (f w)) →
      (c * m ≤ U.card ∨ c + (n - U.card) ≤ 2 * (n / m)) →
      ∃ (f' : Fin n → Fin n) (g' : Fin n → ℕ),
        Function.Injective f' ∧ (∀ x, g' x < 2 * (n / m)) ∧
        ∀ x y z w, g' x = g' y → g' x = g' z → g' x = g' w → G x (f' y) = G z (f' w) := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro U V f g c hr hUV h2 h3 h4 h5 h6
  have hUn : U.card ≤ n := by
    have := Finset.card_le_univ U
    rw [Fintype.card_fin] at this
    exact this
  have hQ : m * 4 ^ m ≤ n / m := by
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]
    exact hn
  have h44 : 4 ≤ 4 ^ m := by
    calc (4 : ℕ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hm4 : m * 4 ≤ m * 4 ^ m := Nat.mul_le_mul_left m h44
  by_cases hr0 : r = 0
  · have hUu : U = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      omega
    subst hUu
    simp only [Finset.card_univ, Fintype.card_fin] at h6
    have hc : c ≤ 2 * (n / m) := by
      rcases h6 with h | h
      · have : c ≤ n / m := by
          rw [Nat.le_div_iff_mul_le hm]
          exact h
        omega
      · omega
    refine ⟨f, g, ?_, ?_, ?_⟩
    · intro x y hxy
      exact h3 x (Finset.mem_univ _) y (Finset.mem_univ _) hxy
    · intro x
      have := h4 x (Finset.mem_univ _)
      omega
    · intro x y z w
      exact h5 x (Finset.mem_univ _) y (Finset.mem_univ _) z (Finset.mem_univ _) w
        (Finset.mem_univ _)
  · have hRc : (Finset.univ \ U).card = n - U.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hSc : (Finset.univ \ V).card = n - U.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        hUV]
    by_cases hblk : c * m ≤ U.card ∧ m * 4 ^ m ≤ n - U.card
    · obtain ⟨A, hAR, B, hBS, hA, hB, col, hmono⟩ :=
        L620_block G m (Finset.univ \ U) (Finset.univ \ V)
          (by rw [hRc]; omega) (by rw [hSc, Nat.mul_comm]; exact hblk.2)
      have hdA : Disjoint A U :=
        Finset.disjoint_left.mpr fun x hxA hxU => (Finset.mem_sdiff.mp (hAR hxA)).2 hxU
      have hdB : Disjoint B V :=
        Finset.disjoint_left.mpr fun x hxB hxV => (Finset.mem_sdiff.mp (hBS hxB)).2 hxV
      obtain ⟨f', g', h2', h3', h4', h5'⟩ :=
        L620_step G U V A B f g c col h2 h3 h4 h5 hdA hdB (by rw [hA, hB]) hmono
      have hUAc : (U ∪ A).card = U.card + m := by
        rw [Finset.card_union_of_disjoint hdA.symm, hA]
      have hVBc : (V ∪ B).card = V.card + m := by
        rw [Finset.card_union_of_disjoint hdB.symm, hB]
      exact ih (n - (U ∪ A).card) (by rw [hUAc]; omega) (U ∪ A) (V ∪ B) f' g' (c + 1) rfl
        (by rw [hUAc, hVBc, hUV]) h2' h3' h4' h5'
        (Or.inl (by rw [hUAc, Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_right hblk.1 _))
    · obtain ⟨x, hx⟩ : (Finset.univ \ U).Nonempty := Finset.card_pos.mp (by rw [hRc]; omega)
      obtain ⟨y, hy⟩ : (Finset.univ \ V).Nonempty := Finset.card_pos.mp (by rw [hSc]; omega)
      have hdA : Disjoint {x} U :=
        Finset.disjoint_singleton_left.mpr (Finset.mem_sdiff.mp hx).2
      have hdB : Disjoint {y} V :=
        Finset.disjoint_singleton_left.mpr (Finset.mem_sdiff.mp hy).2
      have hmono : ∀ a ∈ ({x} : Finset (Fin n)), ∀ b ∈ ({y} : Finset (Fin n)), G a b = G x y := by
        intro a ha b hb
        rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
      obtain ⟨f', g', h2', h3', h4', h5'⟩ :=
        L620_step G U V {x} {y} f g c (G x y) h2 h3 h4 h5 hdA hdB
          (by rw [Finset.card_singleton, Finset.card_singleton]) hmono
      have hUAc : (U ∪ {x}).card = U.card + 1 := by
        rw [Finset.card_union_of_disjoint hdA.symm, Finset.card_singleton]
      have hVBc : (V ∪ {y}).card = V.card + 1 := by
        rw [Finset.card_union_of_disjoint hdB.symm, Finset.card_singleton]
      have h6' : c + 1 + (n - (U ∪ {x}).card) ≤ 2 * (n / m) := by
        rw [hUAc]
        rcases h6 with h | h
        · have hc : c ≤ n / m := by
            rw [Nat.le_div_iff_mul_le hm]
            exact le_trans h hUn
          have hlt : ¬ (m * 4 ^ m ≤ n - U.card) := fun h' => hblk ⟨h, h'⟩
          omega
        · omega
      exact ih (n - (U ∪ {x}).card) (by rw [hUAc]; omega) (U ∪ {x}) (V ∪ {y}) f' g' (c + 1) rfl
        (by rw [hUAc, hVBc, hUV]) h2' h3' h4' h5' (Or.inr h6')

theorem PEqualNP.Outside.L_lib_620_kid.held : ∀ (n m : ℕ), 0 < m → m^2*4^m ≤ n →
  ∀ G : Fin n → Fin n → Bool,
    ∃ (π : Equiv.Perm (Fin n)) (group : Fin n → Fin (2*(n/m))),
      ∀ (x y z w : Fin n), group x = group y → group x = group z → group x = group w →
        G x (π y) = G z (π w) := by
  intro n m hm hn G
  have hn' : m * (m * 4 ^ m) ≤ n := by
    have : m * (m * 4 ^ m) = m ^ 2 * 4 ^ m := by ring
    rw [this]
    exact hn
  obtain ⟨f, g, hf, hg, hmono⟩ :=
    L620_main G m hm hn' (n - (∅ : Finset (Fin n)).card) ∅ ∅ id (fun _ => 0) 0 rfl
      (by simp) (by simp) (by simp) (by simp) (by simp) (Or.inl (by simp))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun x => ⟨g x, hg x⟩, ?_⟩
  intro x y z w hxy hxz hxw
  simp only [Equiv.ofBijective_apply]
  exact hmono x y z w (congrArg Fin.val hxy) (congrArg Fin.val hxz) (congrArg Fin.val hxw)

theorem PEqualNP.Outside.L_lib_620 :
∀ (n m : ℕ), 0 < m → m^2*4^m ≤ n →
  ∀ G : Fin n → Fin n → Bool,
    ∃ (π : Equiv.Perm (Fin n)) (group : Fin n → Fin (2*(n/m))),
      ∀ (x y z w : Fin n), group x = group y → group x = group z → group x = group w →
        G x (π y) = G z (π w) :=
  PEqualNP.Outside.L_lib_620_kid.held
