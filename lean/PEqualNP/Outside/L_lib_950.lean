import Mathlib
import PEqualNP.Defs

-- entry facts over ZMod 4, by evaluation

private theorem L950_z1 : ∀ a : ZMod 4,
    ((((a.val : ℕ) : ZMod 2).val : ℕ) : ZMod 4) + (((a.val / 2 : ℕ) : ZMod 4) + ((a.val / 2 : ℕ) : ZMod 4)) = a := by
  decide

private theorem L950_z2 : ∀ a : ZMod 4, a + a = 2 * ((((a.val : ℕ) : ZMod 2).val : ℕ) : ZMod 4) := by
  decide

private theorem L950_z3 : ∀ a : ZMod 4, a + a ≠ 0 → a * a = 1 := by
  decide

private theorem L950_z4 : ∀ a : ZMod 4, a + a = 0 → 2 * ((a.val / 2 : ℕ) : ZMod 4) = a := by
  decide

private theorem L950_z5 : ∀ a : ZMod 4, a + a = 0 → a ≠ 0 → ((a.val / 2 : ℕ) : ZMod 4) = 1 := by
  decide

private theorem L950_z6 : ∀ a : ZMod 4, a + a = 0 → ((a.val : ℕ) : ZMod 2) = 0 := by
  decide

private theorem L950_z7 : ∀ t : ZMod 4, t + t = 0 →
    ((t.val / 2 : ℕ) : ZMod 4) + ((t.val / 2 : ℕ) : ZMod 4) = t := by
  decide

private theorem L950_z8 : (Finset.univ.filter (fun t : ZMod 4 => t + t = 0)).card = 2 := by
  decide

private theorem L950_z9 : ∀ a : ZMod 4, 2 * a + 2 * a = 0 := by
  decide

private theorem L950_z10 : ∀ a : ZMod 4, a + a = 0 → a ≠ 0 → a = 2 := by
  decide

private theorem L950_hom (x : ZMod 4) :
    ((x.val : ℕ) : ZMod 2) = ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) x := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem L950_pow_le {a b : ℕ} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b := by
  by_contra hab
  have hlt : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact absurd h (not_le.mpr hlt)

-- reduction mod 2 commutes with products

private theorem L950_redmulVec {a b : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 4)) (x : Fin b → ZMod 4) :
    (fun i => (((A.mulVec x) i).val : ZMod 2)) =
      (Matrix.of (fun i j => ((A i j).val : ZMod 2) : Fin a → Fin b → ZMod 2)).mulVec
        (fun j => ((x j).val : ZMod 2)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [L950_hom, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, L950_hom (A i j), L950_hom (x j)]

private theorem L950_red_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 4))
    (B : Matrix (Fin b) (Fin c) (ZMod 4)) :
    Matrix.of (fun i j => (((A * B) i j).val : ZMod 2) : Fin a → Fin c → ZMod 2) =
    Matrix.of (fun i j => ((A i j).val : ZMod 2) : Fin a → Fin b → ZMod 2) *
      Matrix.of (fun i j => ((B i j).val : ZMod 2) : Fin b → Fin c → ZMod 2) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [L950_hom, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, L950_hom (A i k), L950_hom (B k j)]

-- a finite ZMod 2 image has 2 ^ rank elements

private theorem L950_card_rank {a b : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 2)) :
    (Finset.univ.image (fun x : Fin b → ZMod 2 => A.mulVec x)).card ≤ 2 ^ A.rank := by
  classical
  have h2 : Fintype.card (LinearMap.range A.mulVecLin) = 2 ^ A.rank := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    try rfl
  rw [← h2, ← Fintype.card_coe]
  apply le_of_eq
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun y => by simp [Matrix.mulVecLin_apply])

-- counting in a finite subgroup

private theorem L950_out_add {a b : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 4)) :
    ∀ y ∈ Finset.univ.image (fun x : Fin b → ZMod 4 => A.mulVec x),
    ∀ z ∈ Finset.univ.image (fun x : Fin b → ZMod 4 => A.mulVec x),
    y + z ∈ Finset.univ.image (fun x : Fin b → ZMod 4 => A.mulVec x) := by
  intro y hy z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨x', -, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨x + x', Finset.mem_univ _, Matrix.mulVec_add A x x'⟩

private theorem L950_lemA {k : ℕ} (S : Finset (Fin k → ZMod 4)) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) :
    (S.filter (fun y => ∀ i, y i + y i = 0)).card * (S.image (fun y => y + y)).card ≤ S.card := by
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin k → ZMod 4) → (Fin k → ZMod 4),
      ∀ t ∈ S.image (fun y => y + y), σ t ∈ S ∧ σ t + σ t = t := by
    classical
    refine ⟨fun t => if h : ∃ y ∈ S, y + y = t then h.choose else 0, fun t ht => ?_⟩
    have h : ∃ y ∈ S, y + y = t := Finset.mem_image.mp ht
    simp only [dif_pos h]
    exact h.choose_spec
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun pr => pr.1 + σ pr.2) ?_ ?_
  · rintro ⟨k1, t⟩ hpr
    have hp := Finset.mem_product.mp (Finset.mem_coe.mp hpr)
    have hk : k1 ∈ S.filter (fun y => ∀ i, y i + y i = 0) := hp.1
    have ht : t ∈ S.image (fun y => y + y) := hp.2
    exact Finset.mem_coe.mpr (hS _ (Finset.mem_filter.mp hk).1 _ (hσ t ht).1)
  · rintro ⟨k1, t⟩ hpr ⟨k2, t'⟩ hpr' heq
    have hp := Finset.mem_product.mp (Finset.mem_coe.mp hpr)
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hpr')
    have hk : k1 ∈ S.filter (fun y => ∀ i, y i + y i = 0) := hp.1
    have hk' : k2 ∈ S.filter (fun y => ∀ i, y i + y i = 0) := hp'.1
    have ht : t ∈ S.image (fun y => y + y) := hp.2
    have ht' : t' ∈ S.image (fun y => y + y) := hp'.2
    have heq' : k1 + σ t = k2 + σ t' := heq
    have hk1 : k1 + k1 = 0 := funext (Finset.mem_filter.mp hk).2
    have hk2 : k2 + k2 = 0 := funext (Finset.mem_filter.mp hk').2
    have h1 : (k1 + σ t) + (k1 + σ t) = t := by
      rw [add_add_add_comm, hk1, zero_add]; exact (hσ t ht).2
    have h2 : (k2 + σ t') + (k2 + σ t') = t' := by
      rw [add_add_add_comm, hk2, zero_add]; exact (hσ t' ht').2
    have e2 : t = t' := by
      calc t = (k1 + σ t) + (k1 + σ t) := h1.symm
        _ = (k2 + σ t') + (k2 + σ t') := by rw [heq']
        _ = t' := h2
    have e1 : k1 = k2 := by
      rw [e2] at heq'
      exact add_right_cancel heq'
    rw [e1, e2]

private theorem L950_lemC {n w : ℕ} (A : Matrix (Fin n) (Fin w) (ZMod 4)) :
    (Finset.univ.image (fun x : Fin w → ZMod 4 => A.mulVec x)).card ≤
      2 ^ w * ((Finset.univ.image (fun x : Fin w → ZMod 4 => A.mulVec x)).image (fun y => y + y)).card := by
  have hsub : Finset.univ.image (fun x : Fin w → ZMod 4 => A.mulVec x) ⊆
      ((Finset.univ : Finset (Fin w → ZMod 2)) ×ˢ
        ((Finset.univ.image (fun x : Fin w → ZMod 4 => A.mulVec x)).image (fun y => y + y))).image
        (fun pr => A.mulVec (fun i => (((pr.1 i).val : ℕ) : ZMod 4)) + pr.2) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨((fun i => (((x i).val : ℕ) : ZMod 2)),
      A.mulVec (fun i => (((x i).val / 2 : ℕ) : ZMod 4)) + A.mulVec (fun i => (((x i).val / 2 : ℕ) : ZMod 4))),
      ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_image.mpr ⟨A.mulVec (fun i => (((x i).val / 2 : ℕ) : ZMod 4)),
          Finset.mem_image_of_mem _ (Finset.mem_univ _), rfl⟩⟩
    · show A.mulVec (fun i => (((((x i).val : ℕ) : ZMod 2).val : ℕ) : ZMod 4)) +
          (A.mulVec (fun i => (((x i).val / 2 : ℕ) : ZMod 4)) + A.mulVec (fun i => (((x i).val / 2 : ℕ) : ZMod 4))) =
          A.mulVec x
      rw [← Matrix.mulVec_add, ← Matrix.mulVec_add]
      congr 1
      funext i
      exact L950_z1 (x i)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, Finset.card_univ]; simp

private theorem L950_lemD {n m : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4)) :
    ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).image (fun y => y + y)).card ≤
      2 ^ Matrix.rank (fun i j => ((G i j).val : ZMod 2) : Matrix (Fin n) (Fin m) (ZMod 2)) := by
  refine le_trans ?_ (L950_card_rank (Matrix.of (fun i j => ((G i j).val : ZMod 2) : Fin n → Fin m → ZMod 2)))
  calc _ ≤ ((Finset.univ.image (fun x : Fin m → ZMod 2 =>
          (Matrix.of (fun i j => ((G i j).val : ZMod 2) : Fin n → Fin m → ZMod 2)).mulVec x)).image
          (fun c => fun i => 2 * (((c i).val : ℕ) : ZMod 4))).card := by
        apply Finset.card_le_card
        intro t ht
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
        refine Finset.mem_image.mpr ⟨fun i => (((G.mulVec x) i).val : ZMod 2),
          Finset.mem_image.mpr ⟨fun j => ((x j).val : ZMod 2), Finset.mem_univ _, (L950_redmulVec G x).symm⟩, ?_⟩
        funext i
        exact (L950_z2 _).symm
    _ ≤ _ := Finset.card_image_le

-- forward direction

private theorem L950_decomp {n w : ℕ} (U : Matrix (Fin n) (Fin w) (ZMod 4)) (v : Fin w → ZMod 4) :
    U.mulVec (fun i => (((((v i).val : ℕ) : ZMod 2).val : ℕ) : ZMod 4)) +
      (fun i => 2 * ((((((U.mulVec (fun k => (((v k).val / 2 : ℕ) : ZMod 4))) i).val : ℕ) : ZMod 2).val : ℕ)
        : ZMod 4)) = U.mulVec v := by
  calc _ = U.mulVec (fun i => (((((v i).val : ℕ) : ZMod 2).val : ℕ) : ZMod 4)) +
        (U.mulVec (fun k => (((v k).val / 2 : ℕ) : ZMod 4)) + U.mulVec (fun k => (((v k).val / 2 : ℕ) : ZMod 4))) := by
          congr 1
          funext i
          exact (L950_z2 _).symm
    _ = U.mulVec v := by
          rw [← Matrix.mulVec_add, ← Matrix.mulVec_add]
          congr 1
          funext k
          exact L950_z1 (v k)

private theorem L950_out_le {n w m : ℕ} (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)) :
    (Finset.univ.image (fun x : Fin m → ZMod 4 => (U * V).mulVec x)).card ≤
      2 ^ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) *
      2 ^ Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) := by
  have hsub : Finset.univ.image (fun x : Fin m → ZMod 4 => (U * V).mulVec x) ⊆
      ((Finset.univ.image (fun x : Fin w → ZMod 2 =>
          (Matrix.of (fun i j => ((U i j).val : ZMod 2) : Fin n → Fin w → ZMod 2)).mulVec x)) ×ˢ
        (Finset.univ.image (fun x : Fin m → ZMod 2 =>
          (Matrix.of (fun i j => ((V i j).val : ZMod 2) : Fin w → Fin m → ZMod 2)).mulVec x))).image
        (fun pr => U.mulVec (fun i => (((pr.2 i).val : ℕ) : ZMod 4)) +
          (fun i => 2 * (((pr.1 i).val : ℕ) : ZMod 4))) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨((fun i => (((U.mulVec (fun k => ((((V.mulVec x) k).val / 2 : ℕ) : ZMod 4))) i).val
        : ZMod 2)), (fun i => (((V.mulVec x) i).val : ZMod 2))), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (L950_redmulVec U _).symm⟩
      · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (L950_redmulVec V x).symm⟩
    · exact (L950_decomp U (V.mulVec x)).trans (Matrix.mulVec_mulVec x U V)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul (L950_card_rank (Matrix.of (fun i j => ((U i j).val : ZMod 2) : Fin n → Fin w → ZMod 2)))
        (L950_card_rank (Matrix.of (fun i j => ((V i j).val : ZMod 2) : Fin w → Fin m → ZMod 2)))

private theorem L950_kil_le {n w m : ℕ} (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)) :
    ((Finset.univ.image (fun x : Fin m → ZMod 4 => (U * V).mulVec x)).filter
      (fun y => ∀ i, y i + y i = 0)).card ≤ 2 ^ w := by
  have hA := L950_lemA _ (L950_out_add U)
  have hC := L950_lemC U
  have hpos : 0 < ((Finset.univ.image (fun x : Fin w → ZMod 4 => U.mulVec x)).image (fun y => y + y)).card :=
    Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ 0))⟩
  have hsub : (Finset.univ.image (fun x : Fin m → ZMod 4 => (U * V).mulVec x)).filter
      (fun y => ∀ i, y i + y i = 0) ⊆
      (Finset.univ.image (fun x : Fin w → ZMod 4 => U.mulVec x)).filter (fun y => ∀ i, y i + y i = 0) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨?_, hy.2⟩
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hy.1
    exact Finset.mem_image.mpr ⟨V.mulVec x, Finset.mem_univ _, (Matrix.mulVec_mulVec x U V).trans hx⟩
  have h2 : ((Finset.univ.image (fun x : Fin w → ZMod 4 => U.mulVec x)).filter
      (fun y => ∀ i, y i + y i = 0)).card ≤ 2 ^ w := by
    have h3 := hA.trans hC
    first
      | exact Nat.le_of_mul_le_mul_right h3 hpos
      | nlinarith
  exact (Finset.card_le_card hsub).trans h2

-- rank bookkeeping for appending one column and one row

private theorem L950_rank_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem L950_rank_cons {k m : ℕ} (b : Fin m → ZMod 4) (V' : Fin k → Fin m → ZMod 4) :
    Matrix.rank (fun i j => (((Matrix.of (Matrix.vecCons b V')) i j).val : ZMod 2) :
        Matrix (Fin (k + 1)) (Fin m) (ZMod 2)) ≤
      Matrix.rank (fun i j => ((V' i j).val : ZMod 2) : Matrix (Fin k) (Fin m) (ZMod 2)) + 1 ∧
    ((∀ j, b j + b j = 0) →
      Matrix.rank (fun i j => (((Matrix.of (Matrix.vecCons b V')) i j).val : ZMod 2) :
        Matrix (Fin (k + 1)) (Fin m) (ZMod 2)) ≤
      Matrix.rank (fun i j => ((V' i j).val : ZMod 2) : Matrix (Fin k) (Fin m) (ZMod 2))) := by
  have hM : Matrix.rank (Matrix.of (Matrix.vecCons (0 : Fin k → ZMod 2)
        (fun i' x => if i' = x then (1 : ZMod 2) else 0)) *
      Matrix.of (fun i j => ((V' i j).val : ZMod 2) : Fin k → Fin m → ZMod 2)) ≤
      Matrix.rank (fun i j => ((V' i j).val : ZMod 2) : Matrix (Fin k) (Fin m) (ZMod 2)) :=
    Matrix.rank_mul_le_right _ _
  have hentry : ∀ (i' : Fin k) (j : Fin m), (Matrix.of (Matrix.vecCons (0 : Fin k → ZMod 2)
        (fun i' x => if i' = x then (1 : ZMod 2) else 0)) *
      Matrix.of (fun i j => ((V' i j).val : ZMod 2) : Fin k → Fin m → ZMod 2)) i'.succ j =
        ((V' i' j).val : ZMod 2) := by
    intro i' j
    rw [Matrix.mul_apply]
    simp
  have hentry0 : ∀ j : Fin m, (Matrix.of (Matrix.vecCons (0 : Fin k → ZMod 2)
        (fun i' x => if i' = x then (1 : ZMod 2) else 0)) *
      Matrix.of (fun i j => ((V' i j).val : ZMod 2) : Fin k → Fin m → ZMod 2)) 0 j = 0 := by
    intro j
    rw [Matrix.mul_apply]
    simp
  constructor
  · have hE : Matrix.of (fun i j => (((Matrix.of (Matrix.vecCons b V')) i j).val : ZMod 2) :
          Fin (k + 1) → Fin m → ZMod 2) =
        Matrix.vecMulVec (Matrix.vecCons (1 : ZMod 2) 0) (fun j => ((b j).val : ZMod 2)) +
        Matrix.of (Matrix.vecCons (0 : Fin k → ZMod 2) (fun i' x => if i' = x then (1 : ZMod 2) else 0)) *
          Matrix.of (fun i j => ((V' i j).val : ZMod 2) : Fin k → Fin m → ZMod 2) := by
      ext i j
      rw [Matrix.add_apply, Matrix.vecMulVec_apply]
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [hentry0 j]
        simp
      · rw [hentry i' j]
        simp
    refine (le_of_eq (congrArg Matrix.rank hE)).trans ((L950_rank_add _ _).trans ?_)
    have h1 := Matrix.rank_vecMulVec_le (Matrix.vecCons (1 : ZMod 2) (0 : Fin k → ZMod 2)) (fun j => ((b j).val : ZMod 2))
    exact (Nat.add_le_add h1 hM).trans (le_of_eq (Nat.add_comm _ _))
  · intro hb
    have hE0 : Matrix.of (fun i j => (((Matrix.of (Matrix.vecCons b V')) i j).val : ZMod 2) :
          Fin (k + 1) → Fin m → ZMod 2) =
        Matrix.of (Matrix.vecCons (0 : Fin k → ZMod 2) (fun i' x => if i' = x then (1 : ZMod 2) else 0)) *
          Matrix.of (fun i j => ((V' i j).val : ZMod 2) : Fin k → Fin m → ZMod 2) := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [hentry0 j]
        simp only [Matrix.of_apply, Matrix.cons_val_zero]
        first
          | exact L950_z6 (b j) (hb j)
          | simp [L950_z6 (b j) (hb j)]
      · rw [hentry i' j]
        simp
    exact (le_of_eq (congrArg Matrix.rank hE0)).trans hM

private theorem L950_append {n m k : ℕ} (U' : Matrix (Fin n) (Fin k) (ZMod 4)) (V' : Matrix (Fin k) (Fin m) (ZMod 4))
    (a : Fin n → ZMod 4) (b : Fin m → ZMod 4) :
    ∃ (U : Matrix (Fin n) (Fin (k + 1)) (ZMod 4)) (V : Matrix (Fin (k + 1)) (Fin m) (ZMod 4)),
      U * V = Matrix.vecMulVec a b + U' * V' ∧
      Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin (k + 1)) (ZMod 2)) ≤
        Matrix.rank (fun i j => ((U' i j).val : ZMod 2) : Matrix (Fin n) (Fin k) (ZMod 2)) + 1 ∧
      Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin (k + 1)) (Fin m) (ZMod 2)) ≤
        Matrix.rank (fun i j => ((V' i j).val : ZMod 2) : Matrix (Fin k) (Fin m) (ZMod 2)) + 1 ∧
      ((∀ i, a i + a i = 0) →
        Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin (k + 1)) (ZMod 2)) ≤
        Matrix.rank (fun i j => ((U' i j).val : ZMod 2) : Matrix (Fin n) (Fin k) (ZMod 2))) ∧
      ((∀ j, b j + b j = 0) →
        Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin (k + 1)) (Fin m) (ZMod 2)) ≤
        Matrix.rank (fun i j => ((V' i j).val : ZMod 2) : Matrix (Fin k) (Fin m) (ZMod 2))) := by
  have h1 : Matrix.rank (fun i j => ((((Matrix.of (Matrix.vecCons a (fun i' i => U' i i'))).transpose) i j).val
        : ZMod 2) : Matrix (Fin n) (Fin (k + 1)) (ZMod 2)) =
      Matrix.rank (fun i j => (((Matrix.of (Matrix.vecCons a (fun i' i => U' i i'))) i j).val : ZMod 2) :
        Matrix (Fin (k + 1)) (Fin n) (ZMod 2)) :=
    Matrix.rank_transpose (fun i j => (((Matrix.of (Matrix.vecCons a (fun i' i => U' i i'))) i j).val : ZMod 2) :
        Matrix (Fin (k + 1)) (Fin n) (ZMod 2))
  have h3 : Matrix.rank (fun i j => ((U' j i).val : ZMod 2) : Matrix (Fin k) (Fin n) (ZMod 2)) =
      Matrix.rank (fun i j => ((U' i j).val : ZMod 2) : Matrix (Fin n) (Fin k) (ZMod 2)) :=
    Matrix.rank_transpose (fun i j => ((U' i j).val : ZMod 2) : Matrix (Fin n) (Fin k) (ZMod 2))
  refine ⟨(Matrix.of (Matrix.vecCons a (fun i' i => U' i i'))).transpose,
    Matrix.of (Matrix.vecCons b (fun i' j => V' i' j)), ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    first
      | (rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply]
         simp)
      | (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply]; done)
  · exact (le_of_eq h1).trans (((L950_rank_cons a (fun i' i => U' i i')).1).trans
      (Nat.add_le_add_right (le_of_eq h3) 1))
  · exact (L950_rank_cons b (fun i' j => V' i' j)).1
  · intro ha
    exact (le_of_eq h1).trans (((L950_rank_cons a (fun i' i => U' i i')).2 ha).trans (le_of_eq h3))
  · exact (L950_rank_cons b (fun i' j => V' i' j)).2

-- small facts about images

private theorem L950_D_pos {n m : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4)) :
    0 < ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).image (fun y => y + y)).card :=
  Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ 0))⟩

private theorem L950_kil_pos {n m : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4)) :
    0 < ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).filter (fun y => ∀ i, y i + y i = 0)).card := by
  apply Finset.card_pos.mpr
  refine ⟨G.mulVec 0, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ 0), fun i => ?_⟩⟩
  simp

private theorem L950_D_even {n m : ℕ} (H : Matrix (Fin n) (Fin m) (ZMod 4)) (hHev : ∀ i j, H i j + H i j = 0) :
    ((Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).image (fun y => y + y)).card ≤ 1 := by
  have hHH : H + H = 0 := by
    ext i j
    exact hHev i j
  have h0 : ∀ z ∈ ((Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).image (fun y => y + y)), z = 0 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    show H.mulVec x + H.mulVec x = 0
    rw [← Matrix.add_mulVec, hHH, Matrix.zero_mulVec]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [h0 a ha, h0 b hb]

private theorem L950_kil_double {n m : ℕ} (G H : Matrix (Fin n) (Fin m) (ZMod 4)) (u : Fin n → ZMod 4) (i0 : Fin n)
    (hu : u i0 = 1) (hrow : ∀ j, H i0 j = 0)
    (hsurj : ∀ t : ZMod 4, t + t = 0 → ∀ x' : Fin m → ZMod 4, ∃ x, G.mulVec x = (fun i => t * u i) + H.mulVec x') :
    2 * ((Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).filter (fun y => ∀ i, y i + y i = 0)).card ≤
      ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).filter (fun y => ∀ i, y i + y i = 0)).card := by
  have hH0 : ∀ x : Fin m → ZMod 4, (H.mulVec x) i0 = 0 := by
    intro x
    simp [Matrix.mulVec, dotProduct, hrow]
  rw [← L950_z8, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun pr => (fun i => pr.1 * u i) + pr.2) ?_ ?_
  · rintro ⟨t, y⟩ hpr
    have hp := Finset.mem_product.mp (Finset.mem_coe.mp hpr)
    have ht : t ∈ Finset.univ.filter (fun t : ZMod 4 => t + t = 0) := hp.1
    have hy : y ∈ (Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0) := hp.2
    have ht' : t + t = 0 := (Finset.mem_filter.mp ht).2
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨x', -, hx'⟩ := Finset.mem_image.mp hy1
    obtain ⟨x, hx⟩ := hsurj t ht' x'
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩, ?_⟩
    · show G.mulVec x = (fun i => t * u i) + y
      rw [hx, ← hx']
    · intro i
      show (t * u i + y i) + (t * u i + y i) = 0
      have := hy2 i
      linear_combination (u i) * ht' + this
  · rintro ⟨t, y⟩ hpr ⟨t', y'⟩ hpr' heq
    have hp := Finset.mem_product.mp (Finset.mem_coe.mp hpr)
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hpr')
    have hy : y ∈ (Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0) := hp.2
    have hy' : y' ∈ (Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0) := hp'.2
    have hy0 : y i0 = 0 := by
      obtain ⟨x', -, hx'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
      rw [← hx']
      exact hH0 x'
    have hy0' : y' i0 = 0 := by
      obtain ⟨x', -, hx'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy').1
      rw [← hx']
      exact hH0 x'
    have heq' : (fun i => t * u i) + y = (fun i => t' * u i) + y' := heq
    have e1 : t = t' := by
      have h := congrFun heq' i0
      simp only [Pi.add_apply, hu, mul_one, hy0, hy0', add_zero] at h
      exact h
    have e2 : y = y' := by
      rw [e1] at heq'
      exact add_left_cancel heq'
    rw [e1, e2]

private theorem L950_D_double {n m : ℕ} (G H : Matrix (Fin n) (Fin m) (ZMod 4)) (u : Fin n → ZMod 4) (i0 : Fin n)
    (hu : u i0 = 1) (hrow : ∀ j, H i0 j = 0)
    (hsurj : ∀ t : ZMod 4, ∀ x' : Fin m → ZMod 4, ∃ x, G.mulVec x = (fun i => t * u i) + H.mulVec x') :
    2 * ((Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).image (fun y => y + y)).card ≤
      ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).image (fun y => y + y)).card := by
  have hH0 : ∀ x : Fin m → ZMod 4, (H.mulVec x) i0 = 0 := by
    intro x
    simp [Matrix.mulVec, dotProduct, hrow]
  have hz0 : ∀ z ∈ (Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).image (fun y => y + y), z i0 = 0 := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
    obtain ⟨x', -, hx'⟩ := Finset.mem_image.mp hy
    rw [← hyz, ← hx']
    show (H.mulVec x') i0 + (H.mulVec x') i0 = 0
    rw [hH0 x', add_zero]
  rw [← L950_z8, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun pr => (fun i => pr.1 * u i) + pr.2) ?_ ?_
  · rintro ⟨t, z⟩ hpr
    have hp := Finset.mem_product.mp (Finset.mem_coe.mp hpr)
    have ht : t ∈ Finset.univ.filter (fun t : ZMod 4 => t + t = 0) := hp.1
    have hz : z ∈ (Finset.univ.image (fun x : Fin m → ZMod 4 => H.mulVec x)).image (fun y => y + y) := hp.2
    have ht' : t + t = 0 := (Finset.mem_filter.mp ht).2
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
    obtain ⟨x', -, hx'⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx⟩ := hsurj (((t.val / 2 : ℕ) : ZMod 4)) x'
    apply Finset.mem_coe.mpr
    refine Finset.mem_image.mpr ⟨G.mulVec x, Finset.mem_image_of_mem _ (Finset.mem_univ x), ?_⟩
    show G.mulVec x + G.mulVec x = (fun i => t * u i) + z
    rw [hx, ← hyz, ← hx']
    funext i
    simp only [Pi.add_apply]
    linear_combination (u i) * (L950_z7 t ht')
  · rintro ⟨t, z⟩ hpr ⟨t', z'⟩ hpr' heq
    have hp := Finset.mem_product.mp (Finset.mem_coe.mp hpr)
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hpr')
    have hz0a : z i0 = 0 := hz0 z hp.2
    have hz0b : z' i0 = 0 := hz0 z' hp'.2
    have heq' : (fun i => t * u i) + z = (fun i => t' * u i) + z' := heq
    have e1 : t = t' := by
      have h := congrFun heq' i0
      simp only [Pi.add_apply, hu, mul_one, hz0a, hz0b, add_zero] at h
      exact h
    have e2 : z = z' := by
      rw [e1] at heq'
      exact add_left_cancel heq'
    rw [e1, e2]

private theorem L950_vmv {n m : ℕ} (u : Fin n → ZMod 4) (v y : Fin m → ZMod 4) :
    (Matrix.vecMulVec u v).mulVec y = fun i => (dotProduct v y) * u i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

private theorem L950_surj {n m : ℕ} (G H : Matrix (Fin n) (Fin m) (ZMod 4)) (u : Fin n → ZMod 4)
    (v : Fin m → ZMod 4) (j0 : Fin m) (hG : G = Matrix.vecMulVec u v + H) (hcol : ∀ i, H i j0 = 0)
    (x' : Fin m → ZMod 4) (α : ZMod 4) :
    G.mulVec (x' + Pi.single j0 α) = (fun i => (dotProduct v x' + v j0 * α) * u i) + H.mulVec x' := by
  have hs : H.mulVec (Pi.single j0 α) = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol]
  rw [hG, Matrix.add_mulVec, Matrix.mulVec_add H, hs, add_zero, L950_vmv, dotProduct_add, dotProduct_single]

private theorem L950_surj' {n m : ℕ} (G H : Matrix (Fin n) (Fin m) (ZMod 4)) (u : Fin n → ZMod 4)
    (v : Fin m → ZMod 4) (j0 : Fin m) (hG : G = Matrix.vecMulVec u v + H) (hcol : ∀ i, H i j0 = 0)
    (t : ZMod 4) (x' : Fin m → ZMod 4) (hα : ∃ α, dotProduct v x' + v j0 * α = t) :
    ∃ x, G.mulVec x = (fun i => t * u i) + H.mulVec x' := by
  obtain ⟨α, hα⟩ := hα
  exact ⟨x' + Pi.single j0 α, by rw [L950_surj G H u v j0 hG hcol x' α, hα]⟩

-- rank of reduced products and of zero

private theorem L950_rank_red_mul {n w m : ℕ} (A : Matrix (Fin n) (Fin w) (ZMod 4))
    (B : Matrix (Fin w) (Fin m) (ZMod 4)) :
    Matrix.rank (fun i j => (((A * B) i j).val : ZMod 2) : Matrix (Fin n) (Fin m) (ZMod 2)) ≤
      Matrix.rank (fun i j => ((A i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ∧
    Matrix.rank (fun i j => (((A * B) i j).val : ZMod 2) : Matrix (Fin n) (Fin m) (ZMod 2)) ≤
      Matrix.rank (fun i j => ((B i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) := by
  have e := congrArg Matrix.rank (L950_red_mul A B)
  exact ⟨(le_of_eq e).trans (Matrix.rank_mul_le_left _ _), (le_of_eq e).trans (Matrix.rank_mul_le_right _ _)⟩

private theorem L950_rank_red_zero (a b : ℕ) :
    Matrix.rank (fun i j => (((0 : Matrix (Fin a) (Fin b) (ZMod 4)) i j).val : ZMod 2) :
      Matrix (Fin a) (Fin b) (ZMod 2)) ≤ 0 := by
  have e : Matrix.of (fun i j => (((0 : Matrix (Fin a) (Fin b) (ZMod 4)) i j).val : ZMod 2) :
      Fin a → Fin b → ZMod 2) = 0 := by
    ext i j
    simp
  exact le_of_eq ((congrArg Matrix.rank e).trans Matrix.rank_zero)

-- the structure invariant, by pivoting one row at a time

private theorem L950_base {n m : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4)) (h : ∀ i j, G i j = 0) :
    (∃ r s : ℕ, 2 ^ r ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).image (fun y => y + y)).card ∧
      2 ^ (r + s) ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0)).card ∧
      ∀ w p q : ℕ, r ≤ p → r ≤ q → 2 * r + s ≤ p + q → r + s ≤ w →
        ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
          U * V = G ∧ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ≤ p ∧
          Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) ≤ q) := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · rw [Nat.pow_zero]
    first
      | exact L950_D_pos G
      | exact Nat.succ_le_of_lt (L950_D_pos G)
  · rw [Nat.add_zero, Nat.pow_zero]
    first
      | exact L950_kil_pos G
      | exact Nat.succ_le_of_lt (L950_kil_pos G)
  · intro w p q _ _ _ _
    refine ⟨0, 0, ?_, (L950_rank_red_zero n w).trans (Nat.zero_le p),
      (L950_rank_red_zero w m).trans (Nat.zero_le q)⟩
    ext i j
    simp [h i j]

private theorem L950_odd_step {n m : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4)) (i0 : Fin n) (j0 : Fin m)
    (hc : G i0 j0 * G i0 j0 = 1)
    (hH : (∃ r s : ℕ, 2 ^ r ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => ((G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0))).mulVec x)).image (fun y => y + y)).card ∧
      2 ^ (r + s) ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => ((G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0))).mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0)).card ∧
      ∀ w p q : ℕ, r ≤ p → r ≤ q → 2 * r + s ≤ p + q → r + s ≤ w →
        ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
          U * V = (G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0)) ∧ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ≤ p ∧
          Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) ≤ q)) : (∃ r s : ℕ, 2 ^ r ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).image (fun y => y + y)).card ∧
      2 ^ (r + s) ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0)).card ∧
      ∀ w p q : ℕ, r ≤ p → r ≤ q → 2 * r + s ≤ p + q → r + s ≤ w →
        ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
          U * V = G ∧ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ≤ p ∧
          Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) ≤ q) := by
  obtain ⟨r, s, hD, hK, hf⟩ := hH
  have hG : G = Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0) +
      (G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0)) := by
    first
      | exact (add_sub_cancel _ _).symm
      | abel
      | (ext i j; simp)
  have hcol : ∀ i, (G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0)) i j0 = 0 := by
    intro i
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
    linear_combination (-(G i j0)) * hc
  have hrow : ∀ j, (G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0)) i0 j = 0 := by
    intro j
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
    linear_combination (-(G i0 j)) * hc
  have hD2 := L950_D_double G (G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0))
    (fun i => G i j0 * G i0 j0) i0 hc hrow
    (fun t x' => L950_surj' G _ _ (G i0) j0 hG hcol t x'
      ⟨G i0 j0 * (t - dotProduct (G i0) x'), by linear_combination (t - dotProduct (G i0) x') * hc⟩)
  have hK2 := L950_kil_double G (G - Matrix.vecMulVec (fun i => G i j0 * G i0 j0) (G i0))
    (fun i => G i j0 * G i0 j0) i0 hc hrow
    (fun t _ x' => L950_surj' G _ _ (G i0) j0 hG hcol t x'
      ⟨G i0 j0 * (t - dotProduct (G i0) x'), by linear_combination (t - dotProduct (G i0) x') * hc⟩)
  refine ⟨r + 1, s, ?_, ?_, ?_⟩
  · have e : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [e]
    exact (Nat.mul_le_mul (le_refl 2) hD).trans hD2
  · have e : 2 ^ (r + 1 + s) = 2 * 2 ^ (r + s) := by ring
    rw [e]
    exact (Nat.mul_le_mul (le_refl 2) hK).trans hK2
  · intro w p q hp hq hpq hw
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    obtain ⟨U', V', hUV, hU, hV⟩ := hf w' p' q' (by omega) (by omega) (by omega) (by omega)
    obtain ⟨U, V, hUV2, hU2, hV2, -, -⟩ := L950_append U' V' (fun i => G i j0 * G i0 j0) (G i0)
    refine ⟨U, V, ?_, hU2.trans (Nat.add_le_add_right hU 1), hV2.trans (Nat.add_le_add_right hV 1)⟩
    rw [hUV2, hUV]
    exact hG.symm

private theorem L950_even_step {n m : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4)) (i0 : Fin n) (j0 : Fin m)
    (hev : ∀ i j, G i j + G i j = 0) (h2 : G i0 j0 = 2)
    (hH : (∃ r s : ℕ, 2 ^ r ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => ((G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0))).mulVec x)).image (fun y => y + y)).card ∧
      2 ^ (r + s) ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => ((G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0))).mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0)).card ∧
      ∀ w p q : ℕ, r ≤ p → r ≤ q → 2 * r + s ≤ p + q → r + s ≤ w →
        ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
          U * V = (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) ∧ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ≤ p ∧
          Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) ≤ q)) : (∃ r s : ℕ, 2 ^ r ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).image (fun y => y + y)).card ∧
      2 ^ (r + s) ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0)).card ∧
      ∀ w p q : ℕ, r ≤ p → r ≤ q → 2 * r + s ≤ p + q → r + s ≤ w →
        ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
          U * V = G ∧ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ≤ p ∧
          Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) ≤ q) := by
  obtain ⟨r, s, hD, hK, hf⟩ := hH
  have hu0 : (((G i0 j0).val / 2 : ℕ) : ZMod 4) = 1 :=
    L950_z5 (G i0 j0) (hev i0 j0) (by rw [h2]; decide)
  have hG : G = Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0) +
      (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) := by
    first
      | exact (add_sub_cancel _ _).symm
      | abel
      | (ext i j; simp)
  have hcol : ∀ i, (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) i j0 = 0 := by
    intro i
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
    rw [h2]
    linear_combination -(L950_z4 (G i j0) (hev i j0))
  have hrow : ∀ j, (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) i0 j = 0 := by
    intro j
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
    linear_combination (-(G i0 j)) * hu0
  have hHev : ∀ i j, (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) i j +
      (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) i j = 0 := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
    linear_combination hev i j - (((G i j0).val / 2 : ℕ) : ZMod 4) * hev i0 j
  have hr : r = 0 := by
    have h1 : 2 ^ r ≤ 2 ^ 0 := by
      rw [Nat.pow_zero]
      exact hD.trans (L950_D_even (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)) hHev)
    have := L950_pow_le h1
    omega
  subst hr
  have hd : ∀ x' : Fin m → ZMod 4, dotProduct (G i0) x' + dotProduct (G i0) x' = 0 := by
    intro x'
    rw [← add_dotProduct]
    have e : G i0 + G i0 = 0 := funext (hev i0)
    rw [e, zero_dotProduct]
  have hK2 := L950_kil_double G (G - Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0))
    (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) i0 hu0 hrow
    (fun t ht x' => L950_surj' G _ _ (G i0) j0 hG hcol t x'
      ⟨(((t - dotProduct (G i0) x').val / 2 : ℕ) : ZMod 4), by
        have h3 : (t - dotProduct (G i0) x') + (t - dotProduct (G i0) x') = 0 := by
          linear_combination ht - hd x'
        have h4 := L950_z4 (t - dotProduct (G i0) x') h3
        rw [h2]
        linear_combination h4⟩)
  refine ⟨0, s + 1, ?_, ?_, ?_⟩
  · rw [Nat.pow_zero]
    first
      | exact L950_D_pos G
      | exact Nat.succ_le_of_lt (L950_D_pos G)
  · have e : 2 ^ (0 + (s + 1)) = 2 * 2 ^ (0 + s) := by ring
    rw [e]
    exact (Nat.mul_le_mul (le_refl 2) hK).trans hK2
  · intro w p q _ _ hpq hw
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      obtain ⟨U', V', hUV, hU, hV⟩ := hf w' 0 q' (by omega) (by omega) (by omega) (by omega)
      obtain ⟨U, V, hUV2, -, hV2, hU3, -⟩ := L950_append U' V'
        (fun i => 2 * (((G i j0).val / 2 : ℕ) : ZMod 4)) (fun j => (((G i0 j).val / 2 : ℕ) : ZMod 4))
      refine ⟨U, V, ?_, (hU3 (fun i => L950_z9 _)).trans hU, hV2.trans (Nat.add_le_add_right hV 1)⟩
      have e : Matrix.vecMulVec (fun i => 2 * (((G i j0).val / 2 : ℕ) : ZMod 4))
          (fun j => (((G i0 j).val / 2 : ℕ) : ZMod 4)) =
          Matrix.vecMulVec (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0) := by
        ext i j
        simp only [Matrix.vecMulVec_apply]
        linear_combination (((G i j0).val / 2 : ℕ) : ZMod 4) * L950_z4 (G i0 j) (hev i0 j)
      rw [hUV2, hUV, e]
      exact hG.symm
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      obtain ⟨U', V', hUV, hU, hV⟩ := hf w' p' q (by omega) (by omega) (by omega) (by omega)
      obtain ⟨U, V, hUV2, hU2, -, -, hV3⟩ := L950_append U' V'
        (fun i => (((G i j0).val / 2 : ℕ) : ZMod 4)) (G i0)
      refine ⟨U, V, ?_, hU2.trans (Nat.add_le_add_right hU 1), (hV3 (hev i0)).trans hV⟩
      rw [hUV2, hUV]
      exact hG.symm

private theorem L950_struct {n m : ℕ} : ∀ (k : ℕ) (G : Matrix (Fin n) (Fin m) (ZMod 4)) (S : Finset (Fin n)),
    S.card ≤ k → (∀ i, i ∉ S → ∀ j, G i j = 0) → (∃ r s : ℕ, 2 ^ r ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).image (fun y => y + y)).card ∧
      2 ^ (r + s) ≤ ((Finset.univ.image (fun x : Fin m → ZMod 4 => (G).mulVec x)).filter
        (fun y => ∀ i, y i + y i = 0)).card ∧
      ∀ w p q : ℕ, r ≤ p → r ≤ q → 2 * r + s ≤ p + q → r + s ≤ w →
        ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
          U * V = G ∧ Matrix.rank (fun i j => ((U i j).val : ZMod 2) : Matrix (Fin n) (Fin w) (ZMod 2)) ≤ p ∧
          Matrix.rank (fun i j => ((V i j).val : ZMod 2) : Matrix (Fin w) (Fin m) (ZMod 2)) ≤ q) := by
  intro k
  induction k with
  | zero =>
    intro G S hS hz
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    exact L950_base G (fun i j => hz i (by rw [hS0]; exact Finset.notMem_empty i) j)
  | succ k ih =>
    intro G S hS hz
    by_cases hall : ∀ i j, G i j = 0
    · exact L950_base G hall
    · push_neg at hall
      obtain ⟨i1, j1, h1⟩ := hall
      by_cases hodd : ∃ i j, G i j + G i j ≠ 0
      · obtain ⟨i0, j0, h0⟩ := hodd
        have hi0 : i0 ∈ S := by
          by_contra hn
          apply h0
          rw [hz i0 hn j0, add_zero]
        have hc : G i0 j0 * G i0 j0 = 1 := L950_z3 _ h0
        apply L950_odd_step G i0 j0 hc
        refine ih _ (S.erase i0) ?_ ?_
        · rw [Finset.card_erase_of_mem hi0]
          omega
        · intro i hi j
          simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
          by_cases hii : i = i0
          · rw [hii]
            linear_combination (-(G i0 j)) * hc
          · have hiS : i ∉ S := fun h => hi (Finset.mem_erase.mpr ⟨hii, h⟩)
            rw [hz i hiS j, hz i hiS j0]
            ring
      · push_neg at hodd
        have h2 : G i1 j1 = 2 := L950_z10 _ (hodd i1 j1) h1
        have hi1 : i1 ∈ S := by
          by_contra hn
          exact h1 (hz i1 hn j1)
        apply L950_even_step G i1 j1 hodd h2
        refine ih _ (S.erase i1) ?_ ?_
        · rw [Finset.card_erase_of_mem hi1]
          omega
        · intro i hi j
          simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
          by_cases hii : i = i1
          · rw [hii, L950_z5 (G i1 j1) (hodd i1 j1) h1]
            ring
          · have hiS : i ∉ S := fun h => hi (Finset.mem_erase.mpr ⟨hii, h⟩)
            rw [hz i hiS j, hz i hiS j1]
            simp

theorem PEqualNP.Outside.L_lib_950_kid.held : ∀ (n m w p q : ℕ) (G : Matrix (Fin n) (Fin m) (ZMod 4)),
  let reduce := fun {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)) =>
    (fun i j => ((M i j).val : ZMod 2) : Matrix (Fin a) (Fin b) (ZMod 2))
  let outputs := Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)
  let killed := outputs.filter (fun y => ∀ i, y i + y i = 0)
  (∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
    U * V = G ∧ Matrix.rank (reduce U) ≤ p ∧ Matrix.rank (reduce V) ≤ q) ↔
    Matrix.rank (reduce G) ≤ min p q ∧ outputs.card ≤ 2^(p+q) ∧ killed.card ≤ 2^w := by
  intro n m w p q G
  dsimp only
  constructor
  · rintro ⟨U, V, rfl, hU, hV⟩
    refine ⟨le_min ((L950_rank_red_mul U V).1.trans hU) ((L950_rank_red_mul U V).2.trans hV), ?_,
      L950_kil_le U V⟩
    refine (L950_out_le U V).trans ?_
    rw [Nat.pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hU) (Nat.pow_le_pow_right (by norm_num) hV)
  · rintro ⟨hr, hout, hkil⟩
    obtain ⟨r, s, hD, hK, hf⟩ := L950_struct (Finset.univ : Finset (Fin n)).card G Finset.univ le_rfl
      (fun i hi _ => absurd (Finset.mem_univ i) hi)
    have hrr := L950_pow_le (hD.trans (L950_lemD G))
    have hrp : r ≤ p := hrr.trans (hr.trans (min_le_left p q))
    have hrq : r ≤ q := hrr.trans (hr.trans (min_le_right p q))
    have hA := L950_lemA _ (L950_out_add G)
    have e : 2 ^ (2 * r + s) = 2 ^ (r + s) * 2 ^ r := by ring
    have h3 : 2 ^ (2 * r + s) ≤ 2 ^ (p + q) := by
      rw [e]
      exact ((Nat.mul_le_mul hK hD).trans hA).trans hout
    exact hf w p q hrp hrq (L950_pow_le h3) (L950_pow_le (hK.trans hkil))

theorem PEqualNP.Outside.L_lib_950 :
∀ (n m w p q : ℕ) (G : Matrix (Fin n) (Fin m) (ZMod 4)),
  let reduce := fun {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)) =>
    (fun i j => ((M i j).val : ZMod 2) : Matrix (Fin a) (Fin b) (ZMod 2))
  let outputs := Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)
  let killed := outputs.filter (fun y => ∀ i, y i + y i = 0)
  (∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
    U * V = G ∧ Matrix.rank (reduce U) ≤ p ∧ Matrix.rank (reduce V) ≤ q) ↔
    Matrix.rank (reduce G) ≤ min p q ∧ outputs.card ≤ 2^(p+q) ∧ killed.card ≤ 2^w :=
  PEqualNP.Outside.L_lib_950_kid.held
