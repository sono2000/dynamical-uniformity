import Mathlib

set_option linter.unusedSectionVars false

open Finset Pointwise

section DynamicalAlgebraicCore

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- The canonical quadratic map f(X) = X^2 + c -/
def fQuad (c : R) (x : R) : R := x^2 + c

/-- The pointwise squaring map on elements -/
def sqMap (x : R) : R := x^2

/-- Pointwise product set A · B -/
def mulSet (A B : Finset R) : Finset R := (A ×ˢ B).image (fun p => p.1 * p.2)

/-- Pointwise set of squares A^2 -/
def sqSet (A : Finset R) : Finset R := A.image (fun x => x^2)

/-- Scalar dilation t · A -/
def smulSet (t : R) (A : Finset R) : Finset R := A.image (fun x => t * x)

/-- Additive Energy between two finite sets in a commutative ring -/
def additiveEnergy (A B : Finset R) : Nat :=
  (((A ×ˢ A) ×ˢ (B ×ˢ B)).filter (fun p => p.1.1 + p.2.1 = p.1.2 + p.2.2)).card

/-! ### 1. Exact Set-Algebraic Invariance: C^2 = C - c (Lemma 3.1) -/

/-- If C is invariant under f(X) = X^2 + c, then C^2 = C - c. -/
theorem cycle_square_set_eq (c : R) (C : Finset R) 
    (h_inv : C.image (fQuad c) = C) :
    C.image sqMap = C.image (fun x => x - c) := by
  have h_comp : sqMap = (fun y : R => y - c) ∘ (fQuad c) := by
    ext x
    simp [sqMap, fQuad]
  rw [h_comp, ← Finset.image_image, h_inv]

/-! ### 2. Sumset Cardinality Isometry: |C^2 + C^2| = |C + C| (Lemma 3.1, Part 1) -/

/-- Translation of a finset preserves its cardinality -/
theorem card_image_sub_const (A : Finset R) (t : R) :
    (A.image (fun x => x - t)).card = A.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact sub_left_inj.mp hxy

/-- Algebraic translation of a sumset -/
theorem sumset_shift (A B : Finset R) (c : R) :
    (A.image (fun x => x - c)) + (B.image (fun x => x - c)) = 
    (A + B).image (fun x => x - 2 * c) := by
  ext z
  simp only [Finset.mem_add, Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨u, hu, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨u + v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
    ring
  · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    refine ⟨u - c, ⟨u, hu, rfl⟩, v - c, ⟨v, hv, rfl⟩, ?_⟩
    ring

/-- Lemma 3.1 (Part 1): |C^2 + C^2| = |C + C| -/
theorem sumset_card_isometry (c : R) (C : Finset R) 
    (h_inv : C.image (fQuad c) = C) :
    ((C.image sqMap) + (C.image sqMap)).card = (C + C).card := by
  rw [cycle_square_set_eq c C h_inv]
  rw [sumset_shift C C c]
  exact card_image_sub_const (C + C) (2 * c)



/-! ### 3. Additive Energy Invariance under Translations (Lemma 3.1, Parts 2 & 3) -/

/-- Shifting the second set by -c preserves additive energy -/
theorem additiveEnergy_shift_right (A B : Finset R) (c : R) :
    additiveEnergy A (B.image (fun x => x - c)) = additiveEnergy A B := by
  dsimp [additiveEnergy]
  apply Finset.card_bij (fun ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ _ => (⟨x1, x2⟩, ⟨y1 + c, y2 + c⟩))
  · rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ hp
    have h_cond : x1 + y1 = x2 + y2 := (mem_filter.mp hp).2
    have h_prod : (x1, x2) ∈ A ×ˢ A ∧ (y1, y2) ∈ (B.image (fun x => x - c)) ×ˢ (B.image (fun x => x - c)) := 
      mem_product.mp (mem_filter.mp hp).1
    have hA : x1 ∈ A ∧ x2 ∈ A := mem_product.mp h_prod.1
    have hB : y1 ∈ B.image (fun x => x - c) ∧ y2 ∈ B.image (fun x => x - c) := mem_product.mp h_prod.2
    rcases mem_image.mp hB.1 with ⟨b1, hb1, rfl⟩
    rcases mem_image.mp hB.2 with ⟨b2, hb2, rfl⟩
    rw [mem_filter]
    refine ⟨mem_product.mpr ⟨mem_product.mpr hA, mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · simp only [sub_add_cancel, hb1]
    · simp only [sub_add_cancel, hb2]
    · dsimp at h_cond ⊢
      linear_combination h_cond
  · rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ _ ⟨⟨x1', x2'⟩, ⟨y1', y2'⟩⟩ _ h
    simp only [Prod.mk.injEq, add_left_inj] at h
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := h
    rw [hx1, hx2, hy1, hy2]
  · rintro ⟨⟨x1, x2⟩, ⟨b1, b2⟩⟩ hq
    have h_cond : x1 + b1 = x2 + b2 := (mem_filter.mp hq).2
    have h_prod : (x1, x2) ∈ A ×ˢ A ∧ (b1, b2) ∈ B ×ˢ B := 
      mem_product.mp (mem_filter.mp hq).1
    have hA : x1 ∈ A ∧ x2 ∈ A := mem_product.mp h_prod.1
    have hB : b1 ∈ B ∧ b2 ∈ B := mem_product.mp h_prod.2
    refine ⟨((x1, x2), (b1 - c, b2 - c)), ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_product.mpr ⟨mem_product.mpr hA, mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
      · exact mem_image_of_mem (fun x => x - c) hB.1
      · exact mem_image_of_mem (fun x => x - c) hB.2
      · dsimp at h_cond ⊢
        linear_combination h_cond
    · simp only [sub_add_cancel]

/-- Shifting the first set by -c preserves additive energy -/
theorem additiveEnergy_shift_left (A B : Finset R) (c : R) :
    additiveEnergy (A.image (fun x => x - c)) B = additiveEnergy A B := by
  dsimp [additiveEnergy]
  apply Finset.card_bij (fun ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ _ => (⟨x1 + c, x2 + c⟩, ⟨y1, y2⟩))
  · rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ hp
    have h_cond : x1 + y1 = x2 + y2 := (mem_filter.mp hp).2
    have h_prod : (x1, x2) ∈ (A.image (fun x => x - c)) ×ˢ (A.image (fun x => x - c)) ∧ (y1, y2) ∈ B ×ˢ B := 
      mem_product.mp (mem_filter.mp hp).1
    have hA : x1 ∈ A.image (fun x => x - c) ∧ x2 ∈ A.image (fun x => x - c) := mem_product.mp h_prod.1
    have hB : y1 ∈ B ∧ y2 ∈ B := mem_product.mp h_prod.2
    rcases mem_image.mp hA.1 with ⟨a1, ha1, rfl⟩
    rcases mem_image.mp hA.2 with ⟨a2, ha2, rfl⟩
    rw [mem_filter]
    refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, mem_product.mpr hB⟩, ?_⟩
    · simp only [sub_add_cancel, ha1]
    · simp only [sub_add_cancel, ha2]
    · dsimp at h_cond ⊢
      linear_combination h_cond
  · rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ _ ⟨⟨x1', x2'⟩, ⟨y1', y2'⟩⟩ _ h
    simp only [Prod.mk.injEq, add_left_inj] at h
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := h
    rw [hx1, hx2, hy1, hy2]
  · rintro ⟨⟨a1, a2⟩, ⟨y1, y2⟩⟩ hq
    have h_cond : a1 + y1 = a2 + y2 := (mem_filter.mp hq).2
    have h_prod : (a1, a2) ∈ A ×ˢ A ∧ (y1, y2) ∈ B ×ˢ B := 
      mem_product.mp (mem_filter.mp hq).1
    have hA : a1 ∈ A ∧ a2 ∈ A := mem_product.mp h_prod.1
    have hB : y1 ∈ B ∧ y2 ∈ B := mem_product.mp h_prod.2
    refine ⟨((a1 - c, a2 - c), (y1, y2)), ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, mem_product.mpr hB⟩, ?_⟩
      · exact mem_image_of_mem (fun x => x - c) hA.1
      · exact mem_image_of_mem (fun x => x - c) hA.2
      · dsimp at h_cond ⊢
        linear_combination h_cond
    · simp only [sub_add_cancel]

/-- Lemma 3.1 (Part 3): E+(C, C^2) = E+(C, C) -/
theorem energy_C_Csq_eq_energy_C_C (c : R) (C : Finset R) 
    (h_inv : C.image (fQuad c) = C) :
    additiveEnergy C (C.image sqMap) = additiveEnergy C C := by
  rw [cycle_square_set_eq c C h_inv]
  exact additiveEnergy_shift_right C C c

/-- Lemma 3.1 (Part 2): E+(C^2, C^2) = E+(C, C) -/
theorem energy_Csq_Csq_eq_energy_C_C (c : R) (C : Finset R) 
    (h_inv : C.image (fQuad c) = C) :
    additiveEnergy (C.image sqMap) (C.image sqMap) = additiveEnergy C C := by
  rw [cycle_square_set_eq c C h_inv]
  rw [additiveEnergy_shift_left C (C.image (fun x => x - c)) c]
  exact additiveEnergy_shift_right C C c

/-! ### 4. Trivial Additive Energy Upper Bound: E+(A, A) ≤ |A|^3 -/

/-- Trivial bound on additive energy: choosing (x1, x2, y1) uniquely forces y2 -/
theorem additiveEnergy_le_card_cubed (A : Finset R) :
    additiveEnergy A A ≤ A.card ^ 3 := by
  dsimp [additiveEnergy]
  let proj : (R × R) × (R × R) → (R × R) × R :=
    fun ⟨⟨x1, x2⟩, ⟨y1, _⟩⟩ => ((x1, x2), y1)
  have h_maps : ∀ p ∈ (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun p => p.1.1 + p.2.1 = p.1.2 + p.2.2)),
                proj p ∈ (A ×ˢ A) ×ˢ A := by
    rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ hp
    have h_prod := (mem_filter.mp hp).1
    have hA1 := mem_product.mp (mem_product.mp h_prod).1
    have hA2 := mem_product.mp (mem_product.mp h_prod).2
    simp only [mem_product]
    exact ⟨⟨hA1.1, hA1.2⟩, hA2.1⟩
  have h_inj : ∀ p1 ∈ (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun p => p.1.1 + p.2.1 = p.1.2 + p.2.2)),
               ∀ p2 ∈ (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun p => p.1.1 + p.2.1 = p.1.2 + p.2.2)),
               proj p1 = proj p2 → p1 = p2 := by
    rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ hp1 ⟨⟨x1', x2'⟩, ⟨y1', y2'⟩⟩ hp2 h_proj
    have heq1 : x1 + y1 = x2 + y2 := (mem_filter.mp hp1).2
    have heq2 : x1' + y1' = x2' + y2' := (mem_filter.mp hp2).2
    simp only [proj, Prod.mk.injEq] at h_proj
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h_proj
    have h_eq : x2 + y2 = x2 + y2' := by rw [← heq1, heq2]
    have hy2 : y2 = y2' := add_left_cancel h_eq
    rw [hy2]
  have h_card := Finset.card_le_card_of_injOn proj h_maps h_inj
  have h_target : ((A ×ˢ A) ×ˢ A).card = A.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product]
    ring
  rw [h_target] at h_card
  exact h_card

/-! ### 5. Parabolic Secant Rigidity and Vieta Root Invariance (Theorem 4.2) -/

/-- Vieta Root Theorem: Over an integral domain, two elements sharing the same sum and product
    are identical up to transposition. -/
theorem vieta_symmetric_solution {K : Type*} [CommRing K] [IsDomain K] 
    (x1 x2 y1 y2 : K) 
    (h_sum : x1 + x2 = y1 + y2) (h_prod : x1 * x2 = y1 * y2) :
    (x1 = y1 ∧ x2 = y2) ∨ (x1 = y2 ∧ x2 = y1) := by
  have h_poly : (y1 - x1) * (y1 - x2) = 0 := by
    calc (y1 - x1) * (y1 - x2) 
      _ = y1^2 - (x1 + x2) * y1 + x1 * x2 := by ring
      _ = y1^2 - (y1 + y2) * y1 + y1 * y2 := by rw [h_sum, h_prod]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_poly with h1 | h2
  · have hx1 : x1 = y1 := by linear_combination -h1
    have hx2 : x2 = y2 := by linear_combination h_sum - hx1
    exact Or.inl ⟨hx1, hx2⟩
  · have hx2 : x2 = y1 := by linear_combination -h2
    have hx1 : x1 = y2 := by linear_combination h_sum - hx2
    exact Or.inr ⟨hx1, hx2⟩

/-- Parabolic Secant Uniqueness: Any two pairs determining the same secant line on y = x^2 + c
    must coincide as unordered pairs. -/
theorem parabolic_secant_uniqueness {K : Type*} [CommRing K] [IsDomain K]
    (c : K) (x1 x2 y1 y2 : K)
    (h_secant : (x1 + x2, c - x1 * x2) = (y1 + y2, c - y1 * y2)) :
    (x1 = y1 ∧ x2 = y2) ∨ (x1 = y2 ∧ x2 = y1) := by
  injection h_secant with h_sum h_int
  have h_prod : x1 * x2 = y1 * y2 := by linear_combination -h_int
  exact vieta_symmetric_solution x1 x2 y1 y2 h_sum h_prod

/-- Theorem 4.2 (Parabolic Secant Injection): The secant parameter map on ordered pairs
    is strictly injective, establishing the foundation of |A · A| ≥ (|A|(|A|-1))/(2|A+A|). -/
theorem parabolic_secant_ordered_injective {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K]
    (c : K) (x1 x2 y1 y2 : K) (hx : x1 < x2) (hy : y1 < y2)
    (h_secant : (x1 + x2, c - x1 * x2) = (y1 + y2, c - y1 * y2)) :
    x1 = y1 ∧ x2 = y2 := by
  rcases parabolic_secant_uniqueness c x1 x2 y1 y2 h_secant with h_same | h_swap
  · exact h_same
  · obtain ⟨rfl, rfl⟩ := h_swap
    exact (lt_asymm hx hy).elim

/-! ### 6. Algebraic Polarization and Dynamical Product Containment -/

/-- Polarization Identity: 2*(x*y) = (x+y)^2 - x^2 - y^2 -/
theorem polarization_identity (x y : R) :
    2 * (x * y) = (x + y)^2 - x^2 - y^2 := by ring

/-- Theorem (Polarization Set Containment): 
    Every element of 2*(A · B) is contained in (A+B)^2 - A^2 - B^2 -/
theorem polarization_set_containment (A B : Finset R) (w : R) 
    (hw : w ∈ smulSet 2 (mulSet A B)) :
    ∃ s ∈ sqSet (A + B), ∃ u ∈ sqSet A, ∃ v ∈ sqSet B, w = s - u - v := by
  simp only [smulSet, mulSet, sqSet, mem_image, mem_product] at hw ⊢
  rcases hw with ⟨_, ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, rfl⟩
  refine ⟨(a + b)^2, ⟨a + b, ?_, rfl⟩, a^2, ⟨a, ha, rfl⟩, b^2, ⟨b, hb, rfl⟩, ?_⟩
  · exact mem_add.mpr ⟨a, ha, b, hb, rfl⟩
  · ring

/-- Dynamical Product Reduction: Products in the cycle C · C are controlled by the sumset C+C -/
theorem dynamical_product_in_sumset_squares (c : R) (C : Finset R)
    (h_inv : C.image (fQuad c) = C) (w : R) (hw : w ∈ smulSet 2 (mulSet C C)) :
    ∃ s ∈ sqSet (C + C), ∃ u ∈ C, ∃ v ∈ C, w = s - (u - c) - (v - c) := by
  rcases polarization_set_containment C C w hw with ⟨s, hs, u_sq, hu_sq, v_sq, hv_sq, rfl⟩
  have hCsq : sqSet C = C.image (fun x => x - c) := by
    exact cycle_square_set_eq c C h_inv
  rw [hCsq] at hu_sq hv_sq
  simp only [mem_image] at hu_sq hv_sq
  rcases hu_sq with ⟨u, hu, rfl⟩
  rcases hv_sq with ⟨v, hv, rfl⟩
  exact ⟨s, hs, u, hu, v, hv, rfl⟩

/-! ### 7. Koopman / Permutation Isometry on the Orbit (Strategy B) -/

/-- Pullback Koopman operator under the dynamical map -/
def koopman (f : R → R) (ψ : R → Complex) : R → Complex := fun x => ψ (f x)

/-- Theorem: The dynamical permutation preserves the L2-energy on the invariant cycle -/
theorem koopman_l2_isometry (c : R) (C : Finset R) 
    (h_inv : C.image (fQuad c) = C) (h_inj : ∀ x ∈ C, ∀ y ∈ C, fQuad c x = fQuad c y → x = y)
    (ψ : R → Complex) :
    ∑ x ∈ C, ‖koopman (fQuad c) ψ x‖^2 = ∑ x ∈ C, ‖ψ x‖^2 := by
  dsimp [koopman]
  have h_sum : ∑ x ∈ C.image (fQuad c), ‖ψ x‖^2 = ∑ x ∈ C, ‖ψ (fQuad c x)‖^2 := by
    exact Finset.sum_image h_inj
  rw [h_inv] at h_sum
  exact h_sum.symm

end DynamicalAlgebraicCore

section HarmonicFrequencyInvariance

/-! ### 8. Frequency-Invariance of Modulated Autocorrelations (Lemma 6.1) -/

variable {L : Nat} [NeZero L]

/-- The cyclic Hermitian autocorrelation sum on Complex -/
noncomputable def cyclicAutocorr (u : ZMod L → Complex) (h : ZMod L) : Complex :=
  (∑ n : ZMod L, u n * starRingEnd Complex (u (n + h))) / (L : Complex)

/-- A unitary character phase factor on ZMod L -/
structure PhaseChar (L : Nat) where
  toFun : ZMod L → Complex
  map_add' : ∀ x y, toFun (x + y) = toFun x * toFun y
  norm_eq_one' : ∀ x, ‖toFun x‖ = 1
  star_eq_inv' : ∀ x, starRingEnd Complex (toFun x) = (toFun x)⁻¹

/-- Lemma 6.1: Harmonic modulation preserves exact autocorrelation magnitude -/
theorem modulated_autocorr_modulus_eq 
    (u : ZMod L → Complex) (ψ : PhaseChar L) (h : ZMod L) :
    ‖cyclicAutocorr (fun n => u n * ψ.toFun n) h‖ = ‖cyclicAutocorr u h‖ := by
  dsimp [cyclicAutocorr]
  have h_sum : (∑ n : ZMod L, (u n * ψ.toFun n) * starRingEnd Complex (u (n + h) * ψ.toFun (n + h))) =
               (ψ.toFun h)⁻¹ * (∑ n : ZMod L, u n * starRingEnd Complex (u (n + h))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have h_shift : ψ.toFun (n + h) = ψ.toFun n * ψ.toFun h := ψ.map_add' n h
    rw [h_shift, map_mul, map_mul, ψ.star_eq_inv' n, ψ.star_eq_inv' h]
    have h_nz : ψ.toFun n ≠ 0 := by
      intro hz
      have h1 : ‖ψ.toFun n‖ = 1 := ψ.norm_eq_one' n
      rw [hz, norm_zero] at h1
      norm_num at h1
    have h_cancel : ψ.toFun n * (ψ.toFun n)⁻¹ = 1 := mul_inv_cancel₀ h_nz
    have h_assoc : (u n * ψ.toFun n) * (starRingEnd Complex (u (n + h)) * ((ψ.toFun n)⁻¹ * (ψ.toFun h)⁻¹)) =
                   (u n * starRingEnd Complex (u (n + h))) * (ψ.toFun n * (ψ.toFun n)⁻¹) * (ψ.toFun h)⁻¹ := by ring
    rw [h_assoc, h_cancel]
    ring
  rw [h_sum]
  have hL_pos : (L : Complex) ≠ 0 := by
    simp [NeZero.ne L]
  rw [mul_div_assoc, norm_mul]
  have h_inv_norm : ‖(ψ.toFun h)⁻¹‖ = 1 := by
    rw [norm_inv, ψ.norm_eq_one' h, inv_one]
  rw [h_inv_norm, one_mul]

/-! ### 9. Gowers U2 Autocorrelation Algebraic Expansion (Theorem 5.3) -/

/-- Theorem 5.3 (Autocorrelation L2 Algebraic Expansion): 
    The sum of squared cyclic autocorrelations expands identically as a normalized double convolution. -/
theorem autocorr_l2_sum_expansion (u : ZMod L → Complex) :
    (∑ h : ZMod L, (cyclicAutocorr u h) * starRingEnd Complex (cyclicAutocorr u h)) =
    (1 / (L : Complex)^2) * ∑ h : ZMod L, ((∑ n : ZMod L, u n * starRingEnd Complex (u (n + h))) * 
                                     starRingEnd Complex (∑ m : ZMod L, u m * starRingEnd Complex (u (m + h)))) := by
  dsimp [cyclicAutocorr]
  have h_pull : ∀ h : ZMod L, 
      ((∑ n : ZMod L, u n * starRingEnd Complex (u (n + h))) / (L : Complex)) * 
      starRingEnd Complex ((∑ m : ZMod L, u m * starRingEnd Complex (u (m + h))) / (L : Complex)) =
      (1 / (L : Complex)^2) * ((∑ n : ZMod L, u n * starRingEnd Complex (u (n + h))) * 
                         starRingEnd Complex (∑ m : ZMod L, u m * starRingEnd Complex (u (m + h)))) := by
    intro h
    simp only [map_div₀]
    have hL : starRingEnd Complex (L : Complex) = (L : Complex) := by
      simp only [starRingEnd_apply, star_natCast]
    rw [hL]
    ring
  simp_rw [h_pull]
  rw [← Finset.mul_sum]

end HarmonicFrequencyInvariance

/-! ===========================================================================
    EXTENDED FORMALIZATION: SECTIONS 10 - 13 (TABLE 3 PROGRAM EXTENSIONS)
   =========================================================================== -/

section Sym2Dynamics

variable {R : Type*} [CommRing R]

/-- The coordinates e1' and e2' under the symmetric square pushforward -/
def sym2_e1' (c e1 e2 : R) : R := e1^2 - 2 * e2 + 2 * c
def sym2_e2' (c e1 e2 : R) : R := e2^2 + c * (e1^2 - 2 * e2) + c^2

/-- The discriminant Delta = e1^2 - 4 * e2 -/
def sym2_discriminant (e1 e2 : R) : R := e1^2 - 4 * e2

/-! ### 10. Sym^2 Pushforward Dynamics and Discriminant Invariance (Theorem 4.3) -/

/-- Theorem 4.3: Pushforward of elementary symmetric sums matches sym2_e1' -/
theorem sym2_e1_pushforward (c x1 x2 : R) :
    (fQuad c x1) + (fQuad c x2) = sym2_e1' c (x1 + x2) (x1 * x2) := by
  dsimp [fQuad, sym2_e1']
  ring

/-- Theorem 4.3: Pushforward of elementary symmetric products matches sym2_e2' -/
theorem sym2_e2_pushforward (c x1 x2 : R) :
    (fQuad c x1) * (fQuad c x2) = sym2_e2' c (x1 + x2) (x1 * x2) := by
  dsimp [fQuad, sym2_e2']
  ring

/-- Theorem 4.3 (Discriminant Multiplicative Law): Delta' = Delta * e1^2 -/
theorem sym2_discriminant_evolution (c e1 e2 : R) :
    sym2_discriminant (sym2_e1' c e1 e2) (sym2_e2' c e1 e2) =
    (sym2_discriminant e1 e2) * e1^2 := by
  dsimp [sym2_discriminant, sym2_e1', sym2_e2']
  ring

/-- Exact difference squaring identity: (f(x1) - f(x2))^2 = (x1 - x2)^2 * (x1 + x2)^2 -/
theorem quadratic_diff_sq (c x1 x2 : R) :
    (fQuad c x1 - fQuad c x2)^2 = (x1 - x2)^2 * (x1 + x2)^2 := by
  dsimp [fQuad]
  ring

end Sym2Dynamics

section SecantFoliation

variable {R : Type*} [CommRing R]

/-- Slope s1(x) = x^2 + x + c of consecutive secant line -/
def secant_s1 (c x : R) : R := x^2 + x + c

/-- Intercept b1(x) = c - x^3 - c*x of consecutive secant line -/
def secant_b1 (c x : R) : R := c - x^3 - c * x

/-! ### 11. Consecutive Secant Plane Cubic & Rational Inversion (Theorem 4.6, k=1) -/

/-- Theorem 4.6 (Consecutive Secant Cubic Equation):
    The secant coordinates (s1, b1) satisfy the cubic polynomial identity identically. -/
theorem secant_cubic_relation (c x : R) :
    let s := secant_s1 c x
    let b := secant_b1 c x
    b^2 - (3 * s + 1) * b - s^3 + c * s^2 + 2 * c * s + c = 0 := by
  intro s b
  dsimp [s, b, secant_s1, secant_b1]
  ring

/-- Theorem 4.6 (Rational Inverse Reconstruction):
    (s1 - b1) = x * (s1 + 1), enabling birational inversion x = (s1 - b1) / (s1 + 1). -/
theorem secant_cubic_inverse_relation (c x : R) :
    (secant_s1 c x) - (secant_b1 c x) = x * ((secant_s1 c x) + 1) := by
  dsimp [secant_s1, secant_b1]
  ring

end SecantFoliation

section CyclicPairSumProduct

variable {R : Type*} [CommRing R]
variable {L : Nat} [NeZero L]

/-- Orbit recurrence under f(X) = X^2 + c -/
def IsOrbit (c : R) (x : ZMod L → R) : Prop :=
  ∀ k : ZMod L, x (k + 1) = fQuad c (x k)

/-! ### 12. Cyclic Difference Factorization and Pair-Sum Product Theorem (Theorem 4.2) -/

/-- Step difference factor: x(k+1) - x(k+1+h) = (x(k) - x(k+h)) * (x(k) + x(k+h)) -/
theorem orbit_step_diff_factor (c : R) (x : ZMod L → R) (h_orb : IsOrbit c x) (h : ZMod L) (k : ZMod L) :
    x (k + 1) - x (k + 1 + h) = (x k - x (k + h)) * (x k + x (k + h)) := by
  have h1 : x (k + 1) = (x k)^2 + c := by
    have := h_orb k
    dsimp [fQuad] at this
    exact this
  have h2 : x (k + 1 + h) = (x (k + h))^2 + c := by
    have h_add : k + 1 + h = (k + h) + 1 := by ring
    rw [h_add]
    have := h_orb (k + h)
    dsimp [fQuad] at this
    exact this
  rw [h1, h2]
  ring

/-- Telescoping Product Identity:
    ∏_k (x_{k+1} - x_{k+1+h}) = (∏_k (x_k - x_{k+h})) * (∏_k (x_k + x_{k+h})) -/
theorem orbit_pair_diff_product (c : R) (x : ZMod L → R) (h_orb : IsOrbit c x) (h : ZMod L) :
    (∏ k : ZMod L, (x (k + 1) - x (k + 1 + h))) =
    (∏ k : ZMod L, (x k - x (k + h))) * (∏ k : ZMod L, (x k + x (k + h))) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  exact orbit_step_diff_factor c x h_orb h k

/-- Cyclic Shift Permutation Invariance on Differences:
    Because k ↦ k + 1 is a bijection of ZMod L, ∏_k (x_{k+1} - x_{k+1+h}) = ∏_k (x_k - x_{k+h}) -/
theorem prod_cyclic_shift_diff (x : ZMod L → R) (h : ZMod L) :
    (∏ k : ZMod L, (x (k + 1) - x (k + 1 + h))) = (∏ k : ZMod L, (x k - x (k + h))) := by
  have h_reindex : (∏ k : ZMod L, (x (k + 1) - x (k + 1 + h))) = 
                   (∏ k : ZMod L, (x (k + 1) - x ((k + 1) + h))) := by
    apply Finset.prod_congr rfl
    intro k _
    have h_assoc : k + 1 + h = (k + 1) + h := by ring
    rw [h_assoc]
  rw [h_reindex]
  exact Fintype.prod_equiv (Equiv.addRight 1) 
    (fun k => x (k + 1) - x ((k + 1) + h)) 
    (fun k => x k - x (k + h)) 
    (fun _ => rfl)

/-- Theorem 4.2 (Cyclic Pair-Sum Telescoping Product - General Cancellation Form):
    If D_h = ∏_k (x_k - x_{k+h}) is a non-zero divisor, then ∏_k (x_k + x_{k+h}) = 1. -/
theorem cyclic_pair_sum_product_eq_one (c : R) (x : ZMod L → R) (h_orb : IsOrbit c x) (h : ZMod L)
    (D_h : R) (hD : D_h = ∏ k : ZMod L, (x k - x (k + h)))
    (h_cancel : ∀ z : R, D_h * z = D_h → z = 1) :
    (∏ k : ZMod L, (x k + x (k + h))) = 1 := by
  have h_prod := orbit_pair_diff_product c x h_orb h
  rw [prod_cyclic_shift_diff x h, ← hD] at h_prod
  exact h_cancel (∏ k : ZMod L, (x k + x (k + h))) h_prod.symm

/-- Theorem 4.2 (Cyclic Pair-Sum Telescoping Product - Integral Domain / Field Form):
    Over any domain (such as F_p), if D_h ≠ 0, then ∏_k (x_k + x_{k+h}) = 1. -/
theorem cyclic_pair_sum_product_of_ne_zero {K : Type*} [CommRing K] [IsDomain K]
    (c : K) (x : ZMod L → K) (h_orb : IsOrbit c x) (h : ZMod L)
    (h_diff_ne : (∏ k : ZMod L, (x k - x (k + h))) ≠ 0) :
    (∏ k : ZMod L, (x k + x (k + h))) = 1 := by
  have h_prod := orbit_pair_diff_product c x h_orb h
  rw [prod_cyclic_shift_diff x h] at h_prod
  have h_factor : (∏ k : ZMod L, (x k - x (k + h))) * ((∏ k : ZMod L, (x k + x (k + h))) - 1) = 0 := by
    calc (∏ k : ZMod L, (x k - x (k + h))) * ((∏ k : ZMod L, (x k + x (k + h))) - 1)
      _ = (∏ k : ZMod L, (x k - x (k + h))) * (∏ k : ZMod L, (x k + x (k + h))) - (∏ k : ZMod L, (x k - x (k + h))) := by ring
      _ = (∏ k : ZMod L, (x k - x (k + h))) - (∏ k : ZMod L, (x k - x (k + h))) := by rw [← h_prod]
      _ = 0 := sub_self _
  rcases mul_eq_zero.mp h_factor with hD | hP
  · exact (h_diff_ne hD).elim
  · exact sub_eq_zero.mp hP

end CyclicPairSumProduct

section AmbientFourierObstruction

variable {D L p : Real}

/-! ### 13. Ambient Deligne Completion Obstruction Arithmetic (Section 3.1) -/

/-- Theorem: Ambient Deligne completion bound D * sqrt(p / L) is strictly >= 1 for all L <= p -/
theorem ambient_fourier_lower_bound (h_sparse : L ≤ p) (hL_pos : 0 < L) (hD : 1 ≤ D) :
    1 ≤ D * Real.sqrt (p / L) := by
  have h_ratio : 1 ≤ p / L := (one_le_div hL_pos).mpr h_sparse
  have h_sqrt : 1 ≤ Real.sqrt (p / L) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt h_ratio
  nlinarith

end AmbientFourierObstruction
/-! ===========================================================================
    SECTIONS 14 - 16: PARABOLIC SECANT COMBINATORICS & DYNAMICAL BSG PROPAGATION
   =========================================================================== -/

section ParabolicSecantCombinatorics

variable {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]

/-! ### 14. Combinatorial Parabolic Secant Injection on Unordered Pairs (Theorem 4.5) -/

/-- Parabolic Secant Injection on Unordered Pairs (Finset K) -/
theorem parabolic_secant_unordered_injective (c : K) (x1 x2 y1 y2 : K)
    (h_secant : (x1 + x2, c - x1 * x2) = (y1 + y2, c - y1 * y2)) :
    ({x1, x2} : Finset K) = {y1, y2} := by
  rcases parabolic_secant_uniqueness c x1 x2 y1 y2 h_secant with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Finset.pair_comm]

/-- Secant parameter evaluation map on any 2-element subset {x, y} -/
def secantParam (c : K) (s : Finset K) : K × K :=
  (∑ x ∈ s, x, c - ∏ x ∈ s, x)

theorem secantParam_pair (c : K) (x y : K) (h : x ≠ y) :
    secantParam c {x, y} = (x + y, c - x * y) := by
  dsimp [secantParam]
  rw [Finset.sum_pair h, Finset.prod_pair h]

/-- The Secant Parameter Map is strictly injective on 2-element subsets of K -/
theorem secantParam_injOn (c : K) (A : Finset K) :
    Set.InjOn (secantParam c) ↑(A.powersetCard 2) := by
  intro s1 hs1 s2 hs2 h_eq
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hs1 hs2
  obtain ⟨x1, x2, hne1, rfl⟩ := Finset.card_eq_two.mp hs1.2
  obtain ⟨y1, y2, hne2, rfl⟩ := Finset.card_eq_two.mp hs2.2
  rw [secantParam_pair c x1 x2 hne1, secantParam_pair c y1 y2 hne2] at h_eq
  exact parabolic_secant_unordered_injective c x1 x2 y1 y2 h_eq

/-- Image target containment: secantParam maps into (A+A) × (c - A·A) -/
theorem secantParam_mapsTo (c : K) (A : Finset K) :
    Set.MapsTo (secantParam c) 
      ↑(A.powersetCard 2) 
      ↑((A + A) ×ˢ ((mulSet A A).image (fun z => c - z))) := by
  intro s hs
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
  obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.mp hs.2
  have hx : x ∈ A := hs.1 (Finset.mem_insert_self x {y})
  have hy : y ∈ A := hs.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  rw [secantParam_pair c x y hne]
  rw [Finset.mem_coe, Finset.mem_product]
  refine ⟨Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
  rw [Finset.mem_image]
  refine ⟨x * y, ?_, rfl⟩
  dsimp [mulSet]
  rw [Finset.mem_image]
  refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

/-- Theorem 4.5 (Combinatorial Parabolic Secant Injection):
    Nat.choose |A| 2 ≤ |A + A| * |A · A| -/
theorem parabolic_secant_card_bound (c : K) (A : Finset K) :
    Nat.choose A.card 2 ≤ (A + A).card * (mulSet A A).card := by
  have h_inj := secantParam_injOn c A
  have h_map := secantParam_mapsTo c A
  have h_card := Finset.card_le_card_of_injOn (secantParam c) h_map h_inj
  rw [Finset.card_powersetCard 2 A] at h_card
  rw [Finset.card_product] at h_card
  have h_shift : ((mulSet A A).image (fun z => c - z)).card = (mulSet A A).card := by
    apply Finset.card_image_of_injective
    intro u v huv
    dsimp at huv
    exact sub_right_inj.mp huv
  rw [h_shift] at h_card
  exact h_card

/-! ### 15. Dynamical Polarization and Doubling Incompatibility (Theorems 4.6 - 4.8) -/

/-- Theorem 4.6 (Algebraic Identity): 2xy = (x+y)^2 - f(x) - f(y) + 2c -/
theorem dynamical_polarization_identity (c : K) (x y : K) :
    2 * (x * y) = (x + y)^2 - (fQuad c x) - (fQuad c y) + 2 * c := by
  dsimp [fQuad]
  ring

/-- Theorem 4.6 (Set Containment):
    Every element of 2*(A · A) decomposes as s^2 - u - v + 2c with s ∈ A+A and u, v ∈ f(A). -/
theorem dynamical_product_set_containment (c : K) (A : Finset K) (w : K)
    (hw : w ∈ smulSet 2 (mulSet A A)) :
    ∃ s ∈ A + A, ∃ u ∈ A.image (fQuad c), ∃ v ∈ A.image (fQuad c),
    w = s^2 - u - v + 2 * c := by
  dsimp [smulSet, mulSet] at hw
  rcases mem_image.mp hw with ⟨m, hm, rfl⟩
  rcases mem_image.mp hm with ⟨⟨a, b⟩, hp, rfl⟩
  have ha : a ∈ A := (mem_product.mp hp).1
  have hb : b ∈ A := (mem_product.mp hp).2
  refine ⟨a + b, mem_add.mpr ⟨a, ha, b, hb, rfl⟩,
          fQuad c a, mem_image_of_mem (fQuad c) ha,
          fQuad c b, mem_image_of_mem (fQuad c) hb, ?_⟩
  exact dynamical_polarization_identity c a b

/-- The dynamical bounding set W = { s^2 - y + 2c : s ∈ A+A, y ∈ f(A)+f(A) } -/
def dynamicalBoundingSet (c : K) (A : Finset K) : Finset K :=
  ((A + A) ×ˢ (A.image (fQuad c) + A.image (fQuad c))).image (fun p => p.1^2 - p.2 + 2 * c)

/-- Every element of 2*(A · A) is in the dynamical bounding set W -/
theorem smul_mulSet_subset_bounding (c : K) (A : Finset K) :
    smulSet 2 (mulSet A A) ⊆ dynamicalBoundingSet c A := by
  intro w hw
  rcases dynamical_product_set_containment c A w hw with ⟨s, hs, u, hu, v, hv, hw_eq⟩
  have h_sum : u + v ∈ A.image (fQuad c) + A.image (fQuad c) := mem_add.mpr ⟨u, hu, v, hv, rfl⟩
  dsimp [dynamicalBoundingSet]
  rw [Finset.mem_image]
  refine ⟨(s, u + v), ?_, ?_⟩
  · rw [Finset.mem_product]
    exact ⟨hs, h_sum⟩
  · dsimp
    rw [hw_eq]
    ring

/-- The bounding set cardinality is bounded by |A+A| * |f(A)+f(A)| -/
theorem card_dynamicalBoundingSet_le (c : K) (A : Finset K) :
    (dynamicalBoundingSet c A).card ≤ (A + A).card * (A.image (fQuad c) + A.image (fQuad c)).card := by
  dsimp [dynamicalBoundingSet]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]

/-- Theorem 4.7: For any subset A in a ring where 2 is invertible,
    |A · A| ≤ |A + A| * |f(A) + f(A)|. -/
theorem dynamical_product_card_le (c : K) (A : Finset K)
    (h2 : Function.Injective (fun x : K => 2 * x)) :
    (mulSet A A).card ≤ (A + A).card * (A.image (fQuad c) + A.image (fQuad c)).card := by
  have h_inj : (smulSet 2 (mulSet A A)).card = (mulSet A A).card := by
    dsimp [smulSet]
    exact Finset.card_image_of_injective (mulSet A A) h2
  rw [← h_inj]
  have h_sub := Finset.card_le_card (smul_mulSet_subset_bounding c A)
  have h_bnd := card_dynamicalBoundingSet_le c A
  exact h_sub.trans h_bnd

/-- Theorem 4.8 (Dynamical Doubling Incompatibility Theorem):
    Nat.choose |A| 2 ≤ |A + A|^2 * |f(A) + f(A)|. -/
theorem dynamical_doubling_incompatibility (c : K) (A : Finset K)
    (h2 : Function.Injective (fun x : K => 2 * x)) :
    Nat.choose A.card 2 ≤ (A + A).card ^ 2 * (A.image (fQuad c) + A.image (fQuad c)).card := by
  have h_lower := parabolic_secant_card_bound c A
  have h_upper := dynamical_product_card_le c A h2
  calc Nat.choose A.card 2 
    _ ≤ (A + A).card * (mulSet A A).card := h_lower
    _ ≤ (A + A).card * ((A + A).card * (A.image (fQuad c) + A.image (fQuad c)).card) := 
        Nat.mul_le_mul_left (A + A).card h_upper
    _ = (A + A).card ^ 2 * (A.image (fQuad c) + A.image (fQuad c)).card := by ring

/-! ### 16. Unconditional Pair-Sum Product Invariant (Theorem 4.2) -/

variable {L : Nat} [NeZero L]

/-- Unconditional Non-Vanishing of Difference Product for Injective Cycles -/
theorem orbit_diff_prod_ne_zero (x : ZMod L → K) (h_inj : Function.Injective x) 
    (h : ZMod L) (h_h : h ≠ 0) :
    (∏ k : ZMod L, (x k - x (k + h))) ≠ 0 := by
  intro h_zero
  rcases Finset.prod_eq_zero_iff.mp h_zero with ⟨k, _, hk⟩
  have h_eq : x k = x (k + h) := sub_eq_zero.mp hk
  have h_k : k = k + h := h_inj h_eq
  have h_zero_h : h = 0 := by
    calc h = (k + h) - k := by ring
    _ = k - k := by rw [← h_k]
    _ = 0 := sub_self k
  exact h_h h_zero_h

/-- Theorem 4.2 (Unconditional Pair-Sum Product Theorem):
    Any periodic cycle with pairwise distinct elements unconditionally satisfies
    ∏_{k=0}^{L-1} (x_k + x_{k+h}) = 1. -/
theorem cyclic_pair_sum_product_unconditional (c : K) (x : ZMod L → K) 
    (h_orb : IsOrbit c x) (h_inj : Function.Injective x) 
    (h : ZMod L) (h_h : h ≠ 0) :
    (∏ k : ZMod L, (x k + x (k + h))) = 1 := by
  have h_diff_ne := orbit_diff_prod_ne_zero x h_inj h h_h
  exact cyclic_pair_sum_product_of_ne_zero c x h_orb h h_diff_ne

end ParabolicSecantCombinatorics
