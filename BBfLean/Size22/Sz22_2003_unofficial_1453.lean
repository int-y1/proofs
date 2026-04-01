import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1453: [7/15, 297/14, 22/3, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  3  0 -1  1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1453

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem b_to_a : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a := a + 1) (e := e + 1)); ring_nf; finish

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

theorem r2_chain : ∀ k, ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 3 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b := b + 3) (e := e + 1)); ring_nf; finish

theorem r3r2_chain : ∀ k, ⟨0, b + 1, 0, k, e⟩ [fm]⊢* ⟨0, b + 2 * k + 1, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · step fm; step fm
    show ⟨0, (b + 2) + 1, 0, k, e + 2⟩ [fm]⊢* _
    apply stepStar_trans (ih (b := b + 2) (e := e + 2)); ring_nf; finish

theorem drain_round : ⟨a + 1, 0, c + 3, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + 3, e + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain_loop : ∀ k, ⟨a + k, 0, c + 3 * k, d + 1, e⟩ [fm]⊢*
    ⟨a, 0, c, d + 2 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (c := c + 3))
    rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
    apply stepStar_trans (drain_round (a := a) (c := c) (d := d + 2 * k) (e := e + k))
    ring_nf; finish

theorem init_drain : ⟨a + 2, 0, c + 4, 0, 0⟩ [fm]⊢* ⟨a, 0, c, 4, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem full_drain : ⟨a + K + 2, 0, 3 * K + r + 4, 0, 0⟩ [fm]⊢*
    ⟨a, 0, r, 2 * K + 4, K + 1⟩ := by
  rw [show 3 * K + r + 4 = (3 * K + r) + 4 from by ring,
      show a + K + 2 = (a + K) + 2 from by ring]
  apply stepStar_trans (init_drain (a := a + K) (c := 3 * K + r))
  rw [show 3 * K + r = r + 3 * K from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (drain_loop K (a := a) (c := r) (d := 3) (e := 1))
  ring_nf; finish

-- General drain from (a, b, 0, D, E) -> (a+b+2D, 0, 0, 0, E+b+4D)
-- Requires a+b >= 1 (so at least R2 or R3 can fire).
theorem gen_drain (hab : a + b ≥ 1) :
    ⟨a, b, 0, D, E⟩ [fm]⊢* ⟨a + b + 2 * D, 0, 0, 0, E + b + 4 * D⟩ := by
  rcases a.eq_zero_or_pos with ha | ha
  · -- a = 0, so b >= 1
    subst ha; simp only [Nat.zero_add]
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    apply stepStar_trans (r3r2_chain D (b := b') (e := E))
    have h := b_to_a (b' + 2 * D + 1) (a := 0) (b := 0) (e := E + 2 * D)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  · -- a >= 1
    rcases le_or_gt D a with hda | hda
    · -- D <= a
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + D := ⟨a - D, by omega⟩
      have h1 := r2_chain D (a := a') (b := b) (d := 0) (e := E)
      simp only [Nat.zero_add] at h1
      apply stepStar_trans h1
      have h2 := b_to_a (b + 3 * D) (a := a') (b := 0) (e := E + D)
      simp only [Nat.zero_add] at h2
      apply stepStar_trans h2; ring_nf; finish
    · -- D > a
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + a := ⟨D - a, by omega⟩
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have h1 := r2_chain (a' + 1) (a := 0) (b := b) (d := D') (e := E)
      simp only [Nat.zero_add] at h1
      apply stepStar_trans h1
      rw [show b + 3 * (a' + 1) = (b + 3 * a' + 2) + 1 from by ring]
      apply stepStar_trans (r3r2_chain D' (b := b + 3 * a' + 2) (e := E + (a' + 1)))
      have h2 := b_to_a (b + 3 * a' + 2 + 2 * D' + 1) (a := 0) (b := 0) (e := E + (a' + 1) + 2 * D')
      simp only [Nat.zero_add] at h2
      apply stepStar_trans h2; ring_nf; finish

-- End phase r=0
theorem end_r0 (ha : a ≥ 1) :
    ⟨a, 0, 0, D, E⟩ [fm]⊢* ⟨a + 2 * D, 0, E + 4 * D, 0, 0⟩ := by
  have h1 := gen_drain (a := a) (b := 0) (D := D) (E := E) (by omega)
  simp only [Nat.add_zero] at h1
  apply stepStar_trans h1
  have h2 := e_to_c (E + 4 * D) (a := a + 2 * D) (c := 0) (e := 0)
  simp only [Nat.zero_add] at h2; exact h2

-- End phase r=1
theorem end_r1 (ha : a ≥ 1) (hD : D ≥ 1) :
    ⟨a, 0, 1, D, E⟩ [fm]⊢* ⟨a + 2 * D + 1, 0, E + 4 * D + 3, 0, 0⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  step fm; step fm
  apply stepStar_trans (gen_drain (a := a') (b := 2) (D := D' + 1) (E := E + 1) (by omega))
  have h := e_to_c (E + 1 + 2 + 4 * (D' + 1)) (a := a' + 2 + 2 * (D' + 1)) (c := 0) (e := 0)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h; ring_nf; finish

-- End phase r=2
theorem end_r2 (ha : a ≥ 1) (hD : D ≥ 1) :
    ⟨a, 0, 2, D, E⟩ [fm]⊢* ⟨a + 2 * D + 2, 0, E + 4 * D + 6, 0, 0⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  step fm; step fm; step fm
  apply stepStar_trans (gen_drain (a := a') (b := 1) (D := D' + 2) (E := E + 1) (by omega))
  have h := e_to_c (E + 1 + 1 + 4 * (D' + 2)) (a := a' + 1 + 2 * (D' + 2)) (c := 0) (e := 0)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h; ring_nf; finish

-- Base C=0: R5 + R2 + gen_drain + e_to_c
theorem base_c0_star : ⟨a + 2, 0, 0, 0, 0⟩ [fm]⊢* ⟨a + 4, 0, 5, 0, 0⟩ := by
  step fm; step fm  -- (a, 4, 0, 0, 1)
  apply stepStar_trans (gen_drain (a := a) (b := 4) (D := 0) (E := 1) (by omega))
  simp only [Nat.mul_zero, Nat.add_zero]
  have h := e_to_c 5 (a := a + 4) (c := 0) (e := 0)
  simp only [Nat.zero_add] at h; exact h

private theorem ne_of_third {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : ℕ}
    (h : c₁ ≠ c₂) : (a₁, b₁, c₁, d₁, e₁) ≠ (a₂, b₂, c₂, d₂, e₂) := by
  intro heq; exact h (by exact congrArg (fun x => x.2.2.1) heq)

theorem base_c0 : ⟨a + 2, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 5, 0, 0⟩ :=
  stepStar_stepPlus base_c0_star (ne_of_third (by omega))

-- Base C=1
theorem base_c1_star : ⟨a + 2, 0, 1, 0, 0⟩ [fm]⊢* ⟨a + 5, 0, 8, 0, 0⟩ := by
  step fm; step fm
  exact end_r0 (a := a + 1) (D := 2) (E := 0) (by omega)

theorem base_c1 : ⟨a + 2, 0, 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 5, 0, 8, 0, 0⟩ :=
  stepStar_stepPlus base_c1_star (ne_of_third (by omega))

-- Base C=2
theorem base_c2_star : ⟨a + 2, 0, 2, 0, 0⟩ [fm]⊢* ⟨a + 6, 0, 11, 0, 0⟩ := by
  step fm; step fm
  exact end_r1 (a := a + 1) (D := 2) (E := 0) (by omega) (by omega)

theorem base_c2 : ⟨a + 2, 0, 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 6, 0, 11, 0, 0⟩ :=
  stepStar_stepPlus base_c2_star (ne_of_third (by omega))

-- Base C=3
theorem base_c3_star : ⟨a + 2, 0, 3, 0, 0⟩ [fm]⊢* ⟨a + 7, 0, 14, 0, 0⟩ := by
  step fm; step fm
  exact end_r2 (a := a + 1) (D := 2) (E := 0) (by omega) (by omega)

theorem base_c3 : ⟨a + 2, 0, 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 7, 0, 14, 0, 0⟩ :=
  stepStar_stepPlus base_c3_star (ne_of_third (by omega))

-- Big transitions for C >= 4
theorem big_trans_r0 (ha : a ≥ 1) :
    ⟨a + K + 2, 0, 3 * K + 4, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * K + 8, 0, 9 * K + 17, 0, 0⟩ := by
  apply stepStar_stepPlus
  · apply stepStar_trans (full_drain (r := 0))
    apply stepStar_trans (end_r0 (a := a) (D := 2 * K + 4) (E := K + 1) ha)
    ring_nf; finish
  · exact ne_of_third (by omega)

theorem big_trans_r1 (ha : a ≥ 1) :
    ⟨a + K + 2, 0, 3 * K + 5, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * K + 9, 0, 9 * K + 20, 0, 0⟩ := by
  apply stepStar_stepPlus
  · apply stepStar_trans (full_drain (r := 1))
    apply stepStar_trans (end_r1 (a := a) (D := 2 * K + 4) (E := K + 1) ha (by omega))
    ring_nf; finish
  · exact ne_of_third (by omega)

theorem big_trans_r2 (ha : a ≥ 1) :
    ⟨a + K + 2, 0, 3 * K + 6, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * K + 10, 0, 9 * K + 23, 0, 0⟩ := by
  apply stepStar_stepPlus
  · apply stepStar_trans (full_drain (r := 2))
    apply stepStar_trans (end_r2 (a := a) (D := 2 * K + 4) (E := K + 1) ha (by omega))
    ring_nf; finish
  · exact ne_of_third (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 5, 0, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A C, q = ⟨A, 0, C, 0, 0⟩ ∧ A ≥ 2 ∧ C ≤ 3 * (A - 1))
  · intro c ⟨A, C, hq, hA, hC⟩; subst hq
    refine ⟨⟨A + C + 2, 0, 3 * C + 5, 0, 0⟩,
            ⟨A + C + 2, 3 * C + 5, rfl, by omega, by omega⟩, ?_⟩
    rcases (show C ≤ 3 ∨ C ≥ 4 from by omega) with hsmall | hbig
    · interval_cases C
      · obtain ⟨a, rfl⟩ : ∃ a, A = a + 2 := ⟨A - 2, by omega⟩; exact base_c0
      · obtain ⟨a, rfl⟩ : ∃ a, A = a + 2 := ⟨A - 2, by omega⟩; exact base_c1
      · obtain ⟨a, rfl⟩ : ∃ a, A = a + 2 := ⟨A - 2, by omega⟩; exact base_c2
      · obtain ⟨a, rfl⟩ : ∃ a, A = a + 2 := ⟨A - 2, by omega⟩; exact base_c3
    · obtain ⟨K, r, hr, rfl⟩ : ∃ K r, r < 3 ∧ C = 3 * K + r + 4 := by
        exact ⟨(C - 4) / 3, (C - 4) % 3, Nat.mod_lt _ (by omega), by omega⟩
      obtain ⟨a, rfl⟩ : ∃ a, A = a + K + 2 := ⟨A - K - 2, by omega⟩
      have ha : a ≥ 1 := by omega
      interval_cases r
      · show ⟨a + K + 2, 0, 3 * K + 0 + 4, 0, 0⟩ [fm]⊢⁺ _
        rw [show 3 * K + 0 + 4 = 3 * K + 4 from by ring,
            show a + K + 2 + (3 * K + 0 + 4) + 2 = a + 4 * K + 8 from by ring,
            show 3 * (3 * K + 0 + 4) + 5 = 9 * K + 17 from by ring]
        exact big_trans_r0 ha
      · show ⟨a + K + 2, 0, 3 * K + 1 + 4, 0, 0⟩ [fm]⊢⁺ _
        rw [show 3 * K + 1 + 4 = 3 * K + 5 from by ring,
            show a + K + 2 + (3 * K + 1 + 4) + 2 = a + 4 * K + 9 from by ring,
            show 3 * (3 * K + 1 + 4) + 5 = 9 * K + 20 from by ring]
        exact big_trans_r1 ha
      · show ⟨a + K + 2, 0, 3 * K + 2 + 4, 0, 0⟩ [fm]⊢⁺ _
        rw [show 3 * K + 2 + 4 = 3 * K + 6 from by ring,
            show a + K + 2 + (3 * K + 2 + 4) + 2 = a + 4 * K + 10 from by ring,
            show 3 * (3 * K + 2 + 4) + 5 = 9 * K + 23 from by ring]
        exact big_trans_r2 ha
  · exact ⟨3, 5, rfl, by omega, by omega⟩
