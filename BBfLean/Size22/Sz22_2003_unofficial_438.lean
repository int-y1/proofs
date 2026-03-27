import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #438: [27/35, 5/33, 14/3, 11/7, 147/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_438

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a d (e + 1))
  rw [show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r2_drain : ∀ k, ∀ a b c e, ⟨a, b + k, c, 0, e + k⟩ [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a b (c + 1) e)
  rw [show c + 1 + k = c + (k + 1) from by ring]; finish

theorem r3_chain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  step fm; apply stepStar_trans (ih (a + 1) (d + 1))
  rw [show a + 1 + k = a + (k + 1) from by ring,
      show d + 1 + k = d + (k + 1) from by ring]; finish

theorem r3r1_chain : ∀ k, ∀ a b, ⟨a, b + 1, k + 1, 0, 0⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k + 3, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  rw [show (k + 1) + 1 = k + 1 + 1 from by ring]; step fm; step fm
  apply stepStar_trans (ih (a + 1) (b + 2))
  rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
      show b + 2 + 2 * k + 3 = b + 2 * (k + 1) + 3 from by ring]; finish

theorem setup (a d : ℕ) : ⟨a + 1, 0, 0, 0, d + 2⟩ [fm]⊢* ⟨a, 5, 0, 0, d⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem expand (a c e : ℕ) : ⟨a + 1, 0, c + 2, 0, e⟩ [fm]⊢* ⟨a, 7, c, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem round_step (A C E : ℕ) : ⟨A + 1, 7, C, 0, E + 7⟩ [fm]⊢* ⟨A, 7, C + 5, 0, E⟩ := by
  apply stepStar_trans
  · have h := r2_drain 7 (A + 1) 0 C E
    rw [show 0 + 7 = 7 from by ring] at h; exact h
  have h := expand A (C + 5) E
  rw [show C + 5 + 2 = C + 7 from by ring] at h; exact h

-- Finish the base cases E=0..6 by interval_cases before intro
theorem finish_phase : ∀ E, E ≤ 6 → ∀ A C,
    ⟨A, 7, C, 0, E⟩ [fm]⊢* ⟨A + 3 * C + 2 * E + 7, 0, 0, 2 * C + E + 7, 0⟩ := by
  intro E hE A C; interval_cases E
  · -- E=0: (A, 7, C, 0, 0). If C=0: r3_chain 7. If C>=1: r3r1_chain then r3_chain.
    by_cases hC : C = 0
    · subst hC; apply stepStar_trans (r3_chain 7 A 0); ring_nf; finish
    · have hC1 : C ≥ 1 := by omega
      rw [show (7 : ℕ) = 6 + 1 from by ring, show C = (C - 1) + 1 from by omega]
      apply stepStar_trans (r3r1_chain (C - 1) A 6)
      apply stepStar_trans (r3_chain (6 + 2 * (C - 1) + 3) (A + (C - 1) + 1) 0)
      ring_nf; finish
  all_goals (
    first
    | (apply stepStar_trans (r2_drain 1 A 6 C 0)
       apply stepStar_trans (r3r1_chain C A 5)
       apply stepStar_trans (r3_chain (5 + 2 * C + 3) (A + C + 1) 0); ring_nf; finish)
    | (apply stepStar_trans (r2_drain 2 A 5 C 0)
       apply stepStar_trans (r3r1_chain (C + 1) A 4)
       apply stepStar_trans (r3_chain (4 + 2 * (C + 1) + 3) (A + (C + 1) + 1) 0); ring_nf; finish)
    | (apply stepStar_trans (r2_drain 3 A 4 C 0)
       apply stepStar_trans (r3r1_chain (C + 2) A 3)
       apply stepStar_trans (r3_chain (3 + 2 * (C + 2) + 3) (A + (C + 2) + 1) 0); ring_nf; finish)
    | (apply stepStar_trans (r2_drain 4 A 3 C 0)
       apply stepStar_trans (r3r1_chain (C + 3) A 2)
       apply stepStar_trans (r3_chain (2 + 2 * (C + 3) + 3) (A + (C + 3) + 1) 0); ring_nf; finish)
    | (apply stepStar_trans (r2_drain 5 A 2 C 0)
       apply stepStar_trans (r3r1_chain (C + 4) A 1)
       apply stepStar_trans (r3_chain (1 + 2 * (C + 4) + 3) (A + (C + 4) + 1) 0); ring_nf; finish)
    | (apply stepStar_trans (r2_drain 6 A 1 C 0)
       apply stepStar_trans (r3r1_chain (C + 5) A 0)
       apply stepStar_trans (r3_chain (0 + 2 * (C + 5) + 3) (A + (C + 5) + 1) 0); ring_nf; finish))

-- Round processing by strong induction on E
theorem round_process : ∀ E, ∀ A C, A ≥ E / 7 + 1 →
    ⟨A, 7, C, 0, E⟩ [fm]⊢* ⟨A + 3 * C + 2 * E + 7, 0, 0, 2 * C + E + 3 * (E / 7) + 7, 0⟩ := by
  intro E
  induction' E using Nat.strongRecOn with E ih
  intro A C hA
  by_cases hE : E ≤ 6
  · have : E / 7 = 0 := by omega
    rw [this]; simp
    exact finish_phase E hE A C
  · push_neg at hE
    apply stepStar_trans
    · have h := round_step (A - 1) C (E - 7)
      rw [show A - 1 + 1 = A from by omega, show E - 7 + 7 = E from by omega] at h; exact h
    have hEdiv : (E - 7) / 7 + 1 = E / 7 := by omega
    have hA' : A - 1 ≥ (E - 7) / 7 + 1 := by rw [hEdiv]; omega
    have hIH := ih (E - 7) (by omega) (A - 1) (C + 5) hA'
    have h1 : A - 1 + 3 * (C + 5) + 2 * (E - 7) + 7 = A + 3 * C + 2 * E + 7 := by omega
    have h2 : 2 * (C + 5) + (E - 7) + 3 * ((E - 7) / 7) + 7 = 2 * C + E + 3 * (E / 7) + 7 := by
      rw [← hEdiv]; omega
    rw [h1, h2] at hIH; exact hIH

theorem main_trans (A D : ℕ) (hA : A ≥ D + 1) :
    ⟨A + 2, 0, 0, D + 7, 0⟩ [fm]⊢⁺
    ⟨A + 2 * D + 16, 0, 0, D + 3 * (D / 7) + 13, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + 2, 0, 0, 0, D + 7⟩)
  · have h := d_to_e (D + 7) (A + 2) 0 0; simp at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + 1, 5, 0, 0, D + 5⟩)
  · have h := setup (A + 1) (D + 5)
    rw [show A + 1 + 1 = A + 2 from by ring, show D + 5 + 2 = D + 7 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + 1, 0, 5, 0, D⟩)
  · have h := r2_drain 5 (A + 1) 0 0 D
    rw [show 0 + 5 = 5 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A, 7, 3, 0, D⟩)
  · have h := expand A 3 D; rw [show 3 + 2 = 5 from by ring] at h; exact h
  have hA' : A ≥ D / 7 + 1 := by have := Nat.div_le_self D 7; omega
  have hRP := round_process D A 3 hA'
  have h1 : A + 3 * 3 + 2 * D + 7 = A + 2 * D + 16 := by ring
  have h2 : 2 * 3 + D + 3 * (D / 7) + 7 = D + 3 * (D / 7) + 13 := by ring
  rw [h1, h2] at hRP
  exact stepStar_stepPlus hRP (by
    intro heq; have := congr_arg (fun q : Q => q.2.1) heq; simp at this)

theorem trans_d6 (a : ℕ) (ha : a ≥ 7) :
    ⟨a, 0, 0, 6, 0⟩ [fm]⊢⁺ ⟨a + 12, 0, 0, 9, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a, 0, 0, 0, 6⟩)
  · have h := d_to_e 6 a 0 0; simp at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a - 1, 5, 0, 0, 4⟩)
  · have h := setup (a - 1) 4
    rw [show a - 1 + 1 = a from by omega] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a - 1, 1, 4, 0, 0⟩)
  · have h := r2_drain 4 (a - 1) 1 0 0
    rw [show 1 + 4 = 5 from by ring, show 0 + 4 = 4 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 3, 9, 0, 0, 0⟩)
  · have h := r3r1_chain 3 (a - 1) 0
    rw [show a - 1 + 3 + 1 = a + 3 from by omega] at h; exact h
  have h := r3_chain 9 (a + 3) 0
  rw [show a + 3 + 9 = a + 12 from by ring, show 0 + 9 = 9 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq; have := congr_arg (fun q : Q => q.2.1) heq; simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 6, 0⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d + 1 ∧ d ≥ 6)
  · intro q ⟨a, d, hq, ha, hd⟩
    subst hq
    by_cases hd7 : d = 6
    · subst hd7
      exact ⟨⟨a + 12, 0, 0, 9, 0⟩, ⟨a + 12, 9, rfl, by omega, by omega⟩, trans_d6 a (by omega)⟩
    · have hd7' : d ≥ 7 := by omega
      set D := d - 7
      set A := a - 2
      have hd_eq : d = D + 7 := by omega
      have ha_eq : a = A + 2 := by omega
      have hAD : A ≥ D + 1 := by omega
      rw [ha_eq, hd_eq]
      refine ⟨⟨A + 2 * D + 16, 0, 0, D + 3 * (D / 7) + 13, 0⟩,
             ⟨A + 2 * D + 16, D + 3 * (D / 7) + 13, rfl, ?_, ?_⟩,
             main_trans A D hAD⟩
      · have := Nat.div_le_self D 7; omega
      · omega
  · exact ⟨7, 6, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_438
