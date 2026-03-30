import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1091: [5/6, 3/385, 28/5, 11/2, 75/11]

Vector representation:
```
-1 -1  1  0  0
 0  1 -1 -1 -1
 2  0 -1  1  0
-1  0  0  0  1
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1091

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a := a + 1))
    step fm; ring_nf; finish

theorem r5r2r2_triples : ∀ k, ∀ b d e,
    ⟨0, b, 0, d + 2 * k, e + 3 * k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show e + 3 * (k + 1) = (e + 3) + 3 * k from by ring]
    apply stepStar_trans (ih b (d + 2) (e + 3))
    step fm; step fm; step fm; ring_nf; finish

theorem partial_end_mod2 :
    ⟨0, b, 0, d + 1, 2⟩ [fm]⊢* ⟨2, b + 2, 0, d + 1, 0⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem partial_end_mod1 :
    ⟨0, b, 0, d, 1⟩ [fm]⊢* ⟨2, b + 1, 1, d + 1, 0⟩ := by
  step fm; step fm; ring_nf; finish

theorem r1r1r3_chain : ∀ k, ∀ c d,
    ⟨2, 2 * k + 1, c, d, 0⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (d + 1))
    ring_nf; finish

theorem process_odd_b : ∀ k, ∀ c d,
    ⟨2, 2 * k + 1, c, d, 0⟩ [fm]⊢*
    ⟨2 * k + 2 * c + 3, 0, 0, d + 2 * k + c + 1, 0⟩ := by
  intro k c d
  apply stepStar_trans (r1r1r3_chain k c d)
  rw [show c + k + 1 = 0 + (c + k + 1) from by ring]
  apply stepStar_trans (r3_chain (c + k + 1) 1 0 (d + k))
  ring_nf; finish

theorem full_star_A (k D : ℕ) :
    ⟨0, 0, 0, D + (4 * k + 3), 6 * k + 5⟩ [fm]⊢*
    ⟨6 * k + 7, 0, 0, D + 6 * k + 6, 0⟩ := by
  rw [show D + (4 * k + 3) = (D + 1) + 2 * (2 * k + 1) from by ring,
      show 6 * k + 5 = 2 + 3 * (2 * k + 1) from by ring]
  apply stepStar_trans (r5r2r2_triples (2 * k + 1) 0 (D + 1) 2)
  rw [show 0 + 3 * (2 * k + 1) = 6 * k + 3 from by ring]
  apply stepStar_trans (partial_end_mod2 (b := 6 * k + 3) (d := D))
  rw [show 6 * k + 3 + 2 = 6 * k + 5 from by ring,
      show (6 * k + 5 : ℕ) = 2 * (3 * k + 2) + 1 from by ring]
  apply stepStar_trans (process_odd_b (3 * k + 2) 0 (D + 1))
  ring_nf; finish

theorem full_star_B (k D : ℕ) :
    ⟨0, 0, 0, D + (4 * k + 4), 6 * k + 7⟩ [fm]⊢*
    ⟨6 * k + 11, 0, 0, D + 6 * k + 9, 0⟩ := by
  rw [show D + (4 * k + 4) = D + 2 * (2 * k + 2) from by ring,
      show 6 * k + 7 = 1 + 3 * (2 * k + 2) from by ring]
  apply stepStar_trans (r5r2r2_triples (2 * k + 2) 0 D 1)
  rw [show 0 + 3 * (2 * k + 2) = 6 * k + 6 from by ring]
  apply stepStar_trans (partial_end_mod1 (b := 6 * k + 6) (d := D))
  rw [show 6 * k + 6 + 1 = 6 * k + 7 from by ring,
      show (6 * k + 7 : ℕ) = 2 * (3 * k + 3) + 1 from by ring]
  apply stepStar_trans (process_odd_b (3 * k + 3) 1 (D + 1))
  ring_nf; finish

theorem r4_drain_full (k : ℕ) : ⟨k, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d, k⟩ := by
  rw [show (k : ℕ) = 0 + k from by ring]
  exact r4_drain k (a := 0) (d := d) (e := 0)

theorem trans_A (k : ℕ) (hd : d ≥ 4 * k + 3) :
    ⟨6 * k + 5, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨6 * k + 7, 0, 0, d + 2 * k + 3, 0⟩ := by
  obtain ⟨D, rfl⟩ : ∃ D, d = D + (4 * k + 3) := ⟨d - (4 * k + 3), by omega⟩
  have h1 : ⟨6 * k + 5, 0, 0, D + (4 * k + 3), 0⟩ [fm]⊢*
      ⟨6 * k + 7, 0, 0, D + 6 * k + 6, 0⟩ := by
    apply stepStar_trans (r4_drain_full (6 * k + 5) (d := D + (4 * k + 3)))
    exact full_star_A k D
  rw [show D + 6 * k + 6 = D + (4 * k + 3) + 2 * k + 3 from by ring] at h1
  exact stepStar_stepPlus h1 (by intro h; simp [Q] at h)

theorem trans_B (k : ℕ) (hd : d ≥ 4 * k + 4) :
    ⟨6 * k + 7, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨6 * k + 11, 0, 0, d + 2 * k + 5, 0⟩ := by
  obtain ⟨D, rfl⟩ : ∃ D, d = D + (4 * k + 4) := ⟨d - (4 * k + 4), by omega⟩
  have h1 : ⟨6 * k + 7, 0, 0, D + (4 * k + 4), 0⟩ [fm]⊢*
      ⟨6 * k + 11, 0, 0, D + 6 * k + 9, 0⟩ := by
    apply stepStar_trans (r4_drain_full (6 * k + 7) (d := D + (4 * k + 4)))
    exact full_star_B k D
  rw [show D + 6 * k + 9 = D + (4 * k + 4) + 2 * k + 5 from by ring] at h1
  exact stepStar_stepPlus h1 (by intro h; simp [Q] at h)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ k d, q = ⟨6 * k + 5, 0, 0, d, 0⟩ ∧ d ≥ 4 * k + 3)
                 ∨ (∃ k d, q = ⟨6 * k + 7, 0, 0, d, 0⟩ ∧ d ≥ 4 * k + 4))
  · intro c hP
    rcases hP with ⟨k, d, rfl, hd⟩ | ⟨k, d, rfl, hd⟩
    · exact ⟨⟨6 * k + 7, 0, 0, d + 2 * k + 3, 0⟩,
        Or.inr ⟨k, d + 2 * k + 3, rfl, by omega⟩,
        trans_A k hd⟩
    · exact ⟨⟨6 * k + 11, 0, 0, d + 2 * k + 5, 0⟩,
        Or.inl ⟨k + 1, d + 2 * k + 5, by ring_nf, by omega⟩,
        trans_B k hd⟩
  · exact Or.inl ⟨0, 3, by simp, by omega⟩

end Sz22_2003_unofficial_1091
