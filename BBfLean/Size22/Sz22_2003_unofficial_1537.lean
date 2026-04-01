import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1537: [7/30, 27/35, 55/3, 2/11, 35/2]

Vector representation:
```
-1 -1 -1  1  0
 0  3 -1 -1  0
 0 -1  1  0  1
 1  0  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1537

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem e_to_a : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c e)
    ring_nf; finish

theorem r1r2_round : ⟨a + 3, 3, c + 4, d, 0⟩ [fm]⊢⁺ ⟨a, 3, c, d + 2, 0⟩ := by
  rw [show a + 3 = a + 2 + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show c + 4 = c + 3 + 1 from by ring]
  step fm
  rw [show a + 2 = a + 1 + 1 from by ring,
      show c + 3 = c + 2 + 1 from by ring]
  step fm
  rw [show a + 1 = a + 0 + 1 from by ring,
      show c + 2 = c + 1 + 1 from by ring]
  step fm; step fm; finish

theorem r1r2_loop : ∀ k, ∀ a c d, ⟨a + 3 * k, 3, c + 4 * k, d, 0⟩ [fm]⊢*
    ⟨a, 3, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3) + 3 * k from by ring,
        show c + 4 * (k + 1) = (c + 4) + 4 * k from by ring]
    apply stepStar_trans (ih (a + 3) (c + 4) d)
    exact stepPlus_stepStar r1r2_round

theorem cleanup : ⟨a + 2, 3, 1, d, 0⟩ [fm]⊢* ⟨a, 3, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem inner_round : ⟨a + 1, 3, 0, d, e⟩ [fm]⊢⁺ ⟨a, 3, 0, d, e + 2⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show a + 1 = a + 0 + 1 from by ring]
  step fm; step fm; step fm; finish

theorem inner_drain : ∀ k, ∀ a d e, ⟨a + k, 3, 0, d, e⟩ [fm]⊢*
    ⟨a, 3, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a + 1) d e)
    exact stepPlus_stepStar inner_round

theorem r3r2_round : ⟨0, b + 1, 0, d + 1, e⟩ [fm]⊢⁺ ⟨0, b + 3, 0, d, e + 1⟩ := by
  step fm; step fm; finish

theorem r3r2_drain : ∀ k, ∀ b d e, ⟨0, b + 1, 0, d + k, e⟩ [fm]⊢*
    ⟨0, b + 1 + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (r3r2_round (b := b) (d := d + k) (e := e)))
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b + 2) d (e + 1))
    ring_nf; finish

theorem b_to_ce : ∀ k, ∀ c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

theorem half_step_A (n e : ℕ) :
    ⟨0, 0, 12 * n + 9, 0, e + 9 * n + 9⟩ [fm]⊢⁺
    ⟨0, 0, 12 * n + 15, 0, 2 * e + 18 * n + 21⟩ := by
  -- R4 chain then R5 (gives the plus)
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 12 * n + 9, 0, e + 9 * n + 9⟩ [fm]⊢*
        ⟨e + 9 * n + 9, 0, 12 * n + 9, 0, 0⟩
    rw [show e + 9 * n + 9 = 0 + (e + 9 * n + 9) from by ring]
    exact e_to_a (e + 9 * n + 9) 0 (12 * n + 9) 0
  -- R5+R2
  rw [show e + 9 * n + 9 = (e + 9 * n + 8) + 1 from by ring,
      show 12 * n + 9 = (12 * n + 8) + 1 from by ring]
  step fm; step fm
  show ⟨e + 9 * n + 8, 3, 12 * n + 8 + 1, 0, 0⟩ [fm]⊢*
       ⟨0, 0, 12 * n + 15, 0, 2 * e + 18 * n + 21⟩
  rw [show 12 * n + 8 + 1 = 12 * n + 9 from by ring]
  -- R1×3+R2 loop: 3n+2 iterations
  apply stepStar_trans
  · show ⟨e + 9 * n + 8, 3, 12 * n + 9, 0, 0⟩ [fm]⊢* ⟨e + 2, 3, 1, 6 * n + 4, 0⟩
    rw [show e + 9 * n + 8 = (e + 2) + 3 * (3 * n + 2) from by ring,
        show 12 * n + 9 = 1 + 4 * (3 * n + 2) from by ring]
    have := r1r2_loop (3 * n + 2) (e + 2) 1 0
    rw [show 0 + 2 * (3 * n + 2) = 6 * n + 4 from by ring] at this
    exact this
  -- Cleanup
  apply stepStar_trans
  · exact cleanup (a := e) (d := 6 * n + 4)
  -- Inner drain
  apply stepStar_trans
  · have h := inner_drain e 0 (6 * n + 6) 0
    rw [show 0 + e = e from by ring, show 0 + 2 * e = 2 * e from by ring] at h
    exact h
  -- R3+R2: first pair
  show ⟨0, 3, 0, 6 * n + 6, 2 * e⟩ [fm]⊢* _
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 6 * n + 6 = (6 * n + 5) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r3r2_round (b := 2) (d := 6 * n + 5) (e := 2 * e)))
  -- Now at (0, 5, 0, 6n+5, 2e+1)
  -- R3+R2 drain: 6n+5 pairs
  apply stepStar_trans
  · show ⟨0, 5, 0, 6 * n + 5, 2 * e + 1⟩ [fm]⊢*
        ⟨0, 12 * n + 15, 0, 0, 2 * e + 6 * n + 6⟩
    rw [show (5 : ℕ) = 4 + 1 from by ring,
        show 6 * n + 5 = 0 + (6 * n + 5) from by ring]
    have := r3r2_drain (6 * n + 5) 4 0 (2 * e + 1)
    rw [show 4 + 1 + 2 * (6 * n + 5) = 12 * n + 15 from by ring,
        show 2 * e + 1 + (6 * n + 5) = 2 * e + 6 * n + 6 from by ring] at this
    exact this
  -- R3 chain
  show ⟨0, 12 * n + 15, 0, 0, 2 * e + 6 * n + 6⟩ [fm]⊢*
       ⟨0, 0, 12 * n + 15, 0, 2 * e + 18 * n + 21⟩
  have := b_to_ce (12 * n + 15) 0 (2 * e + 6 * n + 6)
  rw [show 0 + (12 * n + 15) = 12 * n + 15 from by ring,
      show 2 * e + 6 * n + 6 + (12 * n + 15) = 2 * e + 18 * n + 21 from by ring] at this
  exact this

theorem half_step_B (n e : ℕ) :
    ⟨0, 0, 12 * n + 15, 0, e + 9 * n + 14⟩ [fm]⊢⁺
    ⟨0, 0, 12 * n + 21, 0, 2 * e + 18 * n + 30⟩ := by
  -- R4 chain
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 12 * n + 15, 0, e + 9 * n + 14⟩ [fm]⊢*
        ⟨e + 9 * n + 14, 0, 12 * n + 15, 0, 0⟩
    rw [show e + 9 * n + 14 = 0 + (e + 9 * n + 14) from by ring]
    exact e_to_a (e + 9 * n + 14) 0 (12 * n + 15) 0
  -- R5+R2
  rw [show e + 9 * n + 14 = (e + 9 * n + 13) + 1 from by ring,
      show 12 * n + 15 = (12 * n + 14) + 1 from by ring]
  step fm; step fm
  show ⟨e + 9 * n + 13, 3, 12 * n + 14 + 1, 0, 0⟩ [fm]⊢* _
  rw [show 12 * n + 14 + 1 = 12 * n + 15 from by ring]
  -- R1×3+R2 loop: 3n+3 iterations
  apply stepStar_trans
  · show ⟨e + 9 * n + 13, 3, 12 * n + 15, 0, 0⟩ [fm]⊢* ⟨e + 4, 3, 3, 6 * n + 6, 0⟩
    rw [show e + 9 * n + 13 = (e + 4) + 3 * (3 * n + 3) from by ring,
        show 12 * n + 15 = 3 + 4 * (3 * n + 3) from by ring]
    have := r1r2_loop (3 * n + 3) (e + 4) 3 0
    rw [show 0 + 2 * (3 * n + 3) = 6 * n + 6 from by ring] at this
    exact this
  -- R1×3: (e+4, 3, 3, 6n+6, 0) → (e+1, 0, 0, 6n+9, 0)
  rw [show e + 4 = (e + 3) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show e + (2 + 1) = (e + 2) + 1 from by ring]
  step fm
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm
  -- R5: (e+1, 0, 0, 6n+9, 0) → (e, 0, 1, 6n+10, 0)
  show ⟨(e + 0) + 1, 0, 0, 6 * n + 6 + 1 + 1 + 1, 0⟩ [fm]⊢* _
  step fm
  -- R2: (e, 0, 1, 6n+10, 0) → (e, 3, 0, 6n+9, 0)
  show ⟨e + 0, 0, 0 + 1, (6 * n + 6 + 1 + 1 + 1) + 1, 0⟩ [fm]⊢* _
  rw [show (6 * n + 6 + 1 + 1 + 1) + 1 = (6 * n + 9) + 1 from by ring]
  step fm
  show ⟨e + 0, 3, 0, 6 * n + 9, 0⟩ [fm]⊢* _
  rw [show e + 0 = e from by ring]
  -- Inner drain
  apply stepStar_trans
  · have h := inner_drain e 0 (6 * n + 9) 0
    rw [show 0 + e = e from by ring, show 0 + 2 * e = 2 * e from by ring] at h
    exact h
  -- R3+R2 first pair
  show ⟨0, 3, 0, 6 * n + 9, 2 * e⟩ [fm]⊢* _
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 6 * n + 9 = (6 * n + 8) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r3r2_round (b := 2) (d := 6 * n + 8) (e := 2 * e)))
  -- R3+R2 drain: 6n+8 pairs
  apply stepStar_trans
  · show ⟨0, 5, 0, 6 * n + 8, 2 * e + 1⟩ [fm]⊢*
        ⟨0, 12 * n + 21, 0, 0, 2 * e + 6 * n + 9⟩
    rw [show (5 : ℕ) = 4 + 1 from by ring,
        show 6 * n + 8 = 0 + (6 * n + 8) from by ring]
    have := r3r2_drain (6 * n + 8) 4 0 (2 * e + 1)
    rw [show 4 + 1 + 2 * (6 * n + 8) = 12 * n + 21 from by ring,
        show 2 * e + 1 + (6 * n + 8) = 2 * e + 6 * n + 9 from by ring] at this
    exact this
  -- R3 chain
  show ⟨0, 12 * n + 21, 0, 0, 2 * e + 6 * n + 9⟩ [fm]⊢*
       ⟨0, 0, 12 * n + 21, 0, 2 * e + 18 * n + 30⟩
  have := b_to_ce (12 * n + 21) 0 (2 * e + 6 * n + 9)
  rw [show 0 + (12 * n + 21) = 12 * n + 21 from by ring,
      show 2 * e + 6 * n + 9 + (12 * n + 21) = 2 * e + 18 * n + 30 from by ring] at this
  exact this

theorem main_trans (n e : ℕ) :
    ⟨0, 0, 12 * n + 9, 0, e + 9 * n + 9⟩ [fm]⊢⁺
    ⟨0, 0, 12 * (n + 1) + 9, 0, (4 * e + 27 * n + 26) + 9 * (n + 1) + 9⟩ := by
  apply stepPlus_trans (half_step_A n e)
  rw [show 2 * e + 18 * n + 21 = (2 * e + 9 * n + 7) + 9 * n + 14 from by ring,
      show 12 * (n + 1) + 9 = 12 * n + 21 from by ring,
      show (4 * e + 27 * n + 26) + 9 * (n + 1) + 9 =
        2 * (2 * e + 9 * n + 7) + 18 * n + 30 from by ring]
  exact half_step_B n (2 * e + 9 * n + 7)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 0, 15⟩)
  · execute fm 57
  rw [show (15 : ℕ) = 6 + 9 * 0 + 9 from by ring,
      show (9 : ℕ) = 12 * 0 + 9 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 12 * n + 9, 0, e + 9 * n + 9⟩) ⟨0, 6⟩
  intro ⟨n, e⟩; exact ⟨⟨n + 1, 4 * e + 27 * n + 26⟩, main_trans n e⟩

end Sz22_2003_unofficial_1537
