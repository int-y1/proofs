import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #436: [27/35, 25/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  2  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_436

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a+k, (0 : ℕ), 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d; rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; apply stepStar_trans (ih _ _); ring_nf; finish

theorem d_to_e : ∀ k a e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e; rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; apply stepStar_trans (ih _ _); ring_nf; finish

theorem r3r4_chain : ∀ E a, ⟨a, E, 0, 0, 0⟩ [fm]⊢* ⟨a+E, (0 : ℕ), 0, 0, E⟩ := by
  intro E a
  apply stepStar_trans (c₂ := ⟨a + E, 0, 0, E, 0⟩)
  · have h := r3_chain E a 0
    rw [show (0 : ℕ) + E = E from by ring] at h; exact h
  have h := d_to_e E (a + E) 0
  rw [show (0 : ℕ) + E = E from by ring] at h; exact h

theorem first_block : ∀ A E, ⟨A+1, 0, 0, 0, E+4⟩ [fm]⊢* ⟨A, (0 : ℕ), 7, 0, E⟩ := by
  intro A E; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem block : ∀ A C E, ⟨A+1, 0, C+1, 0, E+4⟩ [fm]⊢* ⟨A, (0 : ℕ), C+8, 0, E⟩ := by
  intro A C E; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem blocks : ∀ k A C E,
    ⟨A+k, 0, C+1, 0, E+4*k⟩ [fm]⊢* ⟨A, (0 : ℕ), C+1+7*k, 0, E⟩ := by
  intro k; induction k with
  | zero => intro A C E; simp; exists 0
  | succ k ih =>
    intro A C E
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show E + 4 * (k + 1) = (E + 4 * k) + 4 from by ring]
    apply stepStar_trans (block (A + k) C (E + 4 * k))
    apply stepStar_trans (ih A (C + 7) E)
    rw [show C + 7 + 1 + 7 * k = C + 1 + 7 * (k + 1) from by ring]; finish

theorem r3r1_chain : ∀ k a b,
    ⟨a, b+1, k, 0, 0⟩ [fm]⊢* ⟨a+k, b+1+2*k, (0 : ℕ), 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b; rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem tail_0 : ∀ A C,
    ⟨A+1, 0, C+1, 0, 0⟩ [fm]⊢* ⟨A+C, 2*C+4, (0 : ℕ), 0, 0⟩ := by
  intro A C; step fm; step fm; rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r3r1_chain C A 3); ring_nf; finish

theorem tail_1 : ∀ A C,
    ⟨A+1, 0, C+1, 0, 1⟩ [fm]⊢* ⟨A+C+2, 2*C+7, (0 : ℕ), 0, 0⟩ := by
  intro A C; step fm; step fm; step fm; rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r1_chain (C + 2) A 2); ring_nf; finish

theorem tail_2 : ∀ A C,
    ⟨A+1, 0, C+1, 0, 2⟩ [fm]⊢* ⟨A+C+4, 2*C+10, (0 : ℕ), 0, 0⟩ := by
  intro A C; step fm; step fm; step fm; step fm; rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r1_chain (C + 4) A 1); ring_nf; finish

theorem tail_3 : ∀ A C,
    ⟨A+1, 0, C+1, 0, 3⟩ [fm]⊢* ⟨A+C+6, 2*C+13, (0 : ℕ), 0, 0⟩ := by
  intro A C; step fm; step fm; step fm; step fm; step fm; rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r1_chain (C + 6) A 0); ring_nf; finish

-- Inner computation: (A, 0, 0, 0, E) ⊢* result, by cases on E mod 4.
-- For the main_trans, we compose: R3 chain, d_to_e, first_block, blocks, tail.

theorem main_trans_0 (j a : ℕ) :
    ⟨a, 4*j+5, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+10*j+11, 14*j+19, (0 : ℕ), 0, 0⟩ := by
  -- First R3 step for stepPlus, then chain the rest as stepStar
  apply step_stepStar_stepPlus (c₂ := ⟨a+1, 4*j+4, 0, 1, 0⟩)
  · rw [show 4 * j + 5 = (4 * j + 4) + 1 from by ring]; simp [fm]
  -- Rest of R3 chain
  apply stepStar_trans (c₂ := ⟨a+4*j+5, 0, 0, 4*j+5, 0⟩)
  · have h := r3_chain (4 * j + 4) (a + 1) 1
    rw [show a + 1 + (4 * j + 4) = a + 4 * j + 5 from by ring,
        show 1 + (4 * j + 4) = 4 * j + 5 from by ring] at h; exact h
  -- d_to_e
  apply stepStar_trans (c₂ := ⟨a+4*j+5, 0, 0, 0, 4*j+5⟩)
  · have h := d_to_e (4 * j + 5) (a + 4 * j + 5) 0
    simp only [Nat.zero_add] at h; exact h
  -- first_block
  apply stepStar_trans (c₂ := ⟨a+4*j+4, 0, 7, 0, 4*j+1⟩)
  · rw [show a + 4 * j + 5 = (a + 4 * j + 4) + 1 from by ring,
        show 4 * j + 5 = (4 * j + 1) + 4 from by ring]; exact first_block _ _
  -- j blocks
  apply stepStar_trans (c₂ := ⟨a+3*j+4, 0, 7+7*j, 0, 1⟩)
  · rw [show a + 4 * j + 4 = (a + 3 * j + 4) + j from by ring,
        show (7 : ℕ) = 6 + 1 from rfl, show 4 * j + 1 = 1 + 4 * j from by ring]
    have h := blocks j (a + 3 * j + 4) 6 1
    rw [show 6 + 1 + 7 * j = 7 + 7 * j from by ring] at h; exact h
  -- tail
  rw [show a + 3 * j + 4 = (a + 3 * j + 3) + 1 from by ring,
      show 7 + 7 * j = (6 + 7 * j) + 1 from by ring]
  apply stepStar_trans (tail_1 (a + 3 * j + 3) (6 + 7 * j)); ring_nf; finish

theorem main_trans_1 (j a : ℕ) :
    ⟨a, 4*j+6, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+10*j+14, 14*j+22, (0 : ℕ), 0, 0⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a+1, 4*j+5, 0, 1, 0⟩)
  · rw [show 4 * j + 6 = (4 * j + 5) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+4*j+6, 0, 0, 4*j+6, 0⟩)
  · have h := r3_chain (4 * j + 5) (a + 1) 1
    rw [show a + 1 + (4 * j + 5) = a + 4 * j + 6 from by ring,
        show 1 + (4 * j + 5) = 4 * j + 6 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*j+6, 0, 0, 0, 4*j+6⟩)
  · have h := d_to_e (4 * j + 6) (a + 4 * j + 6) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*j+5, 0, 7, 0, 4*j+2⟩)
  · rw [show a + 4 * j + 6 = (a + 4 * j + 5) + 1 from by ring,
        show 4 * j + 6 = (4 * j + 2) + 4 from by ring]; exact first_block _ _
  apply stepStar_trans (c₂ := ⟨a+3*j+5, 0, 7+7*j, 0, 2⟩)
  · rw [show a + 4 * j + 5 = (a + 3 * j + 5) + j from by ring,
        show (7 : ℕ) = 6 + 1 from rfl, show 4 * j + 2 = 2 + 4 * j from by ring]
    have h := blocks j (a + 3 * j + 5) 6 2
    rw [show 6 + 1 + 7 * j = 7 + 7 * j from by ring] at h; exact h
  rw [show a + 3 * j + 5 = (a + 3 * j + 4) + 1 from by ring,
      show 7 + 7 * j = (6 + 7 * j) + 1 from by ring]
  apply stepStar_trans (tail_2 (a + 3 * j + 4) (6 + 7 * j)); ring_nf; finish

theorem main_trans_2 (j a : ℕ) :
    ⟨a, 4*j+7, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+10*j+17, 14*j+25, (0 : ℕ), 0, 0⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a+1, 4*j+6, 0, 1, 0⟩)
  · rw [show 4 * j + 7 = (4 * j + 6) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+4*j+7, 0, 0, 4*j+7, 0⟩)
  · have h := r3_chain (4 * j + 6) (a + 1) 1
    rw [show a + 1 + (4 * j + 6) = a + 4 * j + 7 from by ring,
        show 1 + (4 * j + 6) = 4 * j + 7 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*j+7, 0, 0, 0, 4*j+7⟩)
  · have h := d_to_e (4 * j + 7) (a + 4 * j + 7) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*j+6, 0, 7, 0, 4*j+3⟩)
  · rw [show a + 4 * j + 7 = (a + 4 * j + 6) + 1 from by ring,
        show 4 * j + 7 = (4 * j + 3) + 4 from by ring]; exact first_block _ _
  apply stepStar_trans (c₂ := ⟨a+3*j+6, 0, 7+7*j, 0, 3⟩)
  · rw [show a + 4 * j + 6 = (a + 3 * j + 6) + j from by ring,
        show (7 : ℕ) = 6 + 1 from rfl, show 4 * j + 3 = 3 + 4 * j from by ring]
    have h := blocks j (a + 3 * j + 6) 6 3
    rw [show 6 + 1 + 7 * j = 7 + 7 * j from by ring] at h; exact h
  rw [show a + 3 * j + 6 = (a + 3 * j + 5) + 1 from by ring,
      show 7 + 7 * j = (6 + 7 * j) + 1 from by ring]
  apply stepStar_trans (tail_3 (a + 3 * j + 5) (6 + 7 * j)); ring_nf; finish

theorem main_trans_3 (j a : ℕ) :
    ⟨a, 4*j+8, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+10*j+18, 14*j+30, (0 : ℕ), 0, 0⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a+1, 4*j+7, 0, 1, 0⟩)
  · rw [show 4 * j + 8 = (4 * j + 7) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+4*j+8, 0, 0, 4*j+8, 0⟩)
  · have h := r3_chain (4 * j + 7) (a + 1) 1
    rw [show a + 1 + (4 * j + 7) = a + 4 * j + 8 from by ring,
        show 1 + (4 * j + 7) = 4 * j + 8 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*j+8, 0, 0, 0, 4*j+8⟩)
  · have h := d_to_e (4 * j + 8) (a + 4 * j + 8) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*j+7, 0, 7, 0, 4*j+4⟩)
  · rw [show a + 4 * j + 8 = (a + 4 * j + 7) + 1 from by ring,
        show 4 * j + 8 = (4 * j + 4) + 4 from by ring]; exact first_block _ _
  apply stepStar_trans (c₂ := ⟨a+3*j+6, 0, 7+7*(j+1), 0, 0⟩)
  · rw [show a + 4 * j + 7 = (a + 3 * j + 6) + (j + 1) from by ring,
        show (7 : ℕ) = 6 + 1 from rfl, show 4 * j + 4 = 0 + 4 * (j + 1) from by ring]
    have h := blocks (j + 1) (a + 3 * j + 6) 6 0
    rw [show 6 + 1 + 7 * (j + 1) = 7 + 7 * (j + 1) from by ring] at h; exact h
  rw [show a + 3 * j + 6 = (a + 3 * j + 5) + 1 from by ring,
      show 7 + 7 * (j + 1) = (6 + 7 * (j + 1)) + 1 from by ring]
  apply stepStar_trans (tail_0 (a + 3 * j + 5) (6 + 7 * (j + 1))); ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 8, 0, 0, 0⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b + 5, 0, 0, 0⟩)
  · intro c ⟨a, b, hc⟩
    subst hc
    rcases Nat.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨⟨a + 10 * j + 11, 14 * j + 19, 0, 0, 0⟩,
                ⟨a + 10 * j + 11, 14 * j + 14, by ring_nf⟩, ?_⟩
        have := main_trans_0 j a
        rw [show b = 4 * j from by omega]; exact this
      · refine ⟨⟨a + 10 * j + 17, 14 * j + 25, 0, 0, 0⟩,
                ⟨a + 10 * j + 17, 14 * j + 20, by ring_nf⟩, ?_⟩
        have := main_trans_2 j a
        rw [show b = 4 * j + 2 from by omega]; exact this
    · rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨⟨a + 10 * j + 14, 14 * j + 22, 0, 0, 0⟩,
                ⟨a + 10 * j + 14, 14 * j + 17, by ring_nf⟩, ?_⟩
        have := main_trans_1 j a
        rw [show b = 4 * j + 1 from by omega]; exact this
      · refine ⟨⟨a + 10 * j + 18, 14 * j + 30, 0, 0, 0⟩,
                ⟨a + 10 * j + 18, 14 * j + 25, by ring_nf⟩, ?_⟩
        have := main_trans_3 j a
        rw [show b = 4 * j + 3 from by omega]; exact this
  · exact ⟨3, 3, rfl⟩

end Sz22_2003_unofficial_436
