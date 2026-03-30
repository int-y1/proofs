import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #776: [35/6, 55/2, 4/77, 3/25, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 2  0  0 -1 -1
 0  1 -2  0  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_776

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k b c e, ⟨0, b, c + 2 * k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  show ⟨0, b, (c + 2 * k) + 2, 0, e⟩ [fm]⊢* _; step fm
  apply stepStar_trans (ih (b + 1) c e); ring_nf; finish

theorem r2r2r3_chain : ∀ k c d e, ⟨2, 0, c, d + k, e⟩ [fm]⊢* ⟨2, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  show ⟨(1 : ℕ) + 1, 0, c, (d + k) + 1, e⟩ [fm]⊢* _; step fm
  show ⟨(0 : ℕ) + 1, 0, c + 1, (d + k) + 1, e + 1⟩ [fm]⊢* _; step fm
  rw [show (e : ℕ) + 1 + 1 = (e + 1) + 1 from by ring]; step fm
  apply stepStar_trans (ih (c + 2) d (e + 1)); ring_nf; finish

theorem r1r2r3 : ∀ c d e, ⟨2, 1, c, d, e + 1⟩ [fm]⊢* ⟨2, 0, c + 2, d, e + 1⟩ := by
  intro c d e
  show ⟨(1 : ℕ) + 1, (0 : ℕ) + 1, c, d, e + 1⟩ [fm]⊢* _; step fm
  show ⟨(0 : ℕ) + 1, 0, c + 1, d + 1, e + 1⟩ [fm]⊢* _; step fm
  rw [show (e : ℕ) + 1 + 1 = (e + 1) + 1 from by ring]; step fm; ring_nf; finish

theorem odd_drain : ∀ k c d e, ⟨2, 2 * k + 1, c, d, e + k + 1⟩ [fm]⊢* ⟨2, 0, c + 2 * k + 2, d + k, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exact r1r2r3 c d e
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
      show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
  show ⟨(1 : ℕ) + 1, (2 * k + 1) + 1 + 1, c, d, (e + k + 1) + 1⟩ [fm]⊢* _; step fm
  show ⟨(0 : ℕ) + 1, (2 * k + 1) + 1, c + 1, d + 1, (e + k + 1) + 1⟩ [fm]⊢* _; step fm
  rw [show (d : ℕ) + 1 + 1 = (d + 1) + 1 from by ring]; step fm
  apply stepStar_trans (ih (c + 2) (d + 1) e); ring_nf; finish

theorem r1r1r3_chain : ∀ k c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + 2 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring, show e + (k + 1) = (e + k) + 1 from by ring]
  show ⟨(1 : ℕ) + 1, (2 * k) + 1 + 1, c, d, (e + k) + 1⟩ [fm]⊢* _; step fm
  show ⟨(0 : ℕ) + 1, (2 * k) + 1, c + 1, d + 1, (e + k) + 1⟩ [fm]⊢* _; step fm
  rw [show (d : ℕ) + 1 + 1 = (d + 1) + 1 from by ring]; step fm
  apply stepStar_trans (ih (c + 2) (d + 1) e); ring_nf; finish

theorem r5r1r3_c0 : ∀ b e, ⟨0, b + 1, 0, 0, e + 2⟩ [fm]⊢* ⟨2, b, 1, 1, e⟩ := by
  intro b e; rw [show (e : ℕ) + 2 = (e + 1) + 1 from by ring]; step fm
  show ⟨(0 : ℕ) + 1, b + 1, 0, (0 : ℕ) + 1, e + 1⟩ [fm]⊢* _; step fm; step fm; finish

theorem r5r1r3_c1 : ∀ b e, ⟨0, b + 1, 1, 0, e + 2⟩ [fm]⊢* ⟨2, b, 2, 1, e⟩ := by
  intro b e; rw [show (e : ℕ) + 2 = (e + 1) + 1 from by ring]; step fm
  show ⟨(0 : ℕ) + 1, b + 1, 1, (0 : ℕ) + 1, e + 1⟩ [fm]⊢* _; step fm; step fm; finish

theorem phase3 : ∀ c d e, ⟨2, 0, c, d, e⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * d + 2, 0, e + d + 2⟩ := by
  intro c d e
  apply stepStar_stepPlus_stepPlus
  · rw [show (d : ℕ) = 0 + d from by ring]; exact r2r2r3_chain d c 0 e
  show ⟨(1 : ℕ) + 1, 0, c + 2 * d, 0, e + d⟩ [fm]⊢⁺ _; step fm; step fm
  rw [show (c + 2 * d) + 1 + 1 = c + 2 * d + 2 from by ring,
      show (e + d) + 1 + 1 = e + d + 2 from by ring]; finish

theorem case_4j1 : ∀ j, ⟨0, 0, 12 * j + 4, 0, 4 * j + 2⟩ [fm]⊢⁺ ⟨0, 0, 12 * j + 7, 0, 4 * j + 3⟩ := by
  intro j; rcases j with _ | j
  · execute fm 13
  · apply stepStar_stepPlus_stepPlus
    · rw [show 12 * (j + 1) + 4 = 0 + 2 * (6 * j + 8) from by ring]
      exact r4_chain (6 * j + 8) 0 0 (4 * (j + 1) + 2)
    show ⟨0, 0 + (6 * j + 8), 0, 0, 4 * (j + 1) + 2⟩ [fm]⊢⁺ _
    rw [show 0 + (6 * j + 8) = (6 * j + 7) + 1 from by ring,
        show 4 * (j + 1) + 2 = (4 * j + 4) + 2 from by ring]
    apply stepStar_stepPlus_stepPlus (r5r1r3_c0 (6 * j + 7) (4 * j + 4))
    show ⟨2, 6 * j + 7, 1, 1, 4 * j + 4⟩ [fm]⊢⁺ _
    rw [show (6 * j + 7 : ℕ) = 2 * (3 * j + 3) + 1 from by ring,
        show (4 * j + 4 : ℕ) = j + (3 * j + 3) + 1 from by ring]
    apply stepStar_stepPlus_stepPlus (odd_drain (3 * j + 3) 1 1 j)
    show ⟨2, 0, 1 + 2 * (3 * j + 3) + 2, 1 + (3 * j + 3), j + 1⟩ [fm]⊢⁺ _
    rw [show 1 + 2 * (3 * j + 3) + 2 = 6 * j + 9 from by ring,
        show 1 + (3 * j + 3) = 3 * j + 4 from by ring,
        show 12 * (j + 1) + 7 = (6 * j + 9) + 2 * (3 * j + 4) + 2 from by ring,
        show 4 * (j + 1) + 3 = (j + 1) + (3 * j + 4) + 2 from by ring]
    exact phase3 (6 * j + 9) (3 * j + 4) (j + 1)

theorem case_4j2 : ∀ j, ⟨0, 0, 12 * j + 7, 0, 4 * j + 3⟩ [fm]⊢⁺ ⟨0, 0, 12 * j + 10, 0, 4 * j + 4⟩ := by
  intro j
  apply stepStar_stepPlus_stepPlus
  · rw [show 12 * j + 7 = 1 + 2 * (6 * j + 3) from by ring]
    exact r4_chain (6 * j + 3) 0 1 (4 * j + 3)
  show ⟨0, 0 + (6 * j + 3), 1, 0, 4 * j + 3⟩ [fm]⊢⁺ _
  rw [show 0 + (6 * j + 3) = (6 * j + 2) + 1 from by ring,
      show 4 * j + 3 = (4 * j + 1) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r3_c1 (6 * j + 2) (4 * j + 1))
  show ⟨2, 6 * j + 2, 2, 1, 4 * j + 1⟩ [fm]⊢⁺ _
  rw [show (6 * j + 2 : ℕ) = 2 * (3 * j + 1) from by ring,
      show (4 * j + 1 : ℕ) = j + (3 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r1r3_chain (3 * j + 1) 2 1 j)
  show ⟨2, 0, 2 + 2 * (3 * j + 1), 1 + (3 * j + 1), j⟩ [fm]⊢⁺ _
  rw [show 2 + 2 * (3 * j + 1) = 6 * j + 4 from by ring,
      show 1 + (3 * j + 1) = 3 * j + 2 from by ring,
      show 12 * j + 10 = (6 * j + 4) + 2 * (3 * j + 2) + 2 from by ring,
      show 4 * j + 4 = j + (3 * j + 2) + 2 from by ring]
  exact phase3 (6 * j + 4) (3 * j + 2) j

theorem case_4j3 : ∀ j, ⟨0, 0, 12 * j + 10, 0, 4 * j + 4⟩ [fm]⊢⁺ ⟨0, 0, 12 * j + 13, 0, 4 * j + 5⟩ := by
  intro j
  apply stepStar_stepPlus_stepPlus
  · rw [show 12 * j + 10 = 0 + 2 * (6 * j + 5) from by ring]
    exact r4_chain (6 * j + 5) 0 0 (4 * j + 4)
  show ⟨0, 0 + (6 * j + 5), 0, 0, 4 * j + 4⟩ [fm]⊢⁺ _
  rw [show 0 + (6 * j + 5) = (6 * j + 4) + 1 from by ring,
      show 4 * j + 4 = (4 * j + 2) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r3_c0 (6 * j + 4) (4 * j + 2))
  show ⟨2, 6 * j + 4, 1, 1, 4 * j + 2⟩ [fm]⊢⁺ _
  rw [show (6 * j + 4 : ℕ) = 2 * (3 * j + 2) from by ring,
      show (4 * j + 2 : ℕ) = j + (3 * j + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r1r3_chain (3 * j + 2) 1 1 j)
  show ⟨2, 0, 1 + 2 * (3 * j + 2), 1 + (3 * j + 2), j⟩ [fm]⊢⁺ _
  rw [show 1 + 2 * (3 * j + 2) = 6 * j + 5 from by ring,
      show 1 + (3 * j + 2) = 3 * j + 3 from by ring,
      show 12 * j + 13 = (6 * j + 5) + 2 * (3 * j + 3) + 2 from by ring,
      show 4 * j + 5 = j + (3 * j + 3) + 2 from by ring]
  exact phase3 (6 * j + 5) (3 * j + 3) j

theorem case_4j_succ : ∀ j, ⟨0, 0, 12 * j + 13, 0, 4 * j + 5⟩ [fm]⊢⁺ ⟨0, 0, 12 * j + 16, 0, 4 * j + 6⟩ := by
  intro j
  apply stepStar_stepPlus_stepPlus
  · rw [show 12 * j + 13 = 1 + 2 * (6 * j + 6) from by ring]
    exact r4_chain (6 * j + 6) 0 1 (4 * j + 5)
  show ⟨0, 0 + (6 * j + 6), 1, 0, 4 * j + 5⟩ [fm]⊢⁺ _
  rw [show 0 + (6 * j + 6) = (6 * j + 5) + 1 from by ring,
      show 4 * j + 5 = (4 * j + 3) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r3_c1 (6 * j + 5) (4 * j + 3))
  show ⟨2, 6 * j + 5, 2, 1, 4 * j + 3⟩ [fm]⊢⁺ _
  rw [show (6 * j + 5 : ℕ) = 2 * (3 * j + 2) + 1 from by ring,
      show (4 * j + 3 : ℕ) = j + (3 * j + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (odd_drain (3 * j + 2) 2 1 j)
  show ⟨2, 0, 2 + 2 * (3 * j + 2) + 2, 1 + (3 * j + 2), j + 1⟩ [fm]⊢⁺ _
  rw [show 2 + 2 * (3 * j + 2) + 2 = 6 * j + 8 from by ring,
      show 1 + (3 * j + 2) = 3 * j + 3 from by ring,
      show 12 * j + 16 = (6 * j + 8) + 2 * (3 * j + 3) + 2 from by ring,
      show 4 * j + 6 = (j + 1) + (3 * j + 3) + 2 from by ring]
  exact phase3 (6 * j + 8) (3 * j + 3) (j + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 12 * n + 4, 0, 4 * n + 2⟩) 0
  intro n; exists n + 1
  rw [show 12 * (n + 1) + 4 = 12 * n + 16 from by ring,
      show 4 * (n + 1) + 2 = 4 * n + 6 from by ring]
  apply stepPlus_trans (case_4j1 n)
  apply stepPlus_trans (case_4j2 n)
  apply stepPlus_trans (case_4j3 n)
  exact case_4j_succ n
