import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1244: [5/6, 77/2, 44/35, 3/11, 20/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  1
 0  1  0  0 -1
 2 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1244

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem e_to_b' : ∀ k b c e, ⟨(0 : ℕ), b, c, (0 : ℕ), e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, c, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro b c e; exists 0
  · intro b c e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

theorem r3r1r1_round : ⟨(0 : ℕ), b + 2, c + 1, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2, d, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem r3r1r1_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; simp; exists 0
  · intro b c d e
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl,
        show b + 2 = b + 2 from rfl]
    apply stepStar_trans r3r1r1_round
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

theorem r5r1r1_round : ⟨(0 : ℕ), b + 3, c, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3, (0 : ℕ), (0 : ℕ)⟩ := by
  step fm; step fm; step fm; finish

theorem r5r1r1_chain : ∀ k, ∀ b c,
    ⟨(0 : ℕ), b + 3 * k, c, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + 3 * k, (0 : ℕ), (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro b c; simp; exists 0
  · intro b c
    rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (b + 3) c)
    apply stepStar_trans r5r1r1_round
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]
    finish

theorem r3r2r2_round : ⟨(0 : ℕ), 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 2, e + 3⟩ := by
  step fm; step fm; step fm; finish

theorem r3r2r2_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, c, d + k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show d + k + 1 = (d + k) + 1 from by ring,
        show c + 1 = c + 1 from rfl]
    apply stepStar_trans r3r2r2_round
    rw [show d + k + 2 = d + (k + 1) + 1 from by ring,
        show e + 3 * k + 3 = e + 3 * (k + 1) from by ring]
    finish

theorem main_transition (m j : ℕ) :
    ⟨(0 : ℕ), 0, 0, 3 * j + 1, 3 * m + 6 * j + 8⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 3 * m + 6 * j + 10, 9 * m + 18 * j + 26⟩ := by
  -- Phase 1: R4 chain: (0,0,0,d,e) -> (0,e,0,d,0)
  rw [show 3 * m + 6 * j + 8 = 0 + (3 * m + 6 * j + 8) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (3 * m + 6 * j + 8) 0 (3 * j + 1) 0)
  rw [show (0 : ℕ) + (3 * m + 6 * j + 8) = 3 * m + 6 * j + 8 from by ring]
  -- State: (0, 3m+6j+8, 0, 3j+1, 0)
  -- Phase 2a: R5, R1, R1
  rw [show 3 * m + 6 * j + 8 = (3 * m + 6 * j + 7) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, (3 * m + 6 * j + 7) + 1, 0, 3 * j + 1, 0⟩ : Q) [fm]⊢
      ⟨2, 3 * m + 6 * j + 7, 1, 3 * j + 1, 0⟩)
  rw [show 3 * m + 6 * j + 7 = (3 * m + 6 * j + 6) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, (3 * m + 6 * j + 6) + 1, 1, 3 * j + 1, 0⟩ : Q) [fm]⊢
      ⟨1, 3 * m + 6 * j + 6, 2, 3 * j + 1, 0⟩))
  rw [show 3 * m + 6 * j + 6 = (3 * m + 6 * j + 5) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, (3 * m + 6 * j + 5) + 1, 2, 3 * j + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 3 * m + 6 * j + 5, 3, 3 * j + 1, 0⟩))
  -- State: (0, 3m+6j+5, 3, 3j+1, 0)
  -- Phase 2b: R3,R1,R1 chain x (3j+1) rounds
  have h2b := r3r1r1_chain (3 * j + 1) (3 * m + 3) 2 0 0
  rw [show 3 * m + 3 + 2 * (3 * j + 1) = 3 * m + 6 * j + 5 from by ring,
      show 2 + (3 * j + 1) + 1 = 3 * j + 4 from by ring,
      show (0 : ℕ) + (3 * j + 1) = 3 * j + 1 from by ring] at h2b
  apply stepStar_trans h2b
  -- State: (0, 3m+3, 3j+4, 0, 3j+1)
  -- Phase 3a: R4 chain, move e_reg (3j+1) to b
  rw [show 3 * j + 1 = 0 + (3 * j + 1) from by ring]
  apply stepStar_trans (e_to_b' (3 * j + 1) (3 * m + 3) (3 * j + 4) 0)
  rw [show 3 * m + 3 + (3 * j + 1) = 1 + 3 * (m + j + 1) from by ring]
  -- State: (0, 1+3*(m+j+1), 3j+4, 0, 0)
  -- Phase 3b: R5,R1,R1 chain x (m+j+1) rounds
  apply stepStar_trans (r5r1r1_chain (m + j + 1) 1 (3 * j + 4))
  rw [show 3 * j + 4 + 3 * (m + j + 1) = 3 * m + 6 * j + 7 from by ring]
  -- State: (0, 1, 3m+6j+7, 0, 0)
  -- Phase 3c: R5
  step fm
  -- State: (2, 0, 3m+6j+8, 0, 0)
  -- R2, R2
  step fm; step fm
  -- State: (0, 0, 3m+6j+8, 2, 2)
  -- Phase 4: R3,R2,R2 chain x (3m+6j+8) rounds
  rw [show 3 * m + 6 * j + 8 = 0 + (3 * m + 6 * j + 8) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * m + 6 * j + 8) 0 1 2)
  rw [show 1 + (3 * m + 6 * j + 8) + 1 = 3 * m + 6 * j + 10 from by ring,
      show 2 + 3 * (3 * m + 6 * j + 8) = 9 * m + 18 * j + 26 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 10, 29⟩) (by execute fm 86)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, j⟩ ↦ ⟨0, 0, 0, 3 * j + 1, 3 * m + 6 * j + 8⟩) ⟨1, 3⟩
  intro ⟨m, j⟩
  exists ⟨m + 2 * j, m + 2 * j + 3⟩
  show ⟨(0 : ℕ), 0, 0, 3 * j + 1, 3 * m + 6 * j + 8⟩ [fm]⊢⁺
       ⟨(0 : ℕ), 0, 0, 3 * (m + 2 * j + 3) + 1, 3 * (m + 2 * j) + 6 * (m + 2 * j + 3) + 8⟩
  have h := main_transition m j
  rw [show 3 * (m + 2 * j + 3) + 1 = 3 * m + 6 * j + 10 from by ring,
      show 3 * (m + 2 * j) + 6 * (m + 2 * j + 3) + 8 = 9 * m + 18 * j + 26 from by ring]
  exact h

end Sz22_2003_unofficial_1244
