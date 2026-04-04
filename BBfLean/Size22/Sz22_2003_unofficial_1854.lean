import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1854: [9/35, 125/33, 22/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  3  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1854

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm; apply stepStar_trans (ih a (d + 1)); ring_nf; finish

theorem c_drain : ∀ c, ∀ a e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a + c, 0, 0, 0, e + c⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

theorem spiral : ∀ b, ∀ a c, ⟨a, b, c + 1, 0, 0⟩ [fm]⊢* ⟨a + b, 0, c + 2 * b + 1, 0, 0⟩ := by
  intro b; induction' b with b ih <;> intro a c
  · exists 0
  · step fm; step fm; apply stepStar_trans (ih (a + 1) (c + 2)); ring_nf; finish

theorem drain_round : ∀ a b d, ⟨a + 1, b + 1, 3, d + 4, 0⟩ [fm]⊢* ⟨a, b + 8, 3, d, 0⟩ := by
  intro a b d; step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem drain_loop : ∀ k, ∀ a b, ⟨a + k, b + 1, 3, 4 * k + r, 0⟩ [fm]⊢* ⟨a, b + 7 * k + 1, 3, r, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; finish
  · rw [show a + (k + 1) = a + 1 + k from by ring,
        show 4 * (k + 1) + r = 4 * k + r + 4 from by ring]
    have h1 := drain_round (a + k) b (4 * k + r)
    rw [show a + k + 1 = a + 1 + k from by ring] at h1
    apply stepStar_trans h1
    rw [show b + 8 = b + 7 + 1 from by ring]
    have h2 := ih a (b + 7)
    rw [show b + 7 + 7 * k + 1 = b + 7 * (k + 1) + 1 from by ring] at h2
    exact h2

-- Tail: spiral + c_drain + e_to_d
theorem tail : ∀ b a c, ⟨a, b, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 3 * b + c + 1, 0, 0, c + 2 * b + 1, 0⟩ := by
  intro b a c
  apply stepStar_trans (spiral b a c)
  apply stepStar_trans (c_drain (c + 2 * b + 1) (a + b) 0)
  rw [show a + b + (c + 2 * b + 1) = a + 3 * b + c + 1 from by ring,
      show 0 + (c + 2 * b + 1) = c + 2 * b + 1 from by ring]
  have h := e_to_d (c + 2 * b + 1) (a + 3 * b + c + 1) 0
  rw [show 0 + (c + 2 * b + 1) = c + 2 * b + 1 from by ring] at h
  exact h

-- End r=1
theorem end_r1 : ∀ a b, ⟨a, b + 1, 3, 1, 0⟩ [fm]⊢⁺ ⟨a + 3 * b + 11, 0, 0, 2 * b + 8, 0⟩ := by
  intro a b
  step fm; step fm; step fm
  apply stepStar_trans (tail (b + 2) (a + 1) 3)
  ring_nf; finish

-- End r=2
theorem end_r2 : ∀ a b, ⟨a, b + 1, 3, 2, 0⟩ [fm]⊢⁺ ⟨a + 3 * b + 16, 0, 0, 2 * b + 11, 0⟩ := by
  intro a b
  step fm; step fm; step fm; step fm
  apply stepStar_trans (tail (b + 4) (a + 1) 2)
  ring_nf; finish

-- End r=3
theorem end_r3 : ∀ a b, ⟨a + 1, b + 1, 3, 3, 0⟩ [fm]⊢⁺ ⟨a + 3 * b + 22, 0, 0, 2 * b + 16, 0⟩ := by
  intro a b
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (tail (b + 6) a 3)
  ring_nf; finish

-- End r=0
theorem end_r0 : ∀ a b, ⟨a, b + 1, 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 3 * b + 6, 0, 0, 2 * b + 5, 0⟩ := by
  intro a b
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (tail b (a + 1) 4)
  ring_nf; finish

-- Compose: setup (3 steps via ⊢*) + drain_loop (⊢*) + end_rX (⊢⁺) = ⊢⁺
-- We use stepStar_stepPlus_stepPlus to compose ⊢* and ⊢⁺ into ⊢⁺.

-- Setup lemma
theorem setup : ∀ a d, ⟨a + 1, 0, 0, d + 1 + 1, 0⟩ [fm]⊢* ⟨a, 1, 3, d + 1, 0⟩ := by
  intro a d; step fm; step fm; step fm; ring_nf; finish

-- D mod 4 = 2: setup + k drain rounds + end_r1
theorem trans_mod2 : ∀ k a, ⟨a + 3 * k + 1, 0, 0, 4 * k + 2, 0⟩ [fm]⊢⁺
    ⟨a + 23 * k + 11, 0, 0, 14 * k + 8, 0⟩ := by
  intro k a
  rw [show a + 3 * k + 1 = (a + 3 * k) + 1 from by ring,
      show (4 * k + 2 : ℕ) = 4 * k + 1 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (setup (a + 3 * k) (4 * k))
  rw [show a + 3 * k = a + 2 * k + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 2 * k) 0 (r := 1))
  rw [show 0 + 7 * k + 1 = 7 * k + 1 from by ring]
  have h := end_r1 (a + 2 * k) (7 * k)
  rw [show a + 2 * k + 3 * (7 * k) + 11 = a + 23 * k + 11 from by ring,
      show 2 * (7 * k) + 8 = 14 * k + 8 from by ring] at h
  convert h using 2

-- D mod 4 = 3: setup + k drain rounds + end_r2
theorem trans_mod3 : ∀ k a, ⟨a + 3 * k + 1, 0, 0, 4 * k + 3, 0⟩ [fm]⊢⁺
    ⟨a + 23 * k + 16, 0, 0, 14 * k + 11, 0⟩ := by
  intro k a
  rw [show a + 3 * k + 1 = (a + 3 * k) + 1 from by ring,
      show (4 * k + 3 : ℕ) = 4 * k + 1 + 1 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (setup (a + 3 * k) (4 * k + 1))
  rw [show a + 3 * k = a + 2 * k + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 2 * k) 0 (r := 2))
  rw [show 0 + 7 * k + 1 = 7 * k + 1 from by ring]
  have h := end_r2 (a + 2 * k) (7 * k)
  rw [show a + 2 * k + 3 * (7 * k) + 16 = a + 23 * k + 16 from by ring,
      show 2 * (7 * k) + 11 = 14 * k + 11 from by ring] at h
  convert h using 2

-- D mod 4 = 0: setup + k drain rounds + end_r3
theorem trans_mod0 : ∀ k a, ⟨a + 3 * k + 2, 0, 0, 4 * (k + 1), 0⟩ [fm]⊢⁺
    ⟨a + 23 * k + 22, 0, 0, 14 * k + 16, 0⟩ := by
  intro k a
  rw [show a + 3 * k + 2 = (a + 3 * k + 1) + 1 from by ring,
      show (4 * (k + 1) : ℕ) = 4 * k + 2 + 1 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (setup (a + 3 * k + 1) (4 * k + 2))
  rw [show a + 3 * k + 1 = a + 2 * k + 1 + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 2 * k + 1) 0 (r := 3))
  rw [show 0 + 7 * k + 1 = 7 * k + 1 from by ring]
  have h := end_r3 (a + 2 * k) (7 * k)
  rw [show a + 2 * k + 3 * (7 * k) + 22 = a + 23 * k + 22 from by ring,
      show 2 * (7 * k) + 16 = 14 * k + 16 from by ring] at h
  convert h using 2

-- D mod 4 = 1: setup + (k+1) drain rounds + end_r0
theorem trans_mod1 : ∀ k a, ⟨a + 3 * k + 2, 0, 0, 4 * k + 5, 0⟩ [fm]⊢⁺
    ⟨a + 23 * k + 27, 0, 0, 14 * k + 19, 0⟩ := by
  intro k a
  rw [show a + 3 * k + 2 = (a + 3 * k + 1) + 1 from by ring,
      show (4 * k + 5 : ℕ) = 4 * k + 3 + 1 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (setup (a + 3 * k + 1) (4 * k + 3))
  rw [show 4 * k + 3 + 1 = 4 * (k + 1) + 0 from by ring,
      show a + 3 * k + 1 = a + 2 * k + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (k + 1) (a + 2 * k) 0 (r := 0))
  rw [show 0 + 7 * (k + 1) + 1 = 7 * k + 8 from by ring]
  have h := end_r0 (a + 2 * k) (7 * k + 7)
  rw [show a + 2 * k + 3 * (7 * k + 7) + 6 = a + 23 * k + 27 from by ring,
      show 2 * (7 * k + 7) + 5 = 14 * k + 19 from by ring] at h
  convert h using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + d + 1, 0, 0, d + 2, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ : ∃ k, d = 4 * k ∨ d = 4 * k + 1 ∨ d = 4 * k + 2 ∨ d = 4 * k + 3 :=
    ⟨d / 4, by omega⟩
  · refine ⟨⟨a + 10 * k + 4, 14 * k + 6⟩, ?_⟩
    dsimp only
    rw [show a + 10 * k + 4 + (14 * k + 6) + 1 = (a + k) + 23 * k + 11 from by ring,
        show 14 * k + 6 + 2 = 14 * k + 8 from by ring,
        show a + 4 * k + 1 = (a + k) + 3 * k + 1 from by ring]
    exact trans_mod2 k (a + k)
  · refine ⟨⟨a + 10 * k + 7, 14 * k + 9⟩, ?_⟩
    dsimp only
    rw [show a + 10 * k + 7 + (14 * k + 9) + 1 = (a + k + 1) + 23 * k + 16 from by ring,
        show 14 * k + 9 + 2 = 14 * k + 11 from by ring,
        show a + (4 * k + 1) + 1 = (a + k + 1) + 3 * k + 1 from by ring,
        show 4 * k + 1 + 2 = 4 * k + 3 from by ring]
    exact trans_mod3 k (a + k + 1)
  · refine ⟨⟨a + 10 * k + 8, 14 * k + 14⟩, ?_⟩
    dsimp only
    rw [show a + 10 * k + 8 + (14 * k + 14) + 1 = (a + k + 1) + 23 * k + 22 from by ring,
        show 14 * k + 14 + 2 = 14 * k + 16 from by ring,
        show a + (4 * k + 2) + 1 = (a + k + 1) + 3 * k + 2 from by ring,
        show 4 * k + 2 + 2 = 4 * (k + 1) from by ring]
    exact trans_mod0 k (a + k + 1)
  · refine ⟨⟨a + 10 * k + 11, 14 * k + 17⟩, ?_⟩
    dsimp only
    rw [show a + 10 * k + 11 + (14 * k + 17) + 1 = (a + k + 2) + 23 * k + 27 from by ring,
        show 14 * k + 17 + 2 = 14 * k + 19 from by ring,
        show a + (4 * k + 3) + 1 = (a + k + 2) + 3 * k + 2 from by ring,
        show 4 * k + 3 + 2 = 4 * k + 5 from by ring]
    exact trans_mod1 k (a + k + 2)
