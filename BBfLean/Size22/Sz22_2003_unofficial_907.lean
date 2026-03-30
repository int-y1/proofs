import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #907: [4/15, 3/14, 275/2, 7/5, 20/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_907

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ a, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e + a⟩ := by
  intro a; induction' a with a ih generalizing c e
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2) (e := e + 1))
    ring_nf; finish

theorem r4_chain : ∀ c, ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + c, e⟩ := by
  intro c; induction' c with c ih generalizing d
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r2_chain : ∀ a, ∀ b d, ⟨a, b, 0, d + a, e⟩ [fm]⊢* ⟨0, b + a, 0, d, e⟩ := by
  intro a; induction' a with a ih <;> intro b d
  · simp; exists 0
  · rw [show d + (a + 1) = d + a + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d))
    ring_nf; finish

theorem macro_round : ⟨0, B + 1, 0, D + 4, e + 1⟩ [fm]⊢* ⟨0, B + 4, 0, D, e⟩ := by
  step fm; step fm
  have h := r2_chain 4 (b := B) (d := D) (e := e)
  rw [show D + 4 = D + 4 from rfl] at h
  apply stepStar_trans h
  ring_nf; finish

theorem drain_rounds : ∀ k, ∀ B e, ⟨0, B + 3, 0, 4 * k + r, e + k⟩ [fm]⊢* ⟨0, B + 3 + 3 * k, 0, r, e⟩ := by
  intro k; induction' k with k ih <;> intro B e
  · simp; exists 0
  · rw [show 4 * (k + 1) + r = 4 * k + r + 4 from by ring,
        show e + (k + 1) = e + 1 + k from by ring,
        show B + 3 = (B + 2) + 1 from by ring]
    have hm := macro_round (B := B + 2) (D := 4 * k + r) (e := e + k)
    rw [show e + k + 1 = e + 1 + k from by ring] at hm
    apply stepStar_trans hm
    rw [show B + 2 + 4 = (B + 3) + 3 from by ring]
    apply stepStar_trans (ih (B := B + 3) (e := e))
    ring_nf; finish

theorem cleanup_r0 : ⟨0, B + 3, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨7, B, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem cleanup_r1 : ⟨0, B + 3, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨6, B + 1, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem cleanup_r2 : ⟨0, B + 3, 0, 2, e + 1⟩ [fm]⊢⁺ ⟨5, B + 2, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem cleanup_r3 : ⟨0, B + 3, 0, 3, e + 1⟩ [fm]⊢⁺ ⟨4, B + 3, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem mini_chain : ∀ k, ∀ a e b, ⟨a + 1, 2 * k + b, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e b
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = 2 * k + (b + 2) from by ring]
    apply stepStar_trans (ih (a := a) (b := b + 2) (e := e))
    rw [show a + 1 + 3 * k = (a + 3 * k) + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish

theorem expand_even : ⟨A + 1, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨3, 0, 0, 2 * A + 1, e + A + 1⟩ := by
  apply stepStar_trans (r3_chain (A + 1) (c := 0) (e := e + 1))
  rw [show 0 + 2 * (A + 1) = 2 * A + 2 from by ring, show e + 1 + (A + 1) = e + A + 2 from by ring]
  apply stepStar_trans (r4_chain (2 * A + 2) (d := 0) (e := e + A + 2))
  rw [show 0 + (2 * A + 2) = (2 * A) + 2 from by ring,
      show e + A + 2 = (e + A + 1) + 1 from by ring]
  step fm; step fm; step fm; finish

theorem odd_tail : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2, 0, 1, 0, e + 1⟩ := by
  step fm; step fm; finish

theorem expand_odd : ⟨a + 2, 0, 1, 0, e + 1⟩ [fm]⊢* ⟨3, 0, 0, 2 * a + 4, e + a + 2⟩ := by
  apply stepStar_trans (r3_chain (a + 2) (c := 1) (e := e + 1))
  rw [show 1 + 2 * (a + 2) = 2 * a + 5 from by ring, show e + 1 + (a + 2) = e + a + 3 from by ring]
  apply stepStar_trans (r4_chain (2 * a + 5) (d := 0) (e := e + a + 3))
  rw [show 0 + (2 * a + 5) = (2 * a + 3) + 2 from by ring,
      show e + a + 3 = (e + a + 2) + 1 from by ring]
  step fm; step fm; step fm; finish

theorem r2_phase : ⟨3, 0, 0, D + 3, e⟩ [fm]⊢* ⟨0, 3, 0, D, e⟩ := by
  have h := r2_chain 3 (b := 0) (d := D) (e := e)
  rw [show 0 + 3 = 3 from by ring] at h
  exact h

theorem d1_trans : ⟨3, 0, 0, 1, f⟩ [fm]⊢⁺ ⟨3, 0, 0, 6, f + 3⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (expand_odd (a := 1) (e := f))
  ring_nf; finish

theorem d2_trans : ⟨3, 0, 0, 2, f⟩ [fm]⊢⁺ ⟨3, 0, 0, 7, f + 4⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (expand_even (A := 3) (e := f))
  ring_nf; finish

theorem case_m3 : ⟨3, 0, 0, 8 * j + 3, f + 2 * j + 1⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 13, f + 12 * j + 7⟩ := by
  rw [show 8 * j + 3 = 8 * j + 3 from rfl,
      show f + 2 * j + 1 = (f + 1) + 2 * j from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j) (e := (f + 1) + 2 * j))
  rw [show 8 * j = 4 * (2 * j) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j) (B := 0) (r := 0) (e := f + 1))
  rw [show 0 + 3 + 3 * (2 * j) = 6 * j + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r0 (B := 6 * j) (e := f))
  rw [show (7 : ℕ) = (6 : ℕ) + 1 from by ring,
      show 6 * j = 2 * (3 * j) + 0 from by ring]
  apply stepStar_trans (mini_chain (3 * j) (a := 6) (b := 0) (e := f + 1))
  rw [show 6 + 1 + 3 * (3 * j) = (6 + 9 * j) + 1 from by ring,
      show f + 1 + 3 * j = (f + 3 * j) + 1 from by ring]
  apply stepStar_trans (expand_even (A := 6 + 9 * j) (e := f + 3 * j))
  ring_nf; finish

theorem case_m4 : ⟨3, 0, 0, 8 * j + 4, f + 2 * j + 1⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 14, f + 12 * j + 8⟩ := by
  rw [show 8 * j + 4 = (8 * j + 1) + 3 from by ring,
      show f + 2 * j + 1 = (f + 1) + 2 * j from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 1) (e := (f + 1) + 2 * j))
  rw [show 8 * j + 1 = 4 * (2 * j) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j) (B := 0) (r := 1) (e := f + 1))
  rw [show 0 + 3 + 3 * (2 * j) = 6 * j + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r1 (B := 6 * j) (e := f))
  rw [show 6 * j + 1 = 2 * (3 * j) + 1 from by ring,
      show (6 : ℕ) = (5 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j) (a := 5) (b := 1) (e := f + 1))
  rw [show 5 + 1 + 3 * (3 * j) = (5 + 9 * j) + 1 from by ring]
  apply stepStar_trans (odd_tail (a := 5 + 9 * j) (e := f + 1 + 3 * j))
  apply stepStar_trans (expand_odd (a := 5 + 9 * j) (e := f + 1 + 3 * j))
  ring_nf; finish

theorem case_m5 : ⟨3, 0, 0, 8 * j + 5, f + 2 * j + 1⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 15, f + 12 * j + 9⟩ := by
  rw [show 8 * j + 5 = (8 * j + 2) + 3 from by ring,
      show f + 2 * j + 1 = (f + 1) + 2 * j from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 2) (e := (f + 1) + 2 * j))
  rw [show 8 * j + 2 = 4 * (2 * j) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j) (B := 0) (r := 2) (e := f + 1))
  rw [show 0 + 3 + 3 * (2 * j) = 6 * j + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r2 (B := 6 * j) (e := f))
  rw [show 6 * j + 2 = 2 * (3 * j + 1) + 0 from by ring,
      show (5 : ℕ) = (4 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j + 1) (a := 4) (b := 0) (e := f + 1))
  rw [show 4 + 1 + 3 * (3 * j + 1) = (7 + 9 * j) + 1 from by ring,
      show f + 1 + (3 * j + 1) = (f + 3 * j + 1) + 1 from by ring]
  apply stepStar_trans (expand_even (A := 7 + 9 * j) (e := f + 3 * j + 1))
  ring_nf; finish

theorem case_m6 : ⟨3, 0, 0, 8 * j + 6, f + 2 * j + 1⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 16, f + 12 * j + 10⟩ := by
  rw [show 8 * j + 6 = (8 * j + 3) + 3 from by ring,
      show f + 2 * j + 1 = (f + 1) + 2 * j from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 3) (e := (f + 1) + 2 * j))
  rw [show 8 * j + 3 = 4 * (2 * j) + 3 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j) (B := 0) (r := 3) (e := f + 1))
  rw [show 0 + 3 + 3 * (2 * j) = 6 * j + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r3 (B := 6 * j) (e := f))
  rw [show 6 * j + 3 = 2 * (3 * j + 1) + 1 from by ring,
      show (4 : ℕ) = (3 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j + 1) (a := 3) (b := 1) (e := f + 1))
  rw [show 3 + 1 + 3 * (3 * j + 1) = (6 + 9 * j) + 1 from by ring]
  apply stepStar_trans (odd_tail (a := 6 + 9 * j) (e := f + 1 + (3 * j + 1)))
  apply stepStar_trans (expand_odd (a := 6 + 9 * j) (e := f + 1 + (3 * j + 1)))
  ring_nf; finish

theorem case_m7 : ⟨3, 0, 0, 8 * j + 7, f + 2 * j + 2⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 22, f + 12 * j + 13⟩ := by
  rw [show 8 * j + 7 = (8 * j + 4) + 3 from by ring,
      show f + 2 * j + 2 = (f + 1) + (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 4) (e := (f + 1) + (2 * j + 1)))
  rw [show 8 * j + 4 = 4 * (2 * j + 1) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j + 1) (B := 0) (r := 0) (e := f + 1))
  rw [show 0 + 3 + 3 * (2 * j + 1) = (6 * j + 3) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r0 (B := 6 * j + 3) (e := f))
  rw [show 6 * j + 3 = 2 * (3 * j + 1) + 1 from by ring,
      show (7 : ℕ) = (6 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j + 1) (a := 6) (b := 1) (e := f + 1))
  rw [show 6 + 1 + 3 * (3 * j + 1) = (9 + 9 * j) + 1 from by ring]
  apply stepStar_trans (odd_tail (a := 9 + 9 * j) (e := f + 1 + (3 * j + 1)))
  apply stepStar_trans (expand_odd (a := 9 + 9 * j) (e := f + 1 + (3 * j + 1)))
  ring_nf; finish

theorem case_m0 : ⟨3, 0, 0, 8 * (j + 1), f + 2 * j + 2⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 23, f + 12 * j + 14⟩ := by
  rw [show 8 * (j + 1) = (8 * j + 5) + 3 from by ring,
      show f + 2 * j + 2 = (f + 1) + (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 5) (e := (f + 1) + (2 * j + 1)))
  rw [show 8 * j + 5 = 4 * (2 * j + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j + 1) (B := 0) (r := 1) (e := f + 1))
  rw [show 0 + 3 + 3 * (2 * j + 1) = (6 * j + 3) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r1 (B := 6 * j + 3) (e := f))
  rw [show 6 * j + 3 + 1 = 2 * (3 * j + 2) + 0 from by ring,
      show (6 : ℕ) = (5 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j + 2) (a := 5) (b := 0) (e := f + 1))
  rw [show 5 + 1 + 3 * (3 * j + 2) = (11 + 9 * j) + 1 from by ring,
      show f + 1 + (3 * j + 2) = (f + 3 * j + 2) + 1 from by ring]
  apply stepStar_trans (expand_even (A := 11 + 9 * j) (e := f + 3 * j + 2))
  ring_nf; finish

theorem case_m1 : ⟨3, 0, 0, 8 * (j + 1) + 1, f + 2 * j + 3⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 24, f + 12 * j + 16⟩ := by
  rw [show 8 * (j + 1) + 1 = (8 * j + 6) + 3 from by ring,
      show f + 2 * j + 3 = (f + 2) + (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 6) (e := (f + 2) + (2 * j + 1)))
  rw [show 8 * j + 6 = 4 * (2 * j + 1) + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j + 1) (B := 0) (r := 2) (e := f + 2))
  rw [show 0 + 3 + 3 * (2 * j + 1) = (6 * j + 3) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r2 (B := 6 * j + 3) (e := f + 1))
  rw [show 6 * j + 3 + 2 = 2 * (3 * j + 2) + 1 from by ring,
      show f + 1 + 1 = f + 2 from by ring,
      show (5 : ℕ) = (4 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j + 2) (a := 4) (b := 1) (e := f + 2))
  rw [show 4 + 1 + 3 * (3 * j + 2) = (10 + 9 * j) + 1 from by ring]
  apply stepStar_trans (odd_tail (a := 10 + 9 * j) (e := f + 2 + (3 * j + 2)))
  apply stepStar_trans (expand_odd (a := 10 + 9 * j) (e := f + 2 + (3 * j + 2)))
  ring_nf; finish

theorem case_m2 : ⟨3, 0, 0, 8 * (j + 1) + 2, f + 2 * j + 3⟩ [fm]⊢⁺ ⟨3, 0, 0, 18 * j + 25, f + 12 * j + 17⟩ := by
  rw [show 8 * (j + 1) + 2 = (8 * j + 7) + 3 from by ring,
      show f + 2 * j + 3 = (f + 2) + (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r2_phase (D := 8 * j + 7) (e := (f + 2) + (2 * j + 1)))
  rw [show 8 * j + 7 = 4 * (2 * j + 1) + 3 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_rounds (2 * j + 1) (B := 0) (r := 3) (e := f + 2))
  rw [show 0 + 3 + 3 * (2 * j + 1) = (6 * j + 3) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (cleanup_r3 (B := 6 * j + 3) (e := f + 1))
  rw [show 6 * j + 3 + 3 = 2 * (3 * j + 3) + 0 from by ring,
      show f + 1 + 1 = f + 2 from by ring,
      show (4 : ℕ) = (3 : ℕ) + 1 from by ring]
  apply stepStar_trans (mini_chain (3 * j + 3) (a := 3) (b := 0) (e := f + 2))
  rw [show 3 + 1 + 3 * (3 * j + 3) = (12 + 9 * j) + 1 from by ring,
      show f + 2 + (3 * j + 3) = (f + 3 * j + 4) + 1 from by ring]
  apply stepStar_trans (expand_even (A := 12 + 9 * j) (e := f + 3 * j + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 6, 3⟩) (by execute fm 22)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨3, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ 4 * e ≥ d + 1)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases (show d = 1 ∨ d = 2 ∨ d ≥ 3 from by omega) with rfl | rfl | hd3
    · exact ⟨⟨3, 0, 0, 6, e + 3⟩, ⟨6, e + 3, rfl, by omega, by omega⟩, d1_trans⟩
    · exact ⟨⟨3, 0, 0, 7, e + 4⟩, ⟨7, e + 4, rfl, by omega, by omega⟩, d2_trans⟩
    · obtain ⟨n, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ :
          ∃ n, d = 8 * n + 3 ∨ d = 8 * n + 4 ∨ d = 8 * n + 5 ∨ d = 8 * n + 6 ∨
               d = 8 * n + 7 ∨ d = 8 * (n + 1) ∨ d = 8 * (n + 1) + 1 ∨ d = 8 * (n + 1) + 2 :=
        ⟨(d - 3) / 8, by omega⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 1 := ⟨e - 2 * n - 1, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 13, f + 12 * n + 7⟩,
          ⟨18 * n + 13, f + 12 * n + 7, rfl, by omega, by omega⟩, case_m3⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 1 := ⟨e - 2 * n - 1, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 14, f + 12 * n + 8⟩,
          ⟨18 * n + 14, f + 12 * n + 8, rfl, by omega, by omega⟩, case_m4⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 1 := ⟨e - 2 * n - 1, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 15, f + 12 * n + 9⟩,
          ⟨18 * n + 15, f + 12 * n + 9, rfl, by omega, by omega⟩, case_m5⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 1 := ⟨e - 2 * n - 1, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 16, f + 12 * n + 10⟩,
          ⟨18 * n + 16, f + 12 * n + 10, rfl, by omega, by omega⟩, case_m6⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 2 := ⟨e - 2 * n - 2, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 22, f + 12 * n + 13⟩,
          ⟨18 * n + 22, f + 12 * n + 13, rfl, by omega, by omega⟩, case_m7⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 2 := ⟨e - 2 * n - 2, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 23, f + 12 * n + 14⟩,
          ⟨18 * n + 23, f + 12 * n + 14, rfl, by omega, by omega⟩, case_m0⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 3 := ⟨e - 2 * n - 3, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 24, f + 12 * n + 16⟩,
          ⟨18 * n + 24, f + 12 * n + 16, rfl, by omega, by omega⟩, case_m1⟩
      · obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 * n + 3 := ⟨e - 2 * n - 3, by omega⟩
        exact ⟨⟨3, 0, 0, 18 * n + 25, f + 12 * n + 17⟩,
          ⟨18 * n + 25, f + 12 * n + 17, rfl, by omega, by omega⟩, case_m2⟩
  · exact ⟨6, 3, rfl, by omega, by omega⟩
