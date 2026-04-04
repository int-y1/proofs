import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1853: [9/35, 125/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  3  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1853

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ a e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem spiral_pairs : ∀ c, ∀ a b, ⟨a, b, c + 1, 1, 0⟩ [fm]⊢* ⟨a + c + 1, b + c + 1, 0, 1, 0⟩ := by
  intro c; induction' c with c ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    show ⟨a + 1, b + 1, c + 1, 1, 0⟩ [fm]⊢* ⟨a + (c + 1) + 1, b + (c + 1) + 1, 0, 1, 0⟩
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

theorem spiral : ∀ c, ∀ a b, ⟨a, b, c + 1, 1, 0⟩ [fm]⊢* ⟨a + b + 2 * c + 2, 0, 0, b + c + 2, 0⟩ := by
  intro c a b
  apply stepStar_trans (spiral_pairs c a b)
  rw [show a + b + 2 * c + 2 = (a + c + 1) + (b + c + 1) from by ring,
      show b + c + 2 = 1 + (b + c + 1) from by ring]
  exact r3_chain (b + c + 1) (a + c + 1) 1

theorem opening_round : ∀ a e, ⟨a + 1, 0, 0, 0, e + 3⟩ [fm]⊢* ⟨a, 0, 8, 0, e⟩ := by
  intro a e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem drain_round : ∀ a c e, ⟨a + 1, 0, c + 1, 0, e + 3⟩ [fm]⊢* ⟨a, 0, c + 9, 0, e⟩ := by
  intro a c e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem drain_chain : ∀ k, ∀ a e, ⟨a + k + 1, 0, 0, 0, 3 * k + 3 + e⟩ [fm]⊢* ⟨a, 0, 8 * k + 8, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · rw [show a + 0 + 1 = a + 1 from by ring, show 3 * 0 + 3 + e = e + 3 from by ring,
        show 8 * 0 + 8 = 8 from by ring]
    exact opening_round a e
  · rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show 3 * (k + 1) + 3 + e = 3 * k + 3 + (e + 3) from by ring]
    apply stepStar_trans (ih (a + 1) (e + 3))
    rw [show 8 * k + 8 = (8 * k + 7) + 1 from by ring]
    exact drain_round a (8 * k + 7) e

theorem post_drain_e0 : ∀ c a, ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 2 * c + 3, 0, 0, c + 3, 0⟩ := by
  intro c a
  step fm; step fm; step fm
  rcases c with _ | c
  · show ⟨a + 1, 2, 0, 1, 0⟩ [fm]⊢* ⟨a + 3, 0, 0, 3, 0⟩
    rw [show a + 3 = (a + 1) + 2 from by ring, show (3 : ℕ) = 1 + 2 from by ring]
    exact r3_chain 2 (a + 1) 1
  · rw [show a + 2 * (c + 1) + 3 = (a + 1) + 2 + 2 * c + 2 from by ring,
        show c + 1 + 3 = 2 + c + 2 from by ring]
    exact spiral c (a + 1) 2

theorem post_drain_e1 : ∀ c a, ⟨a + 1, 0, c + 1, 0, 1⟩ [fm]⊢* ⟨a + 2 * c + 8, 0, 0, c + 5, 0⟩ := by
  intro c a
  step fm; step fm; step fm; step fm
  rw [show a + 2 * c + 8 = (a + 1) + 1 + 2 * (c + 2) + 2 from by ring,
      show c + 5 = 1 + (c + 2) + 2 from by ring]
  exact spiral (c + 2) (a + 1) 1

theorem post_drain_e2 : ∀ c a, ⟨a + 1, 0, c + 1, 0, 2⟩ [fm]⊢* ⟨a + 2 * c + 13, 0, 0, c + 7, 0⟩ := by
  intro c a
  step fm; step fm; step fm; step fm; step fm
  rw [show a + 2 * c + 13 = (a + 1) + 0 + 2 * (c + 5) + 2 from by ring,
      show c + 7 = 0 + (c + 5) + 2 from by ring]
  exact spiral (c + 5) (a + 1) 0

theorem post_drain_e2_zero : ∀ a, ⟨a + 1, 0, 0, 0, 2⟩ [fm]⊢* ⟨a + 11, 0, 0, 6, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm; step fm
  rw [show a + 11 = (a + 1) + 0 + 2 * 4 + 2 from by ring,
      show (6 : ℕ) = 0 + 4 + 2 from by ring]
  exact spiral 4 (a + 1) 0

theorem full_trans_mod2 : ∀ k a, ⟨a + k + 1, 0, 0, 3 * k + 2, 0⟩ [fm]⊢* ⟨a + 16 * k + 11, 0, 0, 8 * k + 6, 0⟩ := by
  intro k a
  rcases k with _ | k
  · rw [show a + 0 + 1 = a + 1 from by ring, show 3 * 0 + 2 = 2 from by ring,
        show a + 16 * 0 + 11 = a + 11 from by ring, show 8 * 0 + 6 = 6 from by ring]
    apply stepStar_trans (d_to_e 2 (a + 1) 0)
    rw [show 0 + 2 = 2 from by ring]
    exact post_drain_e2_zero a
  · rw [show a + (k + 1) + 1 = a + k + 2 from by ring,
        show 3 * (k + 1) + 2 = 3 * k + 5 from by ring]
    apply stepStar_trans (d_to_e (3 * k + 5) (a + k + 2) 0)
    rw [show 0 + (3 * k + 5) = 3 * k + 3 + 2 from by ring,
        show a + k + 2 = (a + 1) + k + 1 from by ring]
    apply stepStar_trans (drain_chain k (a + 1) 2)
    rw [show 8 * k + 8 = (8 * k + 7) + 1 from by ring]
    apply stepStar_trans (post_drain_e2 (8 * k + 7) a)
    rw [show a + 2 * (8 * k + 7) + 13 = a + 16 * (k + 1) + 11 from by ring,
        show 8 * k + 7 + 7 = 8 * (k + 1) + 6 from by ring]
    finish

theorem full_trans_mod0 : ∀ k a, ⟨a + k + 2, 0, 0, 3 * k + 3, 0⟩ [fm]⊢* ⟨a + 16 * k + 17, 0, 0, 8 * k + 10, 0⟩ := by
  intro k a
  apply stepStar_trans (d_to_e (3 * k + 3) (a + k + 2) 0)
  rw [show 0 + (3 * k + 3) = 3 * k + 3 + 0 from by ring,
      show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_trans (drain_chain k (a + 1) 0)
  rw [show 8 * k + 8 = (8 * k + 7) + 1 from by ring]
  apply stepStar_trans (post_drain_e0 (8 * k + 7) a)
  rw [show a + 2 * (8 * k + 7) + 3 = a + 16 * k + 17 from by ring,
      show 8 * k + 7 + 3 = 8 * k + 10 from by ring]
  finish

theorem full_trans_mod1 : ∀ k a, ⟨a + k + 2, 0, 0, 3 * k + 4, 0⟩ [fm]⊢* ⟨a + 16 * k + 22, 0, 0, 8 * k + 12, 0⟩ := by
  intro k a
  apply stepStar_trans (d_to_e (3 * k + 4) (a + k + 2) 0)
  rw [show 0 + (3 * k + 4) = 3 * k + 3 + 1 from by ring,
      show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_trans (drain_chain k (a + 1) 1)
  rw [show 8 * k + 8 = (8 * k + 7) + 1 from by ring]
  apply stepStar_trans (post_drain_e1 (8 * k + 7) a)
  rw [show a + 2 * (8 * k + 7) + 8 = a + 16 * k + 22 from by ring,
      show 8 * k + 7 + 5 = 8 * k + 12 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 0, 6, 0⟩)
  · execute fm 24
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 2 ∧ a ≥ d)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, d = 3 * q ∨ d = 3 * q + 1 ∨ d = 3 * q + 2 := ⟨d / 3, by omega⟩
    · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨m + 16 * k + 17, 0, 0, 8 * k + 10, 0⟩,
        ⟨m + 16 * k + 17, 8 * k + 10, rfl, by omega, by omega⟩, ?_⟩
      exact stepStar_stepPlus (full_trans_mod0 k m) (by intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega)
    · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨m + 16 * k + 22, 0, 0, 8 * k + 12, 0⟩,
        ⟨m + 16 * k + 22, 8 * k + 12, rfl, by omega, by omega⟩, ?_⟩
      exact stepStar_stepPlus (full_trans_mod1 k m) (by intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega)
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + q + 1 := ⟨a - q - 1, by omega⟩
      refine ⟨⟨m + 16 * q + 11, 0, 0, 8 * q + 6, 0⟩,
        ⟨m + 16 * q + 11, 8 * q + 6, rfl, by omega, by omega⟩, ?_⟩
      exact stepStar_stepPlus (full_trans_mod2 q m) (by intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega)
  · exact ⟨11, 6, rfl, by omega, by omega⟩
