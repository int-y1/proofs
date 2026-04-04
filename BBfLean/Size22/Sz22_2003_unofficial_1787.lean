import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1787: [9/10, 4/21, 77/2, 5/7, 98/11]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  0
-1  0  0  1  1
 0  0  1 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt. From canonical state `(A, 0, 0, 0, E)` with `A >= 1`,
the machine transitions to `(A', 0, 0, 0, E')` with `A' >= 4` depending on `A mod 5`.
The proof decomposes the transition into: R3 chain (a to d,e), R4 chain (d to c),
core loop (5 units of c per round), tail (remainder), and R3/R2 drain (b to a,e).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1787

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem drain : ∀ k, ∀ a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

theorem core_step : ∀ b c e, ⟨0, b, c + 5, 0, e + 1⟩ [fm]⊢* ⟨0, b + 8, c, 0, e⟩ := by
  intro b c e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem core_loop : ∀ k, ∀ b c e, ⟨0, b, c + 5 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 8 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 5 * (k + 1) = (c + 5) + 5 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih b (c + 5) (e + 1))
    apply stepStar_trans (core_step (b + 8 * k) c e); ring_nf; finish

theorem tail0 : ∀ b e, ⟨0, b + 2, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨b + 5, 0, 0, 0, e + b⟩ := by
  intro b e; step fm; step fm; step fm
  apply stepStar_trans (drain b 4 e); ring_nf; finish

theorem tail1 : ∀ b e, ⟨0, b, 1, 0, e + 1⟩ [fm]⊢⁺ ⟨b + 4, 0, 0, 0, e + b⟩ := by
  intro b e; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain b 3 e); ring_nf; finish

theorem tail2 : ∀ b e, ⟨0, b, 2, 0, e + 1⟩ [fm]⊢⁺ ⟨b + 5, 0, 0, 0, e + b + 2⟩ := by
  intro b e; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain (b + 2) 2 e); ring_nf; finish

theorem tail3 : ∀ b e, ⟨0, b, 3, 0, e + 1⟩ [fm]⊢⁺ ⟨b + 6, 0, 0, 0, e + b + 4⟩ := by
  intro b e; step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain (b + 4) 1 e); ring_nf; finish

theorem tail4 : ∀ b e, ⟨0, b, 4, 0, e + 1⟩ [fm]⊢⁺ ⟨b + 7, 0, 0, 0, e + b + 6⟩ := by
  intro b e; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain (b + 6) 0 e); ring_nf; finish

theorem trans_r1 : ∀ k E, ⟨5 * k + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * k + 4, 0, 0, 0, 12 * k + E⟩ := by
  intro k E
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 8 * k, 1, 0, E + 4 * k + 1⟩)
  · rw [show 5 * k + 1 = 5 * k + 1 from rfl]
    apply stepStar_trans (r3_chain (5 * k + 1) 0 E)
    rw [show 0 + (5 * k + 1) = 5 * k + 1 from by ring,
        show E + (5 * k + 1) = E + 5 * k + 1 from by ring]
    apply stepStar_trans (r4_chain (5 * k + 1) 0 (E + 5 * k + 1))
    rw [show 0 + (5 * k + 1) = 1 + 5 * k from by ring,
        show E + 5 * k + 1 = (E + 4 * k + 1) + k from by ring]
    apply stepStar_trans (core_loop k 0 1 (E + 4 * k + 1))
    ring_nf; finish
  · rw [show E + 4 * k + 1 = (E + 4 * k) + 1 from by ring,
        show 12 * k + E = (E + 4 * k) + 8 * k from by omega]
    exact tail1 (8 * k) (E + 4 * k)

theorem trans_r2 : ∀ k E, ⟨5 * k + 2, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * k + 5, 0, 0, 0, 12 * k + E + 3⟩ := by
  intro k E
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 8 * k, 2, 0, E + 4 * k + 2⟩)
  · apply stepStar_trans (r3_chain (5 * k + 2) 0 E)
    rw [show 0 + (5 * k + 2) = 5 * k + 2 from by ring,
        show E + (5 * k + 2) = E + 5 * k + 2 from by ring]
    apply stepStar_trans (r4_chain (5 * k + 2) 0 (E + 5 * k + 2))
    rw [show 0 + (5 * k + 2) = 2 + 5 * k from by ring,
        show E + 5 * k + 2 = (E + 4 * k + 2) + k from by ring]
    apply stepStar_trans (core_loop k 0 2 (E + 4 * k + 2))
    ring_nf; finish
  · rw [show E + 4 * k + 2 = (E + 4 * k + 1) + 1 from by ring,
        show 12 * k + E + 3 = (E + 4 * k + 1) + 8 * k + 2 from by omega]
    exact tail2 (8 * k) (E + 4 * k + 1)

theorem trans_r3 : ∀ k E, ⟨5 * k + 3, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * k + 6, 0, 0, 0, 12 * k + E + 6⟩ := by
  intro k E
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 8 * k, 3, 0, E + 4 * k + 3⟩)
  · apply stepStar_trans (r3_chain (5 * k + 3) 0 E)
    rw [show 0 + (5 * k + 3) = 5 * k + 3 from by ring,
        show E + (5 * k + 3) = E + 5 * k + 3 from by ring]
    apply stepStar_trans (r4_chain (5 * k + 3) 0 (E + 5 * k + 3))
    rw [show 0 + (5 * k + 3) = 3 + 5 * k from by ring,
        show E + 5 * k + 3 = (E + 4 * k + 3) + k from by ring]
    apply stepStar_trans (core_loop k 0 3 (E + 4 * k + 3))
    ring_nf; finish
  · rw [show E + 4 * k + 3 = (E + 4 * k + 2) + 1 from by ring,
        show 12 * k + E + 6 = (E + 4 * k + 2) + 8 * k + 4 from by omega]
    exact tail3 (8 * k) (E + 4 * k + 2)

theorem trans_r4 : ∀ k E, ⟨5 * k + 4, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * k + 7, 0, 0, 0, 12 * k + E + 9⟩ := by
  intro k E
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 8 * k, 4, 0, E + 4 * k + 4⟩)
  · apply stepStar_trans (r3_chain (5 * k + 4) 0 E)
    rw [show 0 + (5 * k + 4) = 5 * k + 4 from by ring,
        show E + (5 * k + 4) = E + 5 * k + 4 from by ring]
    apply stepStar_trans (r4_chain (5 * k + 4) 0 (E + 5 * k + 4))
    rw [show 0 + (5 * k + 4) = 4 + 5 * k from by ring,
        show E + 5 * k + 4 = (E + 4 * k + 4) + k from by ring]
    apply stepStar_trans (core_loop k 0 4 (E + 4 * k + 4))
    ring_nf; finish
  · rw [show E + 4 * k + 4 = (E + 4 * k + 3) + 1 from by ring,
        show 12 * k + E + 9 = (E + 4 * k + 3) + 8 * k + 6 from by omega]
    exact tail4 (8 * k) (E + 4 * k + 3)

theorem trans_r0 : ∀ k E, ⟨5 * (k + 1), 0, 0, 0, E⟩ [fm]⊢⁺ ⟨8 * k + 11, 0, 0, 0, 12 * k + E + 9⟩ := by
  intro k E
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 8 * (k + 1), 0, 0, E + 4 * k + 4⟩)
  · apply stepStar_trans (r3_chain (5 * (k + 1)) 0 E)
    rw [show 0 + 5 * (k + 1) = 5 * (k + 1) from by ring,
        show E + 5 * (k + 1) = E + 5 * k + 5 from by ring]
    apply stepStar_trans (r4_chain (5 * (k + 1)) 0 (E + 5 * k + 5))
    rw [show 0 + 5 * (k + 1) = 0 + 5 * (k + 1) from by ring,
        show E + 5 * k + 5 = (E + 4 * k + 4) + (k + 1) from by ring]
    apply stepStar_trans (core_loop (k + 1) 0 0 (E + 4 * k + 4))
    ring_nf; finish
  · rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring,
        show E + 4 * k + 4 = (E + 4 * k + 3) + 1 from by ring,
        show 12 * k + E + 9 = (E + 4 * k + 3) + (8 * k + 6) from by omega]
    exact tail0 (8 * k + 6) (E + 4 * k + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = ⟨A, 0, 0, 0, E⟩ ∧ A ≥ 1)
  · intro c ⟨A, E, hq, hA⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl | rfl | rfl⟩ : ∃ k, A = 5 * k ∨ A = 5 * k + 1 ∨ A = 5 * k + 2 ∨ A = 5 * k + 3 ∨ A = 5 * k + 4 :=
      ⟨A / 5, by omega⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ⟨_, ⟨8 * k' + 11, 12 * k' + E + 9, rfl, by omega⟩, trans_r0 k' E⟩
    · exact ⟨_, ⟨8 * k + 4, 12 * k + E, rfl, by omega⟩, trans_r1 k E⟩
    · exact ⟨_, ⟨8 * k + 5, 12 * k + E + 3, rfl, by omega⟩, trans_r2 k E⟩
    · exact ⟨_, ⟨8 * k + 6, 12 * k + E + 6, rfl, by omega⟩, trans_r3 k E⟩
    · exact ⟨_, ⟨8 * k + 7, 12 * k + E + 9, rfl, by omega⟩, trans_r4 k E⟩
  · exact ⟨4, 0, rfl, by omega⟩
