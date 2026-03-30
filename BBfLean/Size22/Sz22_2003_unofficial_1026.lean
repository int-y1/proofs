import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1026: [4/15, 99/14, 65/2, 7/11, 21/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1026

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e f,
    ⟨a + k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d + k, e, f⟩ [fm]⊢*
    ⟨a + 3 * k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c d (e + 1) f)
    ring_nf; finish

theorem main_trans (c n f : ℕ) (hc : c ≥ 2 * n + 3) (hf : f ≥ 1) :
    ⟨(0 : ℕ), 0, c, 0, n, f⟩ [fm]⊢⁺ ⟨0, 0, c + n + 2, 0, n + 1, f + 3 * n + 4⟩ := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * (n + 1) + 1 := ⟨c - (2 * (n + 1) + 1), by omega⟩
  -- Phase 1: R4 chain (n steps): (0, 0, c, 0, n, f'+1) →* (0, 0, c, n, 0, f'+1)
  have h1 : ⟨(0 : ℕ), 0, c' + 2 * (n + 1) + 1, 0, n, f' + 1⟩ [fm]⊢*
      ⟨0, 0, c' + 2 * (n + 1) + 1, n, 0, f' + 1⟩ := by
    have := r4_chain n (c' + 2 * (n + 1) + 1) 0 (f' + 1)
    rw [show (0 : ℕ) + n = n from by ring] at this; exact this
  -- Phase 2: R5 + R1
  have h2 : ⟨(0 : ℕ), 0, c' + 2 * (n + 1) + 1, n, 0, f' + 1⟩ [fm]⊢⁺
      ⟨2, 0, c' + 2 * (n + 1), n + 1, 0, f'⟩ := by
    rw [show c' + 2 * (n + 1) + 1 = (c' + 2 * (n + 1)) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R2,R1,R1 chain (n+1 rounds)
  have h3 : ⟨(2 : ℕ), 0, c' + 2 * (n + 1), n + 1, 0, f'⟩ [fm]⊢*
      ⟨3 * (n + 1) + 2, 0, c', 0, n + 1, f'⟩ := by
    have := r2r1r1_chain (n + 1) 1 c' 0 0 f'
    convert this using 2; ring_nf
  -- Phase 4: R3 chain (3*(n+1)+2 steps)
  have h4 : ⟨3 * (n + 1) + 2, (0 : ℕ), c', 0, n + 1, f'⟩ [fm]⊢*
      ⟨0, 0, c' + (3 * (n + 1) + 2), 0, n + 1, f' + (3 * (n + 1) + 2)⟩ := by
    have := r3_chain (3 * (n + 1) + 2) 0 c' (n + 1) f'
    convert this using 2; ring_nf
  -- Compose
  have heq1 : c' + 2 * (n + 1) + 1 + n + 2 = c' + (3 * (n + 1) + 2) := by ring
  have heq2 : f' + 1 + 3 * n + 4 = f' + (3 * (n + 1) + 2) := by ring
  rw [heq1, heq2]
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 10, 0, 3, 22⟩) (by execute fm 52)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c n f, q = ⟨0, 0, c, 0, n, f⟩ ∧ c ≥ 2 * n + 3 ∧ n ≥ 3 ∧ f ≥ 1)
  · intro q ⟨c, n, f, hq, hc, hn, hf⟩
    exact ⟨⟨0, 0, c + n + 2, 0, n + 1, f + 3 * n + 4⟩,
      ⟨c + n + 2, n + 1, f + 3 * n + 4, rfl, by omega, by omega, by omega⟩,
      hq ▸ main_trans c n f hc hf⟩
  · exact ⟨10, 3, 22, rfl, by omega, le_refl 3, by omega⟩

end Sz22_2003_unofficial_1026
