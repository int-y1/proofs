import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1373: [63/10, 4/77, 363/2, 5/3, 7/5]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  1  0  0  2
 0 -1  1  0  0
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1373

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer b to c.
theorem r4_chain : ∀ k b c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e); ring_nf; finish

-- R3 chain: drain a, accumulating b and e.
theorem r3_chain : ∀ k b e, ⟨k, b, 0, 0, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) (e + 2)); ring_nf; finish

-- R2 chain: drain d, consuming e, accumulating a.
theorem r2_chain : ∀ k a b d e, ⟨a, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b d e); ring_nf; finish

-- R1R1R2 round chain.
theorem r1r1r2_chain : ∀ k, ∀ B C D E,
    ⟨2, B, C + 2 * k, D, E + k⟩ [fm]⊢* ⟨2, B + 4 * k, C, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro B C D E
  · exists 0
  · rw [show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring,
        show B + 4 * (k + 1) = (B + 4) + 4 * k from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (B + 4) C (D + 1) E); ring_nf; finish

-- Drain: (a+1, B, 0, D, e) ⊢* (0, B+a+2D+1, 0, 0, e+2a+3D+2).
-- By induction on D, case split on e.
theorem drain : ∀ D, ∀ a B e,
    ⟨a + 1, B, 0, D, e⟩ [fm]⊢* ⟨0, B + a + 2 * D + 1, 0, 0, e + 2 * a + 3 * D + 2⟩ := by
  intro D; induction' D with D ih <;> intro a B e
  · -- D = 0: r3_chain
    apply stepStar_trans (r3_chain (a + 1) B e)
    ring_nf; finish
  · -- D + 1: case on e
    rcases e with _ | e
    · -- e = 0: R3 step → (a, B+1, 0, D+1, 2), R2 step → (a+2, B+1, 0, D, 1), then IH
      step fm; step fm
      rw [show a + 2 = (a + 1) + 1 from by ring]
      apply stepStar_trans (ih (a + 1) (B + 1) 1)
      ring_nf; finish
    · -- e = e + 1 ≥ 1: R2 step → (a+3, B, 0, D, e), then IH
      step fm
      rw [show a + 1 + 2 = (a + 2) + 1 from by ring]
      apply stepStar_trans (ih (a + 2) B e)
      ring_nf; finish

-- Mixing: (2, B, b, D, e) ⊢* (0, B+3b+2D+2, 0, 0, e+b+3D+4) when 2e+1 ≥ b.
-- By strong induction on b.
theorem mixing : ∀ b, ∀ B D e, 2 * e + 1 ≥ b →
    ⟨2, B, b, D, e⟩ [fm]⊢* ⟨0, B + 3 * b + 2 * D + 2, 0, 0, e + b + 3 * D + 4⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih_b
  intro B D e he
  rcases b with _ | _ | b
  · -- b = 0: drain with a=1
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    apply stepStar_trans (drain D 1 B e)
    ring_nf; finish
  · -- b = 1: R1 step, then drain with a=0
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    apply stepStar_trans (drain (D + 1) 0 (B + 2) e)
    ring_nf; finish
  · -- b + 2: R1, R1, R2, then IH for b
    rw [show b + 2 = b + 1 + 1 from by ring]
    step fm; step fm
    rcases e with _ | e
    · omega
    · step fm
      rw [show B + 2 + 2 = B + 4 from by ring]
      apply stepStar_trans (ih_b b (by omega) (B + 4) (D + 1) e (by omega))
      ring_nf; finish

-- Main transition from canonical form.
theorem main_trans (b e : ℕ) (he : 2 * e + 1 ≥ b) :
    ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 3 * b + 2, 0, 0, e + b + 4⟩ := by
  rw [show (b + 1 : ℕ) = 0 + (b + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (b + 1) 0 0 (e + 1))
  rw [show (0 : ℕ) + (b + 1) = b + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (mixing b 0 0 e he)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b + 1, 0, 0, e + 1⟩ ∧ 2 * e + 1 ≥ b)
  · intro c ⟨b, e, hq, he⟩
    subst hq
    refine ⟨⟨0, 3 * b + 2, 0, 0, e + b + 4⟩, ?_, ?_⟩
    · rw [show e + b + 4 = (e + b + 3) + 1 from by ring,
          show 3 * b + 2 = (3 * b + 1) + 1 from by ring]
      exact ⟨3 * b + 1, e + b + 3, rfl, by omega⟩
    · exact main_trans b e he
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1373
