import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #891: [4/15, 147/22, 175/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_891

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem R4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih c d (e + 1)); ring_nf; finish

theorem R3_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 2) (d + 1)); ring_nf; finish

theorem R2R1_chain : ∀ k a c d e,
    ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (d + 2) e); ring_nf; finish

theorem R2_chain : ∀ k a b d e,
    ⟨a + k, b, 0, d, e + k⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) (d + 2) e); ring_nf; finish

theorem phase3 : ∀ b a d,
    ⟨a + 1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, d + a + 2 * b + 1, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | _ | b
  · apply stepStar_trans (R3_chain (a + 1) 0 d); ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (R3_chain (a + 2) 1 (d + 1)); ring_nf; finish
  · step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih b (by omega) (a + 3) (d + 1)); ring_nf; finish

theorem main_trans (p q : ℕ) :
    ⟨0, 0, q + p + 2, q + 2 * p + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * q + 3 * p + 5, 3 * q + 6 * p + 5, 0⟩ := by
  -- Phase 1: R4 chain to drain d
  have h1 : ⟨0, 0, q + p + 2, q + 2 * p + 1, 0⟩ [fm]⊢*
      ⟨0, 0, q + p + 2, 0, q + 2 * p + 1⟩ := by
    rw [show q + 2 * p + 1 = 0 + (q + 2 * p + 1) from by ring]
    exact R4_chain (q + 2 * p + 1) (q + p + 2) 0 0
  -- Phase 2a: R5 + R1
  have h2a : ⟨0, 0, q + p + 2, 0, q + 2 * p + 1⟩ [fm]⊢*
      ⟨2, 0, q + p, 0, q + 2 * p + 1⟩ := by
    step fm; step fm; finish
  -- Phase 2b: R2R1 chain
  have h2b : ⟨2, 0, q + p, 0, q + 2 * p + 1⟩ [fm]⊢*
      ⟨q + p + 2, 0, 0, 2 * q + 2 * p, p + 1⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show q + p = 0 + (q + p) from by ring,
        show q + 2 * p + 1 = (p + 1) + (q + p) from by ring]
    apply stepStar_trans (R2R1_chain (q + p) 1 0 0 (p + 1)); ring_nf; finish
  -- Phase 2c: R2 chain
  have h2c : ⟨q + p + 2, 0, 0, 2 * q + 2 * p, p + 1⟩ [fm]⊢*
      ⟨q + 1, p + 1, 0, 2 * q + 4 * p + 2, 0⟩ := by
    have key := R2_chain (p + 1) (q + 1) 0 (2 * q + 2 * p) 0
    -- key : ⟨q+1+(p+1), 0, 0, 2*q+2*p, 0+(p+1)⟩ ⊢* ⟨q+1, 0+(p+1), 0, 2*q+2*p+2*(p+1), 0⟩
    rw [show q + 1 + (p + 1) = q + p + 2 from by omega,
        show (0 : ℕ) + (p + 1) = p + 1 from by omega] at key
    apply stepStar_trans key
    ring_nf; finish
  -- Phase 3
  have h3 : ⟨q + 1, p + 1, 0, 2 * q + 4 * p + 2, 0⟩ [fm]⊢*
      ⟨0, 0, 2 * q + 3 * p + 5, 3 * q + 6 * p + 5, 0⟩ := by
    apply stepStar_trans (phase3 (p + 1) q (2 * q + 4 * p + 2)); ring_nf; finish
  -- Compose all phases
  exact stepStar_stepPlus
    (stepStar_trans h1 (stepStar_trans h2a (stepStar_trans h2b (stepStar_trans h2c h3))))
    (by intro h; have := congr_arg (fun x : Q => x.2.2.2.1) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun s ↦ ∃ p q, s = ⟨0, 0, q + p + 2, q + 2 * p + 1, 0⟩)
  · intro s ⟨p, q, hs⟩; subst hs
    refine ⟨⟨0, 0, 2 * q + 3 * p + 5, 3 * q + 6 * p + 5, 0⟩,
      ⟨q + 3 * p + 1, q + 2, ?_⟩, main_trans p q⟩
    ring_nf
  · exact ⟨0, 0, by ring_nf⟩
