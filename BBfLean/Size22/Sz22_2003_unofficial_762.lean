import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #762: [35/6, 4/55, 847/2, 39/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  1  2  0
 0  1  0 -1  0  1
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_762

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+2, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ b d f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d (f + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c d e f,
    ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ a d e,
    ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r1r1r2_chain : ∀ n, ∀ b k d e f,
    ⟨2, b + 2 * n, k, d, e + n, f⟩ [fm]⊢* ⟨2, b, k + n, d + 2 * n, e, f⟩ := by
  intro n; induction' n with n ih <;> intro b k d e f
  · exists 0
  · rw [show b + 2 * (n + 1) = (b + 2 * n + 1) + 1 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm
    rw [show b + 2 * n + 1 = (b + 2 * n) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih b (k + 1) (d + 2) e f)
    ring_nf; finish

theorem chain_even : ∀ n e f,
    ⟨2, 2 * n, 0, 0, e + 2 * n, f⟩ [fm]⊢* ⟨2 * n + 2, 0, 0, 2 * n, e, f⟩ := by
  intro n e f
  rw [show e + 2 * n = (e + n) + n from by ring,
      show 2 * n = 0 + 2 * n from by ring]
  apply stepStar_trans (r1r1r2_chain n 0 0 0 (e + n) f)
  convert r2_drain n 2 0 (0 + 2 * n) e f using 2; ring_nf

theorem chain_odd : ∀ n e f,
    ⟨2, 2 * n + 1, 0, 0, e + (2 * n + 1), f⟩ [fm]⊢* ⟨2 * n + 3, 0, 0, 2 * n + 1, e, f⟩ := by
  intro n e f
  rw [show e + (2 * n + 1) = (e + n + 1) + n from by ring,
      show 2 * n + 1 = 1 + 2 * n from by ring]
  apply stepStar_trans (r1r1r2_chain n 1 0 0 (e + n + 1) f)
  rw [show (0 : ℕ) + n = n from by ring, show (0 : ℕ) + 2 * n = 2 * n from by ring]
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
      show e + n + 1 = e + (n + 1) from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  rw [show 1 + 2 * n = 1 + 2 * n from rfl]
  convert r2_drain (n + 1) 1 0 (1 + 2 * n) e f using 2; ring_nf

theorem full_transition : ∀ d e F,
    ⟨0, 0, 0, d + 1, e + d + 2, F⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 4, e + 2 * d + 6, F + d⟩ := by
  intro d e F
  -- Phase 1: R4 drain d+1 times
  apply stepStar_stepPlus_stepPlus
  · rw [show d + 1 = 0 + (d + 1) from by ring]
    exact r4_drain (d + 1) 0 0 F
  -- Phase 2: R5 once
  show ⟨0, 0 + (d + 1), 0, 0, e + d + 2, F + (d + 1)⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
      show F + (d + 1) = (F + d) + 1 from by ring]
  step fm
  -- Phase 3: R2 once
  show ⟨0, d + 1, 1, 0, e + d + 2, F + d⟩ [fm]⊢* _
  rw [show e + d + 2 = (e + d + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Phase 4: chain
  show ⟨2, d + 1, 0, 0, e + d + 1, F + d⟩ [fm]⊢* _
  rw [show e + d + 1 = e + (d + 1) from by ring]
  rcases Nat.even_or_odd (d + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; rw [hK]
    apply stepStar_trans (chain_even K e (F + d))
    rw [show 2 * K + 2 = 0 + (2 * K + 2) from by ring]
    apply stepStar_trans (r3_drain (2 * K + 2) 0 (2 * K) e)
    rw [← hK]; ring_nf; finish
  · rw [hK]
    apply stepStar_trans (chain_odd K e (F + d))
    rw [show 2 * K + 3 = 0 + (2 * K + 3) from by ring]
    apply stepStar_trans (r3_drain (2 * K + 3) 0 (2 * K + 1) e)
    have hd : d = 2 * K := by omega
    rw [hd]; ring_nf; finish

-- Canonical state: C(d, e, F) = (0, 0, 0, d+1, e+d+2, F)
-- Transition: (d, e, F) → (2d+3, e+1, F+d)
-- Verify: C(2d+3, e+1, F+d) = (0, 0, 0, 2d+4, (e+1)+(2d+3)+2, F+d) = (0, 0, 0, 2d+4, e+2d+6, F+d)
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1 + 1, p.2.1 + p.1 + 2, p.2.2⟩) ⟨0, 0, 0⟩
  intro ⟨d, e, F⟩
  refine ⟨⟨2 * d + 3, e + 1, F + d⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, e + d + 2, F⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 3 + 1, e + 1 + (2 * d + 3) + 2, F + d⟩
  rw [show 2 * d + 3 + 1 = 2 * d + 4 from by ring,
      show e + 1 + (2 * d + 3) + 2 = e + 2 * d + 6 from by ring]
  exact full_transition d e F
