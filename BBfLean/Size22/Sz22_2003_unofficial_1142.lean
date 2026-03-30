import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1142: [5/6, 44/35, 49/2, 9/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1142

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

theorem r4_chain : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ n, ∀ k d,
    ⟨0, 2 * n + 2, k + 1, d + n + 1, k + 1⟩ [fm]⊢* ⟨0, 0, k + n + 2, d, k + n + 2⟩ := by
  intro n; induction' n with n ih <;> intro k d
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 1 + 1 from by ring,
        show d + (n + 1) + 1 = (d + n + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (k + 1) d)
    ring_nf; finish

theorem r2_chain : ∀ m, ∀ a c e, ⟨a, 0, c + m, m, e⟩ [fm]⊢* ⟨a + 2 * m, 0, c, 0, e + m⟩ := by
  intro m; induction' m with m ih <;> intro a c e
  · exists 0
  · rw [show c + (m + 1) = (c + m) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (e + 1))
    ring_nf; finish

theorem r3r2r2_chain : ∀ j, ∀ a e,
    ⟨a + 1, 0, 2 * j + 2, 0, e⟩ [fm]⊢* ⟨a + 3 * j + 4, 0, 0, 0, e + 2 * j + 2⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (j + 1) + 2 = (2 * j + 2) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 2))
    ring_nf; finish

theorem main_transition (d p : ℕ) :
    ⟨d + p + 2, 0, 0, 0, d + 2 * p + 2⟩ [fm]⊢⁺ ⟨2 * d + 3 * p + 5, 0, 0, 0, 2 * d + 4 * p + 6⟩ := by
  -- Phase 1: first R3 step (explicit for stepPlus).
  rw [show d + p + 2 = (d + p + 1) + 1 from by ring]
  step fm
  -- Now at (d+p+1, 0, 0, 2, d+2p+2). Continue R3 chain.
  rw [show d + p + 1 = 0 + (d + p + 1) from by ring]
  apply stepStar_trans (r3_chain (d + p + 1) 0 2 (d + 2 * p + 2))
  -- Now at (0, 0, 0, 2+2*(d+p+1), d+2p+2) = (0, 0, 0, 2d+2p+4, d+2p+2).
  rw [show 2 + 2 * (d + p + 1) = 2 * d + 2 * p + 4 from by ring,
      show d + 2 * p + 2 = 0 + (d + 2 * p + 2) from by ring]
  -- Phase 2: R4 chain.
  apply stepStar_trans (r4_chain (d + 2 * p + 2) 0 (2 * d + 2 * p + 4) 0)
  rw [show 0 + 2 * (d + 2 * p + 2) = 2 * d + 4 * p + 4 from by ring]
  -- Now at (0, 2d+4p+4, 0, 2d+2p+4, 0).
  -- Phase 3: R5, R2, R1, R1.
  rw [show 2 * d + 2 * p + 4 = (2 * d + 2 * p + 2) + 1 + 1 from by ring,
      show 2 * d + 4 * p + 4 = (2 * d + 4 * p + 2) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  -- Now at (0, 2d+4p+2, 2, 2d+2p+2, 2).
  -- Phase 4: R2R1R1 chain.
  rw [show 2 * d + 4 * p + 2 = 2 * (d + 2 * p) + 2 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * d + 2 * p + 2 = (d + 1) + (d + 2 * p) + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain (d + 2 * p) 1 (d + 1))
  -- Now at (0, 0, 1+(d+2p)+2, d+1, 1+(d+2p)+2).
  -- Phase 5: R2 chain.
  rw [show 1 + (d + 2 * p) + 2 = (2 * p + 2) + (d + 1) from by ring]
  apply stepStar_trans (r2_chain (d + 1) 0 (2 * p + 2) ((2 * p + 2) + (d + 1)))
  -- Now at (2d+2, 0, 2p+2, 0, (2p+2)+(d+1)+(d+1)).
  -- Phase 6: R3R2R2 chain.
  rw [show 0 + 2 * (d + 1) = (2 * d + 1) + 1 from by ring,
      show (2 * p + 2) + (d + 1) + (d + 1) = 2 * d + 2 * p + 4 from by ring]
  apply stepStar_trans (r3r2r2_chain p (2 * d + 1) (2 * d + 2 * p + 4))
  rw [show 2 * d + 1 + 3 * p + 4 = 2 * d + 3 * p + 5 from by ring,
      show 2 * d + 2 * p + 4 + 2 * p + 2 = 2 * d + 4 * p + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d p, q = ⟨d + p + 2, 0, 0, 0, d + 2 * p + 2⟩)
  · intro c ⟨d, p, hq⟩; subst hq
    exact ⟨⟨2 * d + 3 * p + 5, 0, 0, 0, 2 * d + 4 * p + 6⟩,
      ⟨2 * d + 2 * p + 2, p + 1, by ring_nf⟩,
      main_transition d p⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1142
