import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #731: [35/6, 4/55, 143/2, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_731

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show (k + 1) = k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d f, ⟨a, 0, c + k, d, k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k + 1) = (k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d f)
    ring_nf; finish

theorem r1r1r2_cycle : ∀ k, ∀ c d e f, ⟨2, 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r1r1r2_cycle_rem1 : ∀ k, ∀ c d e f, ⟨2, 2 * k + 1, c, d, e + k, f⟩ [fm]⊢* ⟨2, 1, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

-- Phase: R3(n+1) + R4(n) + R5 + R2
-- (n+1, 0, 0, n, 0, f) ⊢⁺ (2, n, 0, 1, n, f+n)
theorem phase1 (n f : ℕ) :
    ⟨n + 1, 0, 0, n, 0, f⟩ [fm]⊢⁺ ⟨2, n, 0, 1, n, f + n⟩ := by
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply step_stepStar_stepPlus
  · -- R3 first step: (n+1, 0, 0, n, 0, f) -> (n, 0, 0, n, 1, f+1)
    show fm ⟨0 + (n + 1), 0, 0, n, 0, f⟩ = some ⟨0 + n, 0, 0, n, 1, f + 1⟩
    simp [fm]
  -- R3 remaining n steps: (n, 0, 0, n, 1, f+1) ⊢* (0, 0, 0, n, n+1, f+n+1)
  apply stepStar_trans (r3_chain n 0 n 1 (f + 1))
  -- R4 n steps: (0, 0, 0, n, n+1, f+n+1) ⊢* (0, n, 0, 0, n+1, f+n+1)
  rw [show 1 + n = n + 1 from by ring, show f + 1 + n = f + n + 1 from by ring]
  apply stepStar_trans (r4_chain n 0 (n + 1) (f + n + 1))
  rw [show 0 + n = n from by ring]
  -- R5: (0, n, 0, 0, n+1, f+n+1) -> (0, n, 1, 1, n+1, f+n)
  rw [show f + n + 1 = (f + n) + 1 from by ring, show n + 1 = n + 1 from rfl]
  step fm
  -- R2: (0, n, 1, 1, n+1, f+n) -> (2, n, 0, 1, n, f+n)
  step fm; ring_nf; finish

-- Even drain: (2, 2k, 0, 1, 2k, F) ⊢* (2k+2, 0, 0, 2k+1, 0, F)
theorem drain_even (k F : ℕ) :
    ⟨2, 2 * k, 0, 1, 2 * k, F⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, 2 * k + 1, 0, F⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, 0 + k, 1 + 2 * k, k, F⟩)
  · convert r1r1r2_cycle k 0 1 k F using 2; ring_nf
  apply stepStar_trans (r2_chain k 2 0 (1 + 2 * k) F)
  ring_nf; finish

-- Odd drain: (2, 2k+1, 0, 1, 2k+1, F) ⊢* (2k+3, 0, 0, 2k+2, 0, F)
theorem drain_odd (k F : ℕ) :
    ⟨2, 2 * k + 1, 0, 1, 2 * k + 1, F⟩ [fm]⊢* ⟨2 * k + 3, 0, 0, 2 * k + 2, 0, F⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 1, 0 + k, 1 + 2 * k, k + 1, F⟩)
  · convert r1r1r2_cycle_rem1 k 0 1 (k + 1) F using 2; ring_nf
  step fm
  apply stepStar_trans (c₂ := ⟨1 + 2 * (k + 1), 0, 0, 1 + 2 * k + 1, 0, F⟩)
  · exact r2_chain (k + 1) 1 0 (1 + 2 * k + 1) F
  ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨n + 1, 0, 0, n, 0, f⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, 0, f + n⟩ := by
  apply stepPlus_stepStar_stepPlus (phase1 n f)
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact drain_even k (f + 2 * k)
  · subst hk
    exact drain_odd k (f + (2 * k + 1))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨n + 1, 0, 0, n, 0, f⟩) ⟨1, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n⟩, main_trans n f⟩

end Sz22_2003_unofficial_731
