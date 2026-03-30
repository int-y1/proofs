import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #768: [35/6, 52/55, 143/2, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  1
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_768

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ a d e f,
    ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a d (e + 1) (f + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ b d e f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e f); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c d e f,
    ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) c d e (f + 1)); ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b j d e f,
    ⟨2, b + 2 * k, j, d, e + k, f⟩ [fm]⊢* ⟨2, b, j + k, d + 2 * k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b j d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (j + 1) (d + 2) e (f + 1)); ring_nf; finish

-- Combined opening: R3 drain + R4 drain + R5 + R2
-- (n+2, 0, 0, n+1, 0, F) →⁺ (2, n+2, 0, 0, n+1, F+n+2)
theorem opening : ∀ n F,
    ⟨n + 2, 0, 0, n + 1, 0, F⟩ [fm]⊢⁺ ⟨2, n + 2, 0, 0, n + 1, F + n + 2⟩ := by
  intro n F
  -- R3 drain n+2 steps: (n+2, 0, 0, n+1, 0, F) →* (0, 0, 0, n+1, n+2, F+n+2)
  apply stepStar_stepPlus_stepPlus
  · rw [show n + 2 = 0 + (n + 2) from by ring]
    exact r3_drain (n + 2) 0 (n + 1) 0 F
  -- R4 drain n+1 steps: (0, 0, 0, n+1, n+2, F+n+2) →* (0, n+1, 0, 0, n+2, F+n+2)
  apply stepStar_stepPlus_stepPlus
  · rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
        show n + 1 = 0 + (n + 1) from by ring]
    exact r4_drain (n + 1) 0 0 (n + 2) (F + (n + 2))
  -- R5: (0, n+1, 0, 0, n+2, F+n+2) → (0, n+2, 1, 0, n+2, F+n+1)
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring,
      show F + (n + 2) = F + (n + 1) + 1 from by ring]
  step fm
  -- R2: (0, n+2, 1, 0, n+2, F+n+1) → (2, n+2, 0, 0, n+1, F+n+2)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  show ⟨2, n + 1 + 1, 0, 0, n + 1, F + (n + 1) + 1⟩ [fm]⊢* _
  ring_nf; finish

-- Combined tail: R2 drain (m+1) + R3 + R2
-- (a, 0, m+2, D, m+1, G) →* (a+2m+3, 0, 0, D, 0, G+m+3)
theorem r2_tail : ∀ m a D G,
    ⟨a, 0, m + 2, D, m + 1, G⟩ [fm]⊢* ⟨a + 2 * m + 3, 0, 0, D, 0, G + m + 3⟩ := by
  intro m a D G
  rw [show m + 2 = 1 + (m + 1) from by ring]
  have h := r2_drain (m + 1) a 1 D 0 G
  rw [show (0 : ℕ) + (m + 1) = m + 1 from by ring] at h
  apply stepStar_trans h
  rw [show a + 2 * (m + 1) = (a + 2 * m + 1) + 1 from by ring]
  step fm; step fm; ring_nf; finish

-- Even case: from state after opening with n=2m
-- (2, 2m+2, 0, 0, 2m+1, G) →* (2m+3, 0, 0, 2m+2, 0, G+2m+3)
theorem chain_even : ∀ m G,
    ⟨2, 2 * m + 2, 0, 0, 2 * m + 1, G⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, G + 2 * m + 3⟩ := by
  intro m G
  rw [show 2 * m + 2 = 2 + 2 * m from by ring,
      show 2 * m + 1 = (m + 1) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 2 0 0 (m + 1) G)
  show ⟨2, 2, 0 + m, 0 + 2 * m, m + 1, G + m⟩ [fm]⊢* _
  rw [show (0 : ℕ) + m = m from by ring, show (0 : ℕ) + 2 * m = 2 * m from by ring]
  step fm; step fm
  apply stepStar_trans (r2_tail m 0 (2 * m + 2) (G + m))
  ring_nf; finish

-- Odd case: from state after opening with n=2m+1
-- (2, 2m+3, 0, 0, 2m+2, G) →* (2m+4, 0, 0, 2m+3, 0, G+2m+4)
theorem chain_odd : ∀ m G,
    ⟨2, 2 * m + 3, 0, 0, 2 * m + 2, G⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 2 * m + 3, 0, G + 2 * m + 4⟩ := by
  intro m G
  rw [show 2 * m + 3 = 3 + 2 * m from by ring,
      show 2 * m + 2 = (m + 2) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 3 0 0 (m + 2) G)
  show ⟨2, 3, 0 + m, 0 + 2 * m, m + 2, G + m⟩ [fm]⊢* _
  rw [show (0 : ℕ) + m = m from by ring, show (0 : ℕ) + 2 * m = 2 * m from by ring]
  step fm; step fm
  rw [show m + 2 = (m + 1) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (r2_tail m 1 (2 * m + 3) (G + m + 1))
  ring_nf; finish

-- Full transition: C(n) →⁺ C(n+1)
-- C(n) = (n+2, 0, 0, n+1, 0, (n+1)*(n+3))
theorem full_transition : ∀ n,
    ⟨n + 2, 0, 0, n + 1, 0, (n + 1) * (n + 3)⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, n + 2, 0, (n + 2) * (n + 4)⟩ := by
  intro n
  apply stepPlus_stepStar_stepPlus (opening n ((n + 1) * (n + 3)))
  -- State: (2, n+2, 0, 0, n+1, (n+1)*(n+3)+n+2)
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    show ⟨2, 2 * m + 2, 0, 0, 2 * m + 1, (2 * m + 1) * (2 * m + 3) + 2 * m + 2⟩ [fm]⊢* _
    apply stepStar_trans (chain_even m ((2 * m + 1) * (2 * m + 3) + 2 * m + 2))
    ring_nf; finish
  · subst hm
    show ⟨2, 2 * m + 1 + 2, 0, 0, 2 * m + 1 + 1,
      (2 * m + 1 + 1) * (2 * m + 1 + 3) + 2 * m + 1 + 2⟩ [fm]⊢* _
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show (2 * m + 1 + 1) * (2 * m + 1 + 3) + 2 * m + 1 + 2
           = (2 * m + 2) * (2 * m + 4) + 2 * m + 3 from by ring]
    apply stepStar_trans (chain_odd m ((2 * m + 2) * (2 * m + 4) + 2 * m + 3))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0, (n + 1) * (n + 3)⟩) 0
  intro n; exact ⟨n + 1, full_transition n⟩
