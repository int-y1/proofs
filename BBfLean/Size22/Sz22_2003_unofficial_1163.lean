import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1163: [5/6, 44/35, 91/2, 3/11, 275/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1163

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+2, d, e+1, f⟩
  | _ => none

-- R3 repeated: drain a to d and f.
theorem r3_drain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e (f + 1))
    ring_nf; finish

-- R4 repeated: drain e to b.
theorem r4_drain : ∀ k, ∀ b d e f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R2 chain: b=0, R2 fires repeatedly.
theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1) f)
    ring_nf; finish

-- R2 chain specialized: d starts at 0.
theorem r2_chain' : ∀ d, ∀ a c e f, ⟨a, 0, c + d, d, e, f⟩ [fm]⊢* ⟨a + 2 * d, 0, c, 0, e + d, f⟩ := by
  intro d; induction' d with d ih <;> intro a c e f
  · exists 0
  · rw [show c + (d + 1) = (c + d) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) c (e + 1) f)
    ring_nf; finish

-- One round of R2+R1+R1.
theorem r2r1r1_once : ⟨0, b + 2, c + 1, d + 1, e, f⟩ [fm]⊢* ⟨0, b, c + 2, d, e + 1, f⟩ := by
  step fm; step fm; step fm; finish

-- R2+R1+R1 loop.
theorem r2r1r1_loop : ∀ k, ∀ b c d e f,
    ⟨0, b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢* ⟨0, b, c + 1 + k, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (r2r1r1_once (b := b + 2 * k) (c := c) (d := d + k) (e := e) (f := f))
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d (e + 1) f)
    ring_nf; finish

-- R3+R2 tail: alternating R3 then R2 when d=0.
theorem r3r2_tail : ∀ k, ∀ a e f, ⟨a + 1, 0, k, 0, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Full transition: (2n+3, 0, 0, 0, 3n+3, f) →⁺ (2n+5, 0, 0, 0, 3n+6, f+3n+4)
-- Split by parity of n.

-- n even (n=2m): n'=n+1=2m+1 is odd.
-- Phase 1: R3 drain. Phase 2: R4 drain. Phase 3: R5.
-- Phase 4: middle_odd. Phase 5: R3+R2 tail.
theorem main_trans_even (m : ℕ) :
    ⟨4 * m + 3, 0, 0, 0, 6 * m + 3, f⟩ [fm]⊢⁺ ⟨4 * m + 5, 0, 0, 0, 6 * m + 6, f + 6 * m + 4⟩ := by
  -- First step: R3
  rw [show (4 : ℕ) * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  -- State: (4m+2, 0, 0, 1, 6m+3, f+1)
  -- R3 drain remaining 4m+2 steps
  rw [show (4 : ℕ) * m + 2 = 0 + (4 * m + 2) from by ring]
  apply stepStar_trans (r3_drain (4 * m + 2) 0 1 (6 * m + 3) (f + 1))
  rw [show 1 + (4 * m + 2) = 4 * m + 3 from by ring,
      show f + 1 + (4 * m + 2) = f + 4 * m + 3 from by ring]
  -- State: (0, 0, 0, 4m+3, 6m+3, f+4m+3)
  -- R4 drain
  rw [show (6 : ℕ) * m + 3 = 0 + (6 * m + 3) from by ring]
  apply stepStar_trans (r4_drain (6 * m + 3) 0 (4 * m + 3) 0 (f + 4 * m + 3))
  rw [show 0 + (6 * m + 3) = 6 * m + 3 from by ring]
  -- State: (0, 6m+3, 0, 4m+3, 0, f+4m+3)
  -- R5
  rw [show f + 4 * m + 3 = (f + 4 * m + 2) + 1 from by ring]
  step fm
  -- State: (0, 6m+3, 2, 4m+3, 1, f+4m+2)
  -- Middle phase (odd n'=2m+1)
  -- R2+R1+R1 loop with k=3m+1, b=1
  rw [show (6 : ℕ) * m + 3 = 1 + 2 * (3 * m + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show (4 : ℕ) * m + 3 = (m + 2) + (3 * m + 1) from by ring]
  apply stepStar_trans (r2r1r1_loop (3 * m + 1) 1 1 (m + 2) 1 (f + 4 * m + 2))
  rw [show 1 + 1 + (3 * m + 1) = 3 * m + 3 from by ring,
      show 1 + (3 * m + 1) = 3 * m + 2 from by ring]
  -- State: (0, 1, 3m+3, m+2, 3m+2, f+4m+2)
  -- R2+R1
  rw [show (3 : ℕ) * m + 3 = (3 * m + 2) + 1 from by ring,
      show m + 2 = (m + 1) + 1 from by ring]
  step fm  -- R2: (2, 1, 3m+2, m+1, 3m+3, f+4m+2)
  step fm  -- R1: (1, 0, 3m+3, m+1, 3m+3, f+4m+2)
  -- State: (1, 0, 3m+3, m+1, 3m+3, f+4m+2)
  -- R2 chain' with d=m+1
  rw [show (3 : ℕ) * m + 3 = (2 * m + 2) + (m + 1) from by ring]
  apply stepStar_trans (r2_chain' (m + 1) 1 (2 * m + 2) ((2 * m + 2) + (m + 1)) (f + 4 * m + 2))
  -- State: (2m+3, 0, 2m+2, 0, 4m+4, f+4m+2) up to ring normalization
  -- R3+R2 tail with k=2m+2
  rw [show 1 + 2 * (m + 1) = (2 * m + 2) + 1 from by ring,
      show (2 * m + 2) + (m + 1) + (m + 1) = 4 * m + 4 from by ring]
  apply stepStar_trans (r3r2_tail (2 * m + 2) (2 * m + 2) (4 * m + 4) (f + 4 * m + 2))
  ring_nf; finish

-- n odd (n=2m+1): n'=n+1=2m+2=2(m+1) is even.
theorem main_trans_odd (m : ℕ) :
    ⟨4 * m + 5, 0, 0, 0, 6 * m + 6, f⟩ [fm]⊢⁺ ⟨4 * m + 7, 0, 0, 0, 6 * m + 9, f + 6 * m + 7⟩ := by
  -- First step: R3
  rw [show (4 : ℕ) * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm
  -- R3 drain remaining 4m+4 steps
  rw [show (4 : ℕ) * m + 4 = 0 + (4 * m + 4) from by ring]
  apply stepStar_trans (r3_drain (4 * m + 4) 0 1 (6 * m + 6) (f + 1))
  rw [show 1 + (4 * m + 4) = 4 * m + 5 from by ring,
      show f + 1 + (4 * m + 4) = f + 4 * m + 5 from by ring]
  -- State: (0, 0, 0, 4m+5, 6m+6, f+4m+5)
  -- R4 drain
  rw [show (6 : ℕ) * m + 6 = 0 + (6 * m + 6) from by ring]
  apply stepStar_trans (r4_drain (6 * m + 6) 0 (4 * m + 5) 0 (f + 4 * m + 5))
  rw [show 0 + (6 * m + 6) = 6 * m + 6 from by ring]
  -- State: (0, 6m+6, 0, 4m+5, 0, f+4m+5)
  -- R5
  rw [show f + 4 * m + 5 = (f + 4 * m + 4) + 1 from by ring]
  step fm
  -- State: (0, 6m+6, 2, 4m+5, 1, f+4m+4)
  -- Middle phase (even n'=2(m+1))
  -- R2+R1+R1 loop with k=3(m+1)=3m+3, b=0
  rw [show (6 : ℕ) * m + 6 = 0 + 2 * (3 * m + 3) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show (4 : ℕ) * m + 5 = (m + 2) + (3 * m + 3) from by ring]
  apply stepStar_trans (r2r1r1_loop (3 * m + 3) 0 1 (m + 2) 1 (f + 4 * m + 4))
  rw [show 1 + 1 + (3 * m + 3) = 3 * m + 5 from by ring,
      show 1 + (3 * m + 3) = 3 * m + 4 from by ring]
  -- State: (0, 0, 3m+5, m+2, 3m+4, f+4m+4)
  -- R2 chain' with d=m+2
  rw [show (3 : ℕ) * m + 5 = (2 * m + 3) + (m + 2) from by ring]
  apply stepStar_trans (r2_chain' (m + 2) 0 (2 * m + 3) (3 * m + 4) (f + 4 * m + 4))
  rw [show 0 + 2 * (m + 2) = 2 * m + 4 from by ring,
      show 3 * m + 4 + (m + 2) = 4 * m + 6 from by ring]
  -- State: (2m+4, 0, 2m+3, 0, 4m+6, f+4m+4)
  -- R3+R2 tail with k=2m+3
  rw [show (2 : ℕ) * m + 4 = (2 * m + 3) + 1 from by ring]
  apply stepStar_trans (r3r2_tail (2 * m + 3) (2 * m + 3) (4 * m + 6) (f + 4 * m + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 3, 1⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨2 * n + 3, 0, 0, 0, 3 * n + 3, f⟩) ⟨0, 1⟩
  intro ⟨n, f⟩
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    refine ⟨⟨2 * m + 1, f + 6 * m + 4⟩, ?_⟩
    simp only []
    rw [show 2 * (m + m) + 3 = 4 * m + 3 from by ring,
        show 3 * (m + m) + 3 = 6 * m + 3 from by ring,
        show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 3 * (2 * m + 1) + 3 = 6 * m + 6 from by ring]
    exact main_trans_even m
  · subst hm
    refine ⟨⟨2 * m + 2, f + 6 * m + 7⟩, ?_⟩
    simp only []
    rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 3 * (2 * m + 1) + 3 = 6 * m + 6 from by ring,
        show 2 * (2 * m + 2) + 3 = 4 * m + 7 from by ring,
        show 3 * (2 * m + 2) + 3 = 6 * m + 9 from by ring]
    exact main_trans_odd m
