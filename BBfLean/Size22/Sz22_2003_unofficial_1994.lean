import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1994: [99/35, 5/6, 4/5, 7/11, 275/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1994

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r1_chain : ∀ k, ⟨a, b, c + k, d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨a + k, b + k, c, 0, e⟩ [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r2r1_drain : ∀ k, ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    step fm
    show ⟨a + k, b + 1 + 1, 0, k, e + 1⟩ [fm]⊢* _
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- Full transition from canonical state to next.
-- (3n+4, 0, 0, 0, n+1) →⁺ (3n+7, 0, 0, 0, n+2)
theorem main_trans : ∀ n, ⟨3 * n + 4, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨3 * n + 7, 0, 0, 0, n + 2⟩ := by
  intro n
  -- Phase 1: R4 x (n+1)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_d (n + 1) (a := 3 * n + 4) (d := 0) (e := 0))
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- Phase 2: R5
  apply step_stepStar_stepPlus
  · show fm ⟨(3 * n + 3) + 1, 0, 0, n + 1, 0⟩ = some ⟨3 * n + 3, 0, 2, n + 1, 1⟩
    simp [fm]
  -- Phase 3: R1 x 2 (c=2, d=n+1>=1)
  rcases n with _ | m
  · -- n = 0: (3, 0, 2, 1, 1). R1 x 1 then R2 x 2 then R3 x 3.
    execute fm 6
  · -- n >= 1: R1 x 2 possible since d = m+2 >= 2
    -- (3m+6, 0, 2, m+2, 1)
    rw [show 3 * (m + 1) + 3 = 3 * m + 6 from by ring,
        show m + 1 + 1 = m + 2 from by ring,
        show (2 : ℕ) = 0 + 2 from by ring,
        show m + 2 = m + 2 from rfl]
    apply stepStar_trans (r1_chain 2 (a := 3 * m + 6) (b := 0) (c := 0) (d := m) (e := 1))
    -- At (3m+6, 4, 0, m, 3)
    rw [show 0 + 2 * 2 = 4 from by ring,
        show 1 + 2 = 3 from by ring]
    -- R2+R1 drain: m rounds
    rw [show 3 * m + 6 = (2 * m + 6) + m from by ring,
        show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (r2r1_drain m (a := 2 * m + 6) (b := 3) (e := 3))
    -- At (2m+6, m+4, 0, 0, m+3)
    -- R2 x (m+4): drain b into c
    have h1 : ⟨2 * m + 6, 3 + 1 + m, 0, 0, 3 + m⟩ =
              (⟨(m + 2) + (m + 4), 0 + (m + 4), 0, 0, m + 3⟩ : Q) := by ring_nf
    rw [h1]
    apply stepStar_trans (r2_chain (m + 4) (a := m + 2) (b := 0) (c := 0) (e := m + 3))
    -- At (m+2, 0, m+4, 0, m+3)
    apply stepStar_trans (r3_chain (m + 4) (a := m + 2) (c := 0) (e := m + 3))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨3 * n + 4, 0, 0, 0, n + 1⟩) 0
  intro n; exists n + 1; exact main_trans n
