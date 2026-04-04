import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1755: [9/10, 2/21, 539/2, 25/77, 2/5]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  0
-1  0  0  2  1
 0  0  2 -1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1755

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Phase 1: R4 drain. (0, 0, c, d+k, k) →* (0, 0, c+2*k, d, 0).
-- When a=0, b=0, c≥0, d≥1, e≥1: R4 fires.
theorem r4_drain : ∀ k, ∀ c d, ⟨0, 0, c, d + k, k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 2) d)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]
    finish

-- Phase 2a: Opening steps. (0, 0, c+2, 1, 0) →* (1, 1, c, 0, 0).
-- R5: (1, 0, c+1, 1, 0). R1: (0, 2, c, 1, 0). R2: (1, 1, c, 0, 0).
theorem opening : ⟨0, 0, c + 2, 1, 0⟩ [fm]⊢* ⟨1, 1, c, 0, 0⟩ := by
  step fm; step fm; step fm; finish

-- Phase 2b: R1+R5 chain. (1, b, 2*k, 0, 0) →* (1, b+2*k, 0, 0, 0).
-- Each round: R1 gives (0, b+2, 2*k-1, 0, 0), R5 gives (1, b+2, 2*k-2, 0, 0).
theorem r1r5_chain : ∀ k, ∀ b, ⟨1, b, 2 * k, 0, 0⟩ [fm]⊢* ⟨1, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 2))
    rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring]
    finish

-- Phase 2 combined: (0, 0, 2*(k+1), 1, 0) →* (1, 2*k+1, 0, 0, 0).
theorem c_to_b : ∀ k, ⟨0, 0, 2 * (k + 1), 1, 0⟩ [fm]⊢* ⟨1, 2 * k + 1, 0, 0, 0⟩ := by
  intro k
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  apply stepStar_trans (opening (c := 2 * k))
  apply stepStar_trans (r1r5_chain k (b := 1))
  rw [show 1 + 2 * k = 2 * k + 1 from by ring]
  finish

-- Phase 3: b-drain rounds. (a+1, 2*j+3, 0, 0, e) →* (a+j+2, 1, 0, 0, e+j+1).
-- Each round: R3 (a-=1, d+=2, e+=1), R2, R2 (a+=2, b-=2, d-=2). Net: a+=1, b-=2, e+=1.
theorem b_drain_rounds : ∀ j, ∀ a e, ⟨a + 1, 2 * j + 3, 0, 0, e⟩ [fm]⊢* ⟨a + j + 2, 1, 0, 0, e + j + 1⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · step fm; step fm; step fm; finish
  · rw [show 2 * (j + 1) + 3 = (2 * j + 3) + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    rw [show a + 1 + j + 2 = a + (j + 1) + 2 from by ring,
        show e + 1 + j + 1 = e + (j + 1) + 1 from by ring]
    finish

-- Phase 3 final: (a+1, 1, 0, 0, e) →* (a+1, 0, 0, 1, e+1).
-- R3: (a, 1, 0, 2, e+1). R2: (a+1, 0, 0, 1, e+1).
theorem b_drain_final : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 1, 0, 0, 1, e + 1⟩ := by
  step fm; step fm; finish

-- Phase 3 combined: (1, 2*k+1, 0, 0, 0) →* (k+1, 0, 0, 1, k+1).
theorem b_drain : ∀ k, ⟨1, 2 * k + 1, 0, 0, 0⟩ [fm]⊢* ⟨k + 1, 0, 0, 1, k + 1⟩ := by
  intro k
  rcases k with _ | k
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
    apply stepStar_trans (b_drain_rounds k (a := 0) (e := 0))
    rw [show 0 + k + 2 = k + 1 + 1 from by ring, show 0 + k + 1 = k + 1 from by ring]
    exact b_drain_final

-- Phase 4: R3 drain. (a+k, 0, 0, d, e) →* (a, 0, 0, d+2*k, e+k).
-- Each R3: a-=1, d+=2, e+=1.
theorem r3_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 1))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, 2*n+3, 2*n+2) →⁺ (0, 0, 0, 4*n+5, 4*n+4).
theorem main_trans : ∀ n, ⟨0, 0, 0, 2 * n + 3, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 5, 4 * n + 4⟩ := by
  intro n
  -- Phase 1: R4 drain with k = 2*n+2, d = 1.
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * n + 3 = 1 + (2 * n + 2) from by ring]
    exact r4_drain (2 * n + 2) 0 1
  -- Phase 2: c_to_b.
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (2 * n + 2) = 2 * ((2 * n + 1) + 1) from by ring]
    apply stepStar_trans (c_to_b (2 * n + 1))
    finish
  -- Phase 3: b_drain.
  apply stepStar_stepPlus_stepPlus
  · exact b_drain (2 * n + 1)
  -- Phase 4: R3 drain from ((2*n+1)+1, 0, 0, 1, (2*n+1)+1).
  show ⟨(2 * n + 1) + 1, 0, 0, 1, (2 * n + 1) + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 5, 4 * n + 4⟩
  have h4 : ⟨0 + ((2 * n + 1) + 1), 0, 0, 1, (2 * n + 1) + 1⟩ [fm]⊢*
             ⟨0, 0, 0, 1 + 2 * ((2 * n + 1) + 1), (2 * n + 1) + 1 + ((2 * n + 1) + 1)⟩ :=
    r3_drain ((2 * n + 1) + 1) 0 1 ((2 * n + 1) + 1)
  rw [show (0 : ℕ) + ((2 * n + 1) + 1) = (2 * n + 1) + 1 from by ring,
      show 1 + 2 * ((2 * n + 1) + 1) = 4 * n + 5 from by ring,
      show (2 * n + 1) + 1 + ((2 * n + 1) + 1) = 4 * n + 4 from by ring] at h4
  exact stepStar_stepPlus h4 (by intro h; injection h with h; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 3, 2 * n + 2⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  rw [show 2 * (2 * n + 1) + 3 = 4 * n + 5 from by ring,
      show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
  exact main_trans n
