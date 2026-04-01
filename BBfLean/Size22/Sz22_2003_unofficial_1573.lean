import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1573: [7/45, 275/14, 22/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
-1  0  2 -1  1
 1  0 -1  0  1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1573

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to b.
theorem e_to_b : ∀ k b, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro b; exists 0
  · intro b; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih (b + 1)); ring_nf; finish

-- R3 chain: drain c, building a and e.
theorem r3_chain : ∀ k a e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- R3-R2 alternation: (0, 0, c+1, d+k, e) -> (0, 0, c+k+1, d, e+2k).
theorem r3r2_chain : ∀ k c d e, ⟨0, 0, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 2)); ring_nf; finish

-- R1-R1-R2 loop: (k, 4k+2, 2, d, e) -> (0, 2, 2, d+k, e+k).
theorem r1r1r2_loop : ∀ k d e, ⟨k, 4 * k + 2, 2, d, e⟩ [fm]⊢* ⟨0, 2, 2, d + k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show 4 * (k + 1) + 2 = (4 * k + 2) + 4 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- Tail phase: (0, 2, 2, d, e) ⊢⁺ (d+2, 0, 0, 0, e+3d+4).
theorem tail_phase (d e : ℕ) :
    ⟨0, 2, 2, d, e⟩ [fm]⊢⁺ ⟨d + 2, 0, 0, 0, e + 3 * d + 4⟩ := by
  -- R1: (0, 2, 2, d, e) -> (0, 0, 1, d+1, e)
  step fm
  -- R3: (0, 0, 1, d+1, e) -> (1, 0, 0, d+1, e+1)
  step fm
  -- R2: (1, 0, 0, d+1, e+1) -> (0, 0, 2, d, e+2)
  rw [show d + 1 = d + 1 from rfl]
  step fm
  -- Now at (0, 0, 2, d, e+2) = (0, 0, 1+1, 0+d, e+2)
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show e + 1 + 1 = e + 2 from by ring,
      show (d : ℕ) = 0 + d from by ring]
  apply stepStar_trans (r3r2_chain d 1 0 (e + 2))
  rw [show 1 + d + 1 = d + 2 from by ring,
      show e + 2 + 2 * d = 2 * d + e + 2 from by ring,
      show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
  apply stepStar_trans (r3_chain (d + 2) 0 (2 * d + e + 2) (c := 0))
  ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 4n+4) ⊢⁺ (n+3, 0, 0, 0, 4n+8).
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 4 * n + 8⟩ := by
  -- e_to_b: (n+2, 0, 0, 0, 4n+4) -> (n+2, 4n+4, 0, 0, 0)
  rw [show (4 * n + 4 : ℕ) = 0 + (4 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (4 * n + 4) 0 (a := n + 2) (e := 0))
  rw [show 0 + (4 * n + 4) = 4 * n + 4 from by ring]
  -- R5: (n+2, 4n+4, 0, 0, 0) -> (n+1, 4n+4, 1, 1, 0)
  step fm
  -- R1: (n+1, 4n+4, 1, 1, 0) -> (n+1, 4n+2, 0, 2, 0)
  rw [show 4 * n + 4 = (4 * n + 2) + 2 from by ring]
  step fm
  -- R2: (n+1, 4n+2, 0, 2, 0) -> (n, 4n+2, 2, 1, 1)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- R1-R1-R2 loop: (n, 4n+2, 2, 1, 1) -> (0, 2, 2, n+1, n+1)
  rw [show 4 * n + 1 + 1 = 4 * n + 2 from by ring]
  apply stepStar_trans (r1r1r2_loop n 1 1)
  rw [show 1 + n = n + 1 from by ring]
  -- tail_phase: (0, 2, 2, n+1, n+1) -> (n+3, 0, 0, 0, 4n+8)
  have h := tail_phase (n + 1) (n + 1)
  rw [show n + 1 + 2 = n + 3 from by ring,
      show n + 1 + 3 * (n + 1) + 4 = 4 * n + 8 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 4 * n + 4⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1573
