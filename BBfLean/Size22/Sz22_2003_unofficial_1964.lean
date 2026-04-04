import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1964: [99/35, 1/66, 55/3, 2/5, 147/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  0  0 -1
 0 -1  1  0  1
 1  0 -1  0  0
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1964

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R3+R1 interleave: (0, b+1, 0, d+k, e) ->* (0, b+k+1, 0, d, e+2*k)
theorem r3r1_chain : ∀ k b d e, ⟨0, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k + 1, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [Nat.add_succ d k]
    step fm  -- R3: (0, b, 1, (d+k)+1, e+1)
    step fm  -- R1: (0, b+2, 0, d+k, e+2)
    apply stepStar_trans (ih (b + 1) d (e + 2))
    ring_nf; finish

-- R3 drain: (0, b+k, c, 0, e) ->* (0, b, c+k, 0, e+k)
theorem r3_drain : ∀ k b c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [Nat.add_succ b k]
    step fm  -- R3: (0, b+k, c+1, 0, e+1)
    apply stepStar_trans (ih b (c + 1) (e + 1))
    ring_nf; finish

-- R4 chain: (a, 0, c+k, 0, e) ->* (a+k, 0, c, 0, e)
theorem r4_chain : ∀ k a c e, ⟨a, 0, c + k, (0 : ℕ), e⟩ [fm]⊢* ⟨a + k, 0, c, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [Nat.add_succ c k]
    step fm  -- R4: (a+1, 0, c+k, 0, e)
    apply stepStar_trans (ih (a + 1) c e)
    ring_nf; finish

-- R5+R2 pair: (a+2, 0, 0, d, e+1) ->* (a, 0, 0, d+2, e)
-- R5: (a+2, 0, 0, d, e+1) -> (a+1, 1, 0, d+2, e+1)
-- R2: (a+1, 1, 0, d+2, e+1) -> (a, 0, 0, d+2, e)
theorem r5r2_pair : ⟨a + 2, 0, 0, d, e + 1⟩ [fm]⊢* ⟨a, 0, 0, d + 2, e⟩ := by
  step fm; step fm; finish

-- R5+R2 drain using r5r2_pair: (2*k+1, 0, 0, d, e+k) ->* (1, 0, 0, d+2*k, e)
theorem r5r2_drain : ∀ k d e, ⟨2 * k + 1, 0, 0, d, e + k⟩ [fm]⊢* ⟨(1 : ℕ), 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (r5r2_pair (a := 2 * k + 1) (d := d) (e := e + k))
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

theorem main_trans (n e : ℕ) : ⟨1, 0, 0, 2 * n, e⟩ [fm]⊢⁺ ⟨(1 : ℕ), 0, 0, 2 * (n + 1), e + 5 * n + 6⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R5: (0, 1, 0, 2*n+2, e)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3r1_chain (2 * n + 2) 0 0 e)
  rw [show 0 + (2 * n + 2) + 1 = 0 + (2 * n + 3) from by ring,
      show e + 2 * (2 * n + 2) = e + 4 * n + 4 from by ring]
  apply stepStar_trans (r3_drain (2 * n + 3) 0 0 (e + 4 * n + 4))
  rw [show e + 4 * n + 4 + (2 * n + 3) = e + 6 * n + 7 from by ring,
      show (0 + (2 * n + 3) : ℕ) = 0 + (2 * n + 3) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 3) 0 0 (e + 6 * n + 7))
  rw [show 0 + (2 * n + 3) = 2 * (n + 1) + 1 from by ring,
      show e + 6 * n + 7 = (e + 5 * n + 6) + (n + 1) from by ring]
  apply stepStar_trans (r5r2_drain (n + 1) 0 (e + 5 * n + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨1, 0, 0, 2 * n, e⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  exact ⟨⟨n + 1, e + 5 * n + 6⟩, main_trans n e⟩

end Sz22_2003_unofficial_1964
