import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1433: [7/15, 22/3, 9/77, 25/11, 99/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  2  0 -1 -1
 0  0  2  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1433

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- Inner loop: R5, R1, R1, R3, R1, R1 (6 steps per iteration).
theorem inner_loop : ∀ k, ∀ a c d, ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

-- R3+R2+R2 chain: each round a += 2, d -= 1, e += 1.
theorem r3r2r2_chain : ∀ k, ∀ a e, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm; step fm
    rw [show a + 1 + 1 = a + 2 from by ring]
    apply stepStar_trans (ih (a + 2) (e + 1)); ring_nf; finish

-- R4 drain: e to c (d = 0).
theorem r4_drain : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih a (c + 2)); ring_nf; finish

-- Phase B: (a+1, 0, 2, D, 0) -> (a+2D+4, 0, 2D+6, 0, 0).
theorem phase_b (a D : ℕ) : ⟨a + 1, 0, 2, D, 0⟩ [fm]⊢* ⟨a + 2 * D + 4, 0, 2 * D + 6, 0, 0⟩ := by
  step fm; step fm; step fm
  rw [show D + 2 = D + 2 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (D + 2) a 0)
  rw [show a + 2 * (D + 2) = a + 2 * D + 4 from by ring,
      show 0 + (D + 2) + 1 = D + 3 from by ring]
  apply stepStar_trans (r4_drain (D + 3) (a + 2 * D + 4) 0)
  ring_nf; finish

-- Phase C: (a+1, 0, 0, d+1, 0) -> (a+2d+4, 0, 2d+8, 0, 0).
theorem phase_c (a d : ℕ) : ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 2 * d + 4, 0, 2 * d + 8, 0, 0⟩ := by
  step fm; step fm; step fm
  rw [show a + 1 + 1 = a + 2 from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (d + 1) (a + 2) 2)
  rw [show a + 2 + 2 * (d + 1) = a + 2 * d + 4 from by ring,
      show 2 + (d + 1) + 1 = d + 4 from by ring]
  apply stepStar_trans (r4_drain (d + 4) (a + 2 * d + 4) 0)
  ring_nf; finish

-- Even case: c = 2p.
-- (n+p+1, 0, 4p, 0, 0) ⊢⁺ (n+6p+2, 0, 6p+6, 0, 0)
theorem main_even (n : ℕ) : ∀ p, ⟨n + p + 1, 0, 4 * p, 0, 0⟩ [fm]⊢⁺ ⟨n + 6 * p + 2, 0, 6 * p + 6, 0, 0⟩ := by
  intro p; rcases p with _ | p
  · step fm; step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  · rw [show n + (p + 1) + 1 = (n + 1) + (p + 1) from by ring,
        show 4 * (p + 1) = 0 + 4 * (p + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (inner_loop (p + 1) (n + 1) 0 0)
    rw [show 0 + 3 * (p + 1) = (3 * p + 2) + 1 from by ring,
        show n + 6 * (p + 1) + 2 = n + 2 * (3 * p + 2) + 4 from by ring,
        show 6 * (p + 1) + 6 = 2 * (3 * p + 2) + 8 from by ring]
    apply stepStar_stepPlus (phase_c n (3 * p + 2))
    intro h
    have := congrArg (fun q : Q ↦ q.1) h
    simp at this; omega

-- Odd case: c = 2m+1.
-- (n+m+1, 0, 4m+2, 0, 0) ⊢⁺ (n+6m+4, 0, 6m+6, 0, 0)
theorem main_odd (n m : ℕ) :
    ⟨n + m + 1, 0, 4 * m + 2, 0, 0⟩ [fm]⊢⁺ ⟨n + 6 * m + 4, 0, 6 * m + 6, 0, 0⟩ := by
  rw [show n + m + 1 = (n + 1) + m from by ring,
      show 4 * m + 2 = 2 + 4 * m from by ring]
  apply stepStar_stepPlus_stepPlus (inner_loop m (n + 1) 2 0)
  rw [show 0 + 3 * m = 3 * m from by ring,
      show n + 6 * m + 4 = n + 2 * (3 * m) + 4 from by ring,
      show 6 * m + 6 = 2 * (3 * m) + 6 from by ring]
  apply stepStar_stepPlus (phase_b n (3 * m))
  intro h
  have := congrArg (fun q : Q ↦ q.1) h
  simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 6, 0, 0⟩)
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n c, q = ⟨n + 1, 0, 2 * c, 0, 0⟩ ∧ 2 * n + 1 ≥ c)
  · intro q ⟨n, c, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd c with ⟨p, hp⟩ | ⟨m, hm⟩
    · subst hp
      have hn : n ≥ p := by omega
      obtain ⟨k, rfl⟩ : ∃ k, n = k + p := ⟨n - p, by omega⟩
      refine ⟨⟨k + 6 * p + 2, 0, 6 * p + 6, 0, 0⟩,
              ⟨k + 6 * p + 1, 3 * p + 3, by ring_nf, by omega⟩, ?_⟩
      rw [show 2 * (p + p) = 4 * p from by ring]
      exact main_even k p
    · subst hm
      have hn : n ≥ m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
      refine ⟨⟨k + 6 * m + 4, 0, 6 * m + 6, 0, 0⟩,
              ⟨k + 6 * m + 3, 3 * m + 3, by ring_nf, by omega⟩, ?_⟩
      rw [show 2 * (2 * m + 1) = 4 * m + 2 from by ring]
      exact main_odd k m
  · exact ⟨1, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1433
