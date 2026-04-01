import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1580: [7/45, 5/77, 5324/5, 3/11, 5/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  1 -1 -1
 2  0 -1  0  3
 0  1  0  0 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1580

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain (b=0, d=0): (a, 0, c+k, 0, e) -> (a+2k, 0, c, 0, e+3k)
theorem r3_chain_b0 : ∀ k, ∀ a c e,
    (⟨a, 0, c + k, 0, e⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, c, 0, e + 3 * k⟩ := by
  intro k; induction k with
  | zero => intro a c e; ring_nf; finish
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (e + 3))
    ring_nf; finish

-- R3 chain (b=1, d=0): (a, 1, c+k, 0, e) -> (a+2k, 1, c, 0, e+3k)
theorem r3_chain_b1 : ∀ k, ∀ a c e,
    (⟨a, 1, c + k, 0, e⟩ : Q) [fm]⊢* ⟨a + 2 * k, 1, c, 0, e + 3 * k⟩ := by
  intro k; induction k with
  | zero => intro a c e; ring_nf; finish
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (e + 3))
    ring_nf; finish

-- R4 chain (c=0, d=0): (a, b, 0, 0, e+k) -> (a, b+k, 0, 0, e)
theorem r4_chain : ∀ k, ∀ a b e,
    (⟨a, b, 0, 0, e + k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; ring_nf; finish
  | succ k ih =>
    intro a b e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) e)
    ring_nf; finish

-- R2 chain (b=0, c stays): (a, 0, c, d+k, e+k) -> (a, 0, c+k, d, e)
theorem r2_chain_b0 : ∀ k, ∀ a c d e,
    (⟨a, 0, c, d + k, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, d, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; ring_nf; finish
  | succ k ih =>
    intro a c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) d e)
    ring_nf; finish

-- R2 chain (b=1): (a, 1, c, d+k, e+k) -> (a, 1, c+k, d, e)
theorem r2_chain_b1 : ∀ k, ∀ a c d e,
    (⟨a, 1, c, d + k, e + k⟩ : Q) [fm]⊢* ⟨a, 1, c + k, d, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; ring_nf; finish
  | succ k ih =>
    intro a c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) d e)
    ring_nf; finish

-- R5,R1 chain (b odd, c=0, e=0): (a+k, 2k+1, 0, d, 0) -> (a, 1, 0, d+k, 0)
theorem r5r1_chain_odd : ∀ k, ∀ a d,
    (⟨a + k, 2 * k + 1, 0, d, 0⟩ : Q) [fm]⊢* ⟨a, 1, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; ring_nf; finish
  | succ k ih =>
    intro a d
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R5,R1 chain (b even, c=0, e=0): (a+k, 2k, 0, d, 0) -> (a, 0, 0, d+k, 0)
theorem r5r1_chain_even : ∀ k, ∀ a d,
    (⟨a + k, 2 * k, 0, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; ring_nf; finish
  | succ k ih =>
    intro a d
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R3,R2^3 chain (b=0): each round does R3 then 3×R2
theorem r3r2_chain_b0 : ∀ k, ∀ a c d,
    (⟨a, 0, c + 1, d + 3 * k, 0⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, c + 1 + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring]
    step fm
    rw [show d + 3 * k + 3 = (d + 3 * k) + 3 from by ring]
    apply stepStar_trans (r2_chain_b0 3 (a + 2) c (d + 3 * k) 0)
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (c + 2) d)
    ring_nf; finish

-- R3,R2^3 chain (b=1): same with b=1
theorem r3r2_chain_b1 : ∀ k, ∀ a c d,
    (⟨a, 1, c + 1, d + 3 * k, 0⟩ : Q) [fm]⊢* ⟨a + 2 * k, 1, c + 1 + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring]
    step fm
    rw [show d + 3 * k + 3 = (d + 3 * k) + 3 from by ring]
    apply stepStar_trans (r2_chain_b1 3 (a + 2) c (d + 3 * k) 0)
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (c + 2) d)
    ring_nf; finish

-- Tail phase: (a, 1, c+1, 1, 0) -> (a+4, 1, c, 0, 5)
-- R3: (a+2, 1, c, 1, 3). R2^1: (a+2, 1, c+1, 0, 2). R3: (a+4, 1, c, 0, 5).
theorem tail_d1 : ∀ a c,
    (⟨a, 1, c + 1, 1, 0⟩ : Q) [fm]⊢* ⟨a + 4, 1, c, 0, 5⟩ := by
  intro a c
  step fm; step fm; step fm
  ring_nf; finish

-- Main transition: (a, 0, 2n+1, 0, 0) [fm]⊢⁺ (a+6n+2, 0, 2n+3, 0, 0)
theorem main_trans : ∀ n a,
    (⟨a, 0, 2 * n + 1, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a + 6 * n + 2, 0, 2 * n + 3, 0, 0⟩ := by
  intro n a
  -- Phase 1: R3^(2n+1): (a, 0, 2n+1, 0, 0) -> (a+4n+2, 0, 0, 0, 6n+3)
  have phase1 : (⟨a, 0, 2 * n + 1, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a + 4 * n + 2, 0, 0, 0, 6 * n + 3⟩ := by
    rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
    step fm
    apply stepStar_trans (r3_chain_b0 (2 * n) (a + 2) 0 3)
    ring_nf; finish
  -- Phase 2: R4^(6n+3): -> (a+4n+2, 6n+3, 0, 0, 0)
  have phase2 : (⟨a + 4 * n + 2, 0, 0, 0, 6 * n + 3⟩ : Q) [fm]⊢*
      ⟨a + 4 * n + 2, 6 * n + 3, 0, 0, 0⟩ := by
    rw [show 6 * n + 3 = 0 + (6 * n + 3) from by ring]
    apply stepStar_trans (r4_chain (6 * n + 3) (a + 4 * n + 2) 0 0)
    ring_nf; finish
  -- Phase 3: R5,R1 x(3n+1): b=6n+3=2(3n+1)+1 (odd)
  -- -> (a+n+1, 1, 0, 3n+1, 0)
  have phase3 : (⟨a + 4 * n + 2, 6 * n + 3, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨a + n + 1, 1, 0, 3 * n + 1, 0⟩ := by
    rw [show 6 * n + 3 = 2 * (3 * n + 1) + 1 from by ring,
        show a + 4 * n + 2 = (a + n + 1) + (3 * n + 1) from by ring]
    apply stepStar_trans (r5r1_chain_odd (3 * n + 1) (a + n + 1) 0)
    ring_nf; finish
  -- Phase 4: R5 then r3r2_chain_b1 with k=n
  -- (a+n+1, 1, 0, 3n+1, 0) -> R5 -> (a+n, 1, 1, 3n+1, 0)
  -- r3r2_chain_b1 k=n: (a+n, 1, 0+1, 1+3n, 0) -> (a+3n, 1, 2n+1, 1, 0)
  have phase4 : (⟨a + n + 1, 1, 0, 3 * n + 1, 0⟩ : Q) [fm]⊢*
      ⟨a + 3 * n, 1, 2 * n + 1, 1, 0⟩ := by
    rw [show a + n + 1 = (a + n) + 1 from by ring]
    step fm
    rw [show 3 * n + 1 = 1 + 3 * n from by ring]
    apply stepStar_trans (r3r2_chain_b1 n (a + n) 0 1)
    ring_nf; finish
  -- Phase 5: tail d=1: (a+3n, 1, 2n+1, 1, 0) -> (a+3n+4, 1, 2n, 0, 5)
  have phase5 : (⟨a + 3 * n, 1, 2 * n + 1, 1, 0⟩ : Q) [fm]⊢*
      ⟨a + 3 * n + 4, 1, 2 * n, 0, 5⟩ := by
    rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
    exact tail_d1 (a + 3 * n) (2 * n)
  -- Phase 6: R3^(2n) (b=1, d=0): (a+3n+4, 1, 2n, 0, 5) -> (a+7n+4, 1, 0, 0, 6n+5)
  have phase6 : (⟨a + 3 * n + 4, 1, 2 * n, 0, 5⟩ : Q) [fm]⊢*
      ⟨a + 7 * n + 4, 1, 0, 0, 6 * n + 5⟩ := by
    rw [show 2 * n = 0 + 2 * n from by ring]
    apply stepStar_trans (r3_chain_b1 (2 * n) (a + 3 * n + 4) 0 5)
    ring_nf; finish
  -- Phase 7: R4^(6n+5): -> (a+7n+4, 6n+6, 0, 0, 0)
  have phase7 : (⟨a + 7 * n + 4, 1, 0, 0, 6 * n + 5⟩ : Q) [fm]⊢*
      ⟨a + 7 * n + 4, 6 * n + 6, 0, 0, 0⟩ := by
    rw [show 6 * n + 5 = 0 + (6 * n + 5) from by ring]
    apply stepStar_trans (r4_chain (6 * n + 5) (a + 7 * n + 4) 1 0)
    ring_nf; finish
  -- Phase 8: R5,R1 x(3n+3) (even): b=6n+6=2(3n+3)
  -- -> (a+4n+1, 0, 0, 3n+3, 0)
  have phase8 : (⟨a + 7 * n + 4, 6 * n + 6, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨a + 4 * n + 1, 0, 0, 3 * n + 3, 0⟩ := by
    rw [show 6 * n + 6 = 2 * (3 * n + 3) from by ring,
        show a + 7 * n + 4 = (a + 4 * n + 1) + (3 * n + 3) from by ring]
    apply stepStar_trans (r5r1_chain_even (3 * n + 3) (a + 4 * n + 1) 0)
    ring_nf; finish
  -- Phase 9: R5, R3, R2^3, then r3r2_chain_b0 with k=n
  -- (a+4n+1, 0, 0, 3n+3, 0) -> R5 -> (a+4n, 0, 1, 3n+3, 0)
  -- -> R3 -> (a+4n+2, 0, 0, 3n+3, 3)
  -- -> R2^3 -> (a+4n+2, 0, 3, 3n, 0)
  -- -> r3r2_chain_b0 k=n: (a+4n+2, 0, 2+1, 0+3n, 0) -> (a+6n+2, 0, 2n+3, 0, 0)
  have phase9 : (⟨a + 4 * n + 1, 0, 0, 3 * n + 3, 0⟩ : Q) [fm]⊢*
      ⟨a + 6 * n + 2, 0, 2 * n + 3, 0, 0⟩ := by
    rw [show a + 4 * n + 1 = (a + 4 * n) + 1 from by ring]
    step fm
    -- state: (a+4n, 0, 1, 3n+3, 0). R3: (a+4n+2, 0, 0, 3n+3, 3)
    rw [show 3 * n + 3 = (3 * n) + 3 from by ring]
    step fm
    -- state: (a+4n+2, 0, 0, 3n+3, 3). R2^3: (a+4n+2, 0, 3, 3n, 0)
    rw [show (3 * n + 3 : ℕ) = (3 * n) + 3 from by ring]
    apply stepStar_trans (r2_chain_b0 3 (a + 4 * n + 2) 0 (3 * n) 0)
    -- state: (a+4n+2, 0, 3, 3n, 0) = (a+4n+2, 0, 2+1, 0+3n, 0)
    rw [show (0 : ℕ) + 3 = 2 + 1 from by ring,
        show 3 * n = 0 + 3 * n from by ring]
    apply stepStar_trans (r3r2_chain_b0 n (a + 4 * n + 2) 2 0)
    ring_nf; finish
  exact stepPlus_stepStar_stepPlus phase1
    (stepStar_trans phase2 (stepStar_trans phase3 (stepStar_trans phase4
      (stepStar_trans phase5 (stepStar_trans phase6 (stepStar_trans phase7
        (stepStar_trans phase8 phase9)))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a, 0, 2 * n + 1, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, n⟩
  exact ⟨⟨a + 6 * n + 2, n + 1⟩, main_trans n a⟩

end Sz22_2003_unofficial_1580
