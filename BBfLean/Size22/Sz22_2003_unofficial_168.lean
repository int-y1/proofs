import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #168: [1/45, 500/77, 7/5, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 2  0  3 -1 -1
 0  0 -1  1  0
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt. The canonical states are `(3*n^2+3*n+1, 0, 0, 0, 3*n+3)`.
Each cycle maps `C(n) →⁺ C(n+1)`, incrementing n.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_168

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R3+R2 loop with b=0.
-- Each pair: (a, 0, c+1, 0, k+1) →R3→ (a, 0, c, 1, k+1) →R2→ (a+2, 0, c+3, 0, k)
theorem r3r2_loop_b0 : ∀ k a c,
    (⟨a, 0, c + 1, 0, k + 1⟩ : Q) [fm]⊢* ⟨a + 2 * (k + 1), 0, c + 1 + 2 * (k + 1), 0, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro a c
    step fm -- R3
    step fm -- R2
    ring_nf; finish
  | succ k ih =>
    intro a c
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm -- R3
    step fm -- R2
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (c + 2))
    ring_nf; finish

-- R3+R2 loop with b=1.
theorem r3r2_loop_b1 : ∀ k a c,
    (⟨a, 1, c + 1, 0, k + 1⟩ : Q) [fm]⊢* ⟨a + 2 * (k + 1), 1, c + 1 + 2 * (k + 1), 0, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro a c
    step fm -- R3
    step fm -- R2
    ring_nf; finish
  | succ k ih =>
    intro a c
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm -- R3
    step fm -- R2
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (c + 2))
    ring_nf; finish

-- R3 drain with b=0: (a, 0, c, d, e) →* (a, 0, 0, d+c, e) when e=0
-- Actually need e=0 to prevent R2 from firing after R3 (R2 needs d+1 and e+1).
-- When e=0, after R3: (a, 0, c-1, d+1, 0). R2 needs e+1, e=0, no. R3 fires again. Good.
theorem r3_drain_b0 : ∀ c a d,
    (⟨a, 0, c, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, d + c, 0⟩ := by
  intro c; induction c with
  | zero => intro a d; simp; finish
  | succ c ih =>
    intro a d
    step fm -- R3: (a, 0, c, d+1, 0)
    apply stepStar_trans (ih a (d + 1))
    rw [show d + 1 + c = d + (c + 1) from by ring]; finish

-- R3 drain with b=1, e=0.
theorem r3_drain_b1 : ∀ c a d,
    (⟨a, 1, c, d, 0⟩ : Q) [fm]⊢* ⟨a, 1, 0, d + c, 0⟩ := by
  intro c; induction c with
  | zero => intro a d; simp; finish
  | succ c ih =>
    intro a d
    step fm -- R3: (a, 1, c, d+1, 0)
    apply stepStar_trans (ih a (d + 1))
    rw [show d + 1 + c = d + (c + 1) from by ring]; finish

-- R4 drain: (a, b, 0, k, 0) →* (a, b+k, 0, 0, 0)
theorem r4_drain : ∀ k a b,
    (⟨a, b, 0, k, 0⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; finish
  | succ k ih =>
    intro a b
    step fm -- R4: (a, b+1, 0, k, 0)
    apply stepStar_trans (ih a (b + 1))
    rw [show b + 1 + k = b + (k + 1) from by ring]; finish

-- R5+R1 drain (even): (a+k, 2*k, 0, 0, e) →* (a, 0, 0, 0, e+k)
theorem r5r1_drain_even : ∀ k a e,
    (⟨a + k, 2 * k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm -- R5: (a+k, 2k+2, 1, 0, e+1)
    step fm -- R1: (a+k, 2k, 0, 0, e+1)
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- R5+R1 drain (odd): (a+k, 2*k+1, 0, 0, e) →* (a, 1, 0, 0, e+k)
theorem r5r1_drain_odd : ∀ k a e,
    (⟨a + k, 2 * k + 1, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, 1, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm -- R5: (a+k, 2k+3, 1, 0, e+1)
    step fm -- R1: (a+k, 2k+1, 0, 0, e+1)
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- Main transition: C(n) →⁺ C(n+1)
theorem main_trans : ∀ n,
    (⟨3 * n ^ 2 + 3 * n + 1, 0, 0, 0, 3 * n + 3⟩ : Q) [fm]⊢⁺
    ⟨3 * (n + 1) ^ 2 + 3 * (n + 1) + 1, 0, 0, 0, 3 * (n + 1) + 3⟩ := by
  intro n
  -- Phase 1: R5
  -- (3n²+3n+1, 0, 0, 0, 3n+3) → (3n²+3n, 0, 1, 0, 3n+4)
  rw [show 3 * n ^ 2 + 3 * n + 1 = (3 * n ^ 2 + 3 * n) + 1 from by ring]
  step fm -- R5
  -- Phase 2: R3+R2 loop with b=0, starting from (3n²+3n, 0, 1, 0, 3n+4)
  -- Need 3n+4 >= 1, i.e., in form k+1 where k = 3n+3
  -- (a, 0, 0+1, 0, (3n+3)+1) →* (a+2*(3n+4), 0, 0+1+2*(3n+4), 0, 0)
  -- = (3n²+9n+8, 0, 6n+9, 0, 0)
  rw [show 3 * n + 4 = (3 * n + 3) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r2_loop_b0 (3 * n + 3) (3 * n ^ 2 + 3 * n) 0)
  -- Phase 3: R3 drain (b=0, e=0)
  -- (3n²+9n+8, 0, 6n+9, 0, 0) →* (3n²+9n+8, 0, 0, 6n+9, 0)
  rw [show 0 + 1 + 2 * (3 * n + 3 + 1) = 6 * n + 9 from by ring,
      show 3 * n ^ 2 + 3 * n + 2 * (3 * n + 3 + 1) = 3 * n ^ 2 + 9 * n + 8 from by ring]
  apply stepStar_trans (r3_drain_b0 (6 * n + 9) (3 * n ^ 2 + 9 * n + 8) 0)
  -- Phase 4: R4 drain
  -- (3n²+9n+8, 0, 0, 6n+9, 0) →* (3n²+9n+8, 6n+9, 0, 0, 0)
  rw [show 0 + (6 * n + 9) = 6 * n + 9 from by ring]
  apply stepStar_trans (r4_drain (6 * n + 9) (3 * n ^ 2 + 9 * n + 8) 0)
  -- Phase 5: R5+R1 drain (odd: b = 6n+9 = 2*(3n+4)+1)
  -- (3n²+9n+8, 6n+9, 0, 0, 0) →* (3n²+6n+4, 1, 0, 0, 3n+4)
  rw [show 0 + (6 * n + 9) = 2 * (3 * n + 4) + 1 from by ring,
      show 3 * n ^ 2 + 9 * n + 8 = (3 * n ^ 2 + 6 * n + 4) + (3 * n + 4) from by ring]
  apply stepStar_trans (r5r1_drain_odd (3 * n + 4) (3 * n ^ 2 + 6 * n + 4) 0)
  -- Phase 6: R5
  -- (3n²+6n+4, 1, 0, 0, 3n+4) → (3n²+6n+3, 1, 1, 0, 3n+5)
  rw [show 0 + (3 * n + 4) = 3 * n + 4 from by ring,
      show 3 * n ^ 2 + 6 * n + 4 = (3 * n ^ 2 + 6 * n + 3) + 1 from by ring]
  step fm -- R5
  -- Phase 7: R3+R2 loop with b=1, starting from (3n²+6n+3, 1, 1, 0, 3n+5)
  -- (a, 1, 0+1, 0, (3n+4)+1) →* (a+2*(3n+5), 1, 0+1+2*(3n+5), 0, 0)
  rw [show 3 * n + 5 = (3 * n + 4) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r2_loop_b1 (3 * n + 4) (3 * n ^ 2 + 6 * n + 3) 0)
  -- Phase 8: R3 drain (b=1, e=0)
  -- (3n²+12n+13, 1, 6n+11, 0, 0) →* (3n²+12n+13, 1, 0, 6n+11, 0)
  rw [show 0 + 1 + 2 * (3 * n + 4 + 1) = 6 * n + 11 from by ring,
      show 3 * n ^ 2 + 6 * n + 3 + 2 * (3 * n + 4 + 1) = 3 * n ^ 2 + 12 * n + 13 from by ring]
  apply stepStar_trans (r3_drain_b1 (6 * n + 11) (3 * n ^ 2 + 12 * n + 13) 0)
  -- Phase 9: R4 drain
  -- (3n²+12n+13, 1, 0, 6n+11, 0) →* (3n²+12n+13, 6n+12, 0, 0, 0)
  rw [show 0 + (6 * n + 11) = 6 * n + 11 from by ring]
  apply stepStar_trans (r4_drain (6 * n + 11) (3 * n ^ 2 + 12 * n + 13) 1)
  -- Phase 10: R5+R1 drain (even: b = 6n+12 = 2*(3n+6))
  -- (3n²+12n+13, 6n+12, 0, 0, 0) →* (3n²+9n+7, 0, 0, 0, 3n+6)
  rw [show 1 + (6 * n + 11) = 2 * (3 * n + 6) from by ring,
      show 3 * n ^ 2 + 12 * n + 13 = (3 * n ^ 2 + 9 * n + 7) + (3 * n + 6) from by ring]
  apply stepStar_trans (r5r1_drain_even (3 * n + 6) (3 * n ^ 2 + 9 * n + 7) 0)
  rw [show 0 + (3 * n + 6) = 3 * (n + 1) + 3 from by ring,
      show 3 * n ^ 2 + 9 * n + 7 = 3 * (n + 1) ^ 2 + 3 * (n + 1) + 1 from by ring]
  finish

-- Bootstrap: c₀ →⁺ C(0) = (1, 0, 0, 0, 3)
theorem bootstrap : c₀ [fm]⊢⁺ (⟨1, 0, 0, 0, 3⟩ : Q) := by
  unfold c₀; execute fm 32

theorem nonhalt : ¬halts fm c₀ := by
  apply stepPlus_not_halts_not_halts bootstrap
  exact progress_nonhalt_simple (A := ℕ)
    (C := fun n ↦ (⟨3 * n ^ 2 + 3 * n + 1, 0, 0, 0, 3 * n + 3⟩ : Q))
    (i₀ := 0)
    (fun n ↦ ⟨n + 1, main_trans n⟩)

end Sz22_2003_unofficial_168
