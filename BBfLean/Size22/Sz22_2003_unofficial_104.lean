import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #104: [1/30, 45/77, 7/3, 4/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0  2  1 -1 -1
 0 -1  0  1  0
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_104

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase B: interleaving growth (R3 then R2, k times)
-- (0, b+1, c, 0, e+k) →* (0, b+1+k, c+k, 0, e)
theorem interleave : ∀ k, ∀ b c e,
    ⟨0, b+1, c, 0, e+k⟩ [fm]⊢* ⟨(0 : ℕ), b+1+k, c+k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b c e; exists 0
  | succ k ih =>
    intro b c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    -- R3: (0, b+1, c, 0, (e+k)+1) → (0, b, c, 1, (e+k)+1)
    step fm
    -- R2: (0, b, c, 1, (e+k)+1) → (0, b+2, c+1, 0, e+k)
    rw [show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    -- now (0, b+2, c+1, 0, e+k) and we need (0, b+1+(k+1), c+(k+1), 0, e)
    -- = (0, b+2+k, c+1+k, 0, e)
    -- ih: (0, (b+1)+1, c+1, 0, e+k) →* (0, (b+1)+1+k, c+1+k, 0, e)
    -- = (0, b+2+k, c+1+k, 0, e) ✓
    apply stepStar_trans (ih (b+1) (c+1) e)
    ring_nf; finish

-- Phase C: drain b to d (R3 repeated, when a=0, e=0)
theorem b_to_d : ∀ k, ∀ b c d,
    ⟨0, b+k, c, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), b, c, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro b c d; exists 0
  | succ k ih =>
    intro b c d
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase D: convert d to a (R4 repeated, when b=0, e=0)
theorem d_to_a : ∀ k, ∀ a c d,
    ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a+2*k, (0 : ℕ), c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase E: unwind a and c into e (R5 then R1, when b=0, d=0, a≥1, c≥1)
-- Each pair: (a+2, 0, c+1, 0, e) →[R5] (a+1, 1, c+1, 0, e+2) →[R1] (a, 0, c, 0, e+2)
theorem unwind : ∀ k, ∀ a c e,
    ⟨a+2*k, 0, c+k, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), c, 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + 2 * (k + 1) = (a + 2 * k + 1) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    -- R5: ((a+2k+1)+1, 0, (c+k)+1, 0, e) → (a+2k+1, 1, (c+k)+1, 0, e+2)
    step fm
    -- R1: (a+2k+1, 1, (c+k)+1, 0, e+2) needs a+2k+1 ≥ 1
    rw [show a + 2 * k + 1 = (a + 2 * k) + 1 from by ring,
        show c + k + 1 = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (2, 0, 0, 0, 2*K) ⊢⁺ (2, 0, 0, 0, 2*(2*K+1)) for K ≥ 1
-- i.e. (2, 0, 0, 0, 2*(k+1)) ⊢⁺ (2, 0, 0, 0, 2*(2*(k+1)+1))
theorem main_trans (k : ℕ) : ⟨2, 0, 0, 0, 2*(k+1)⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 2*(2*(k+1)+1)⟩ := by
  -- Phase A: 6 steps (2, 0, 0, 0, 2K) → (0, 2, 1, 0, 2K) where K = k+1
  -- R5: (2, 0, 0, 0, 2K) → (1, 1, 0, 0, 2K+2)
  apply step_stepStar_stepPlus
    (c₂ := ⟨1, 1, 0, 0, 2*(k+1)+2⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]; simp [fm]
  -- R3: (1, 1, 0, 0, 2K+2) → (1, 0, 0, 1, 2K+2)
  apply stepStar_trans (c₂ := ⟨1, 0, 0, 1, 2*(k+1)+2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- R2: (1, 0, 0, 1, 2K+2) → (1, 2, 1, 0, 2K+1)
  apply stepStar_trans (c₂ := ⟨1, 2, 1, 0, 2*(k+1)+1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2*(k+1)+2 = (2*(k+1)+1) + 1 from by ring]
    step fm; finish
  -- R1: (1, 2, 1, 0, 2K+1) → (0, 1, 0, 0, 2K+1)
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 0, 2*(k+1)+1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- R3: (0, 1, 0, 0, 2K+1) → (0, 0, 0, 1, 2K+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 1, 2*(k+1)+1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- R2: (0, 0, 0, 1, 2K+1) → (0, 2, 1, 0, 2K)
  apply stepStar_trans (c₂ := ⟨0, 2, 1, 0, 2*(k+1)⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2*(k+1)+1 = (2*(k+1)) + 1 from by ring]
    step fm; finish
  -- Phase B: interleave 2K times: (0, 2, 1, 0, 2K) →* (0, 2+2K, 1+2K, 0, 0)
  -- interleave with b=1, c=1, e=0, k_param=2*(k+1)
  apply stepStar_trans (c₂ := ⟨0, 2+2*(k+1), 1+2*(k+1), 0, 0⟩)
  · have h := interleave (2*(k+1)) 1 1 0
    simp only [Nat.zero_add] at h
    rw [show (1 : ℕ) + 1 = 2 from by ring] at h
    exact h
  -- Phase C: drain b to d: (0, 2+2K, 1+2K, 0, 0) →* (0, 0, 1+2K, 2+2K, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 1+2*(k+1), 2+2*(k+1), 0⟩)
  · have h := b_to_d (2+2*(k+1)) 0 (1+2*(k+1)) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase D: d to a: (0, 0, 1+2K, 2+2K, 0) →* (2*(2+2K), 0, 1+2K, 0, 0) = (4+4K, 0, 1+2K, 0, 0)
  apply stepStar_trans (c₂ := ⟨2*(2+2*(k+1)), 0, 1+2*(k+1), 0, 0⟩)
  · have h := d_to_a (2+2*(k+1)) 0 (1+2*(k+1)) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase E: unwind: (4+4K, 0, 1+2K, 0, 0) →* (2, 0, 0, 0, 2*(1+2K))
  -- unwind with a=2, c=0, k_param=1+2K, e=0
  -- (2+2*(1+2K), 0, 0+(1+2K), 0, 0) →* (2, 0, 0, 0, 2*(1+2K))
  -- 2+2*(1+2K) = 2+2+4K = 4+4K = 2*(2+2K) ✓
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 0, 2*(1+2*(k+1))⟩)
  · have h := unwind (1+2*(k+1)) 2 0 0
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (1 + 2 * (k + 1)) = 2 * (2 + 2 * (k + 1)) from by ring] at h
    exact h
  -- Now show 2*(1+2*(k+1)) = 2*(2*(k+1)+1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) →* (2, 0, 0, 0, 4) = (2, 0, 0, 0, 2*2) in 15 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 15)
  -- Use progress_nonhalt_simple with C(n) = (2, 0, 0, 0, 2*(n+2))
  -- n=0 → (2,0,0,0,4), and we need C(n) ⊢⁺ C(n') for some n'
  -- main_trans k: (2, 0, 0, 0, 2*(k+1)) ⊢⁺ (2, 0, 0, 0, 2*(2*(k+1)+1))
  -- With k+1 = n+2, i.e. k = n+1:
  -- (2, 0, 0, 0, 2*(n+2)) ⊢⁺ (2, 0, 0, 0, 2*(2*(n+2)+1)) = (2, 0, 0, 0, 2*(2n+5))
  -- We need n' such that n'+2 = 2n+5, i.e. n' = 2n+3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 0, 0, 2*(n+2)⟩) 0
  intro n
  refine ⟨2*n+3, ?_⟩
  show ⟨2, 0, 0, 0, 2*(n+2)⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 2*(2*n+3+2)⟩
  rw [show n + 2 = (n+1) + 1 from by ring,
      show 2*n+3+2 = 2*((n+1)+1)+1 from by ring]
  exact main_trans (n+1)

end Sz22_2003_unofficial_104
