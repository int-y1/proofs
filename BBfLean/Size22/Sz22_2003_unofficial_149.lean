import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #149: [1/45, 245/33, 2/3, 3/7, 1089/2]

Vector representation:
```
 0 -2 -1  0  0
 0 -1  1  2 -1
 1 -1  0  0  0
 0  1  0 -1  0
-1  2  0  0  2
```

This Fractran program doesn't halt. The canonical states are `(n, 0, c, c+2, 0)`.
Each cycle maps `(n, 0, c, c+2, 0) →⁺ (n+1, 0, 2c+2, 2c+4, 0)`, doubling `c`.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_149

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- R4+R3 chain: transfer d to a (when e=0)
theorem d_to_a : ∀ k a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a+k, (0:ℕ), c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5+R1 drain: each pair a-=1, c-=1, e+=2
theorem r5r1_drain : ∀ k a c e, ⟨a+k, 0, c+k, 0, e⟩ [fm]⊢* ⟨a, (0:ℕ), c, 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Bridge: R5, R2, R2
theorem bridge : ∀ a e, ⟨a+1, 0, 0, 0, e⟩ [fm]⊢* ⟨a, (0:ℕ), 2, 4, e⟩ := by
  intro a e; step fm; step fm; step fm; finish

-- R4+R2 chain: each pair c+=1, d+=1, e-=1
theorem r4r2_chain : ∀ k a c d e, ⟨a, 0, c, d+1, e+k⟩ [fm]⊢* ⟨a, (0:ℕ), c+k, d+k+1, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Main transition: (n, 0, c, c+2, 0) →⁺ (n+1, 0, 2*c+2, 2*c+4, 0)
theorem main_trans : ∀ n c, ⟨n, 0, c, c+2, 0⟩ [fm]⊢⁺ ⟨n+1, (0:ℕ), 2*c+2, 2*c+4, 0⟩ := by
  intro n c
  -- First step: R4 on (n, 0, c, c+2, 0) → (n, 1, c, c+1, 0)
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨n, 1, c, c+1, 0⟩)
  · show fm ⟨n, 0, c, (c + 1) + 1 - 1 + 1, 0⟩ = some ⟨n, 0 + 1, c, c + 1, 0⟩; simp [fm]
  -- R3: (n, 1, c, c+1, 0) → (n+1, 0, c, c+1, 0)
  step fm
  -- d_to_a: (n+1, 0, c, 0+(c+1), 0) →* (n+1+(c+1), 0, c, 0, 0) = (n+c+2, 0, c, 0, 0)
  apply stepStar_trans (c₂ := ⟨n+c+2, 0, c, 0, 0⟩)
  · rw [show c + 1 = 0 + (c + 1) from by ring]
    apply stepStar_trans (d_to_a (c+1) (n+1) c 0)
    ring_nf; finish
  -- r5r1_drain: (n+c+2, 0, c, 0, 0) →* (n+2, 0, 0, 0, 2*c)
  apply stepStar_trans (c₂ := ⟨n+2, 0, 0, 0, 2*c⟩)
  · have h := r5r1_drain c (n+2) 0 0
    simp only [Nat.zero_add] at h
    rw [show n + c + 2 = n + 2 + c from by ring]
    exact h
  -- bridge: (n+2, 0, 0, 0, 2*c) →* (n+1, 0, 2, 4, 2*c)
  apply stepStar_trans (c₂ := ⟨n+1, 0, 2, 4, 2*c⟩)
  · rw [show n + 2 = (n + 1) + 1 from by ring]
    exact bridge (n+1) (2*c)
  -- r4r2_chain: (n+1, 0, 2, 3+1, 0+2*c) →* (n+1, 0, 2+2*c, 3+2*c+1, 0)
  rw [show (4:ℕ) = 3 + 1 from by ring, show 2 * c = 0 + 2 * c from by ring]
  apply stepStar_trans (r4r2_chain (2*c) (n+1) 2 3 0)
  ring_nf; finish

-- Bootstrap: c₀ →⁺ (0, 0, 2, 4, 0)
theorem bootstrap : c₀ [fm]⊢⁺ ⟨0, (0:ℕ), 2, 4, 0⟩ := by
  unfold c₀; execute fm 3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepPlus_not_halts_not_halts bootstrap
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n, 0, c, c+2, 0⟩) ⟨0, 2⟩
  intro ⟨n, c⟩
  exact ⟨⟨n+1, 2*c+2⟩, main_trans n c⟩

end Sz22_2003_unofficial_149
