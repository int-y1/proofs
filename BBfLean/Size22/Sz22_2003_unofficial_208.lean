import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #208: [1/6, 4/35, 55/2, 3/5, 98/33]

Vector representation:
```
-1 -1  0  0  0
 2  0 -1 -1  0
-1  0  1  0  1
 0  1 -1  0  0
 1 -1  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_208

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- Consume d via alternating rule3+rule2.
-- (a+1, 0, 0, k, e) →* (a+1+k, 0, 0, 0, e+k)
theorem consume_d : ∀ k a e,
    ⟨a + 1, 0, 0, k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    step fm  -- rule3: (a+1,0,0,k+1,e) → (a,0,1,k+1,e+1)
    step fm  -- rule2: (a,0,1,k+1,e+1) → (a+2,0,0,k,e+1)
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Rule3 repeated: drain a, incrementing c and e.
-- (k, 0, c, 0, e) →* (0, 0, c+k, 0, e+k)
theorem rule3_repeat : ∀ k c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; simp; exists 0
  | succ k ih =>
    intro c e
    step fm  -- rule3: (k+1,0,c,0,e) → (k,0,c+1,0,e+1)
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- Rule4 repeated: drain c, incrementing b.
-- (0, b, k, 0, e) →* (0, b+k, 0, 0, e)
theorem rule4_repeat : ∀ k b e,
    ⟨0, b, k, 0, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b e; simp; exists 0
  | succ k ih =>
    intro b e
    step fm  -- rule4: (0,b,k+1,0,e) → (0,b+1,k,0,e)
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- Phase 4: consume b and e via rule5+rule1 pairs, then final rule5.
-- (0, 2k+1, 0, d, e+k+1) →* (1, 0, 0, d+2k+2, e)
theorem phase4 : ∀ k d e,
    ⟨0, 2 * k + 1, 0, d, e + k + 1⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * k + 2, e⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    step fm  -- rule5: (0,1,0,d,e+1) → (1,0,0,d+2,e)
    ring_nf; finish
  | succ k ih =>
    intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = ((e + 1) + k) + 1 from by ring]
    step fm  -- rule5: (0,(2k+2)+1,0,d,(e+1)+k+1) → (1,2k+2,0,d+2,(e+1)+k)
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm  -- rule1: (1,(2k+1)+1,0,d+2,(e+1)+k) → (0,2k+1,0,d+2,(e+1)+k)
    rw [show (e + 1) + k = e + k + 1 from by ring]
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

-- Main transition: (1, 0, 0, 2n, e) →⁺ (1, 0, 0, 2(n+1), e+3n)
theorem main_trans (n e : ℕ) :
    ⟨1, 0, 0, 2 * n, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * (n + 1), e + 3 * n⟩ := by
  -- Phase 1: consume_d: (1, 0, 0, 2n, e) →* (2n+1, 0, 0, 0, e+2n)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (consume_d (2 * n) 0 e)
  rw [show 0 + 1 + 2 * n = 2 * n + 1 from by ring]
  -- Phase 2: rule3_repeat: (2n+1, 0, 0, 0, e+2n) →* (0, 0, 2n+1, 0, e+4n+1)
  apply step_stepStar_stepPlus
  · -- First step of rule3_repeat (always possible since 2n+1≥1)
    rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
    show fm ⟨2 * n + 1, 0, 0, 0, e + 2 * n⟩ = some ⟨2 * n, 0, 1, 0, e + 2 * n + 1⟩
    rfl
  apply stepStar_trans (rule3_repeat (2 * n) 1 (e + 2 * n + 1))
  rw [show 1 + 2 * n = 2 * n + 1 from by ring,
      show e + 2 * n + 1 + 2 * n = e + (4 * n + 1) from by ring]
  -- Phase 3: rule4_repeat: (0, 0, 2n+1, 0, e+4n+1) →* (0, 2n+1, 0, 0, e+4n+1)
  apply stepStar_trans (rule4_repeat (2 * n + 1) 0 (e + (4 * n + 1)))
  rw [show 0 + (2 * n + 1) = 2 * n + 1 from by ring]
  -- Phase 4: phase4: (0, 2n+1, 0, 0, e+4n+1) →* (1, 0, 0, 2n+2, e+3n)
  rw [show e + (4 * n + 1) = (e + 3 * n) + n + 1 from by ring,
      show 2 * n + 1 = 2 * n + 1 from rfl]
  apply stepStar_trans (phase4 n 0 (e + 3 * n))
  rw [show 0 + 2 * n + 2 = 2 * (n + 1) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨1, 0, 0, 2 * p.1, p.2⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, e + 3 * n⟩, ?_⟩
  exact main_trans n e

end Sz22_2003_unofficial_208
