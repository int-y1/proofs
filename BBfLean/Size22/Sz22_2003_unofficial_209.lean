import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #209: [1/6, 4/35, 605/2, 3/5, 98/33]

Vector representation:
```
-1 -1  0  0  0
 2  0 -1 -1  0
-1  0  1  0  2
 0  1 -1  0  0
 1 -1  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_209

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- Rule 4: (0, b, c+1, 0, e) → (0, b+1, c, 0, e), repeated k times
theorem r4_repeat : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b c e; simp; exists 0
  | succ k ih =>
    intro b c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- Rule 3: (a+1, 0, c, 0, e) → (a, 0, c+1, 0, e+2), repeated k times
theorem r3_drain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 2))
    ring_nf; finish

-- R5+R1 chain: (0, 2j+1, 0, d, e+j+1) →* (0, 0, 1, d+2j+2, e+2)
theorem r5r1_chain : ∀ j d e, ⟨0, 2 * j + 1, 0, d, e + j + 1⟩ [fm]⊢* ⟨0, 0, 1, d + 2 * j + 2, e + 2⟩ := by
  intro j; induction j with
  | zero =>
    intro d e
    rw [show 2 * 0 + 1 = 0 + 1 from by ring,
        show e + 0 + 1 = e + 1 from by ring,
        show d + 2 * 0 + 2 = d + 2 from by ring]
    step fm; step fm; finish
  | succ j ih =>
    intro d e
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 from by ring,
        show e + (j + 1) + 1 = (e + j + 1) + 1 from by ring]
    step fm
    rw [show 2 * j + 1 + 1 = (2 * j + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

-- R2+R3 round: (a, 0, 1, d+1, e) →* (a+1, 0, 1, d, e+2)
theorem r2r3_round : ∀ a d e, ⟨a, 0, 1, d + 1, e⟩ [fm]⊢* ⟨a + 1, 0, 1, d, e + 2⟩ := by
  intro a d e
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm; ring_nf; finish

-- R2/R3 rounds repeated d times
theorem r2r3_rounds : ∀ d a e, ⟨a, 0, 1, d, e⟩ [fm]⊢* ⟨a + d, 0, 1, 0, e + 2 * d⟩ := by
  intro d; induction d with
  | zero => intro a e; simp; exists 0
  | succ d ih =>
    intro a e
    rw [show d + 1 = d + 1 from by ring]
    apply stepStar_trans (r2r3_round a d e)
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- Full interleave: (0, 0, 1, d, e) →* (0, 0, d+1, 0, e+4d)
theorem r2r3_full : ∀ d e, ⟨0, 0, 1, d, e⟩ [fm]⊢* ⟨0, 0, d + 1, 0, e + 4 * d⟩ := by
  intro d e
  rw [show d + 1 = 1 + d from by ring,
      show e + 4 * d = e + 2 * d + 2 * d from by ring]
  exact stepStar_trans (r2r3_rounds d 0 e) (r3_drain d 0 1 (e + 2 * d))

-- Main transition: (0, 0, 2n+3, 0, e+n+2) →⁺ (0, 0, 2n+5, 0, e+8n+18)
theorem main_trans (n e : ℕ) :
    ⟨0, 0, 2 * n + 3, 0, e + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 5, 0, e + 8 * n + 18⟩ := by
  -- First step: rule 4
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  -- Now at (0, 1, 2n+2, 0, e+n+2). Apply remaining r4.
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_repeat (2 * n + 2) 1 0 (e + n + 2))
  rw [show 1 + (2 * n + 2) = 2 * (n + 1) + 1 from by ring,
      show e + n + 2 = e + (n + 1) + 1 from by ring]
  -- Now at (0, 2(n+1)+1, 0, 0, e+(n+1)+1). Apply r5r1_chain.
  apply stepStar_trans (r5r1_chain (n + 1) 0 e)
  rw [show 0 + 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  -- Now at (0, 0, 1, 2n+4, e+2). Apply r2r3_full.
  apply stepStar_trans (r2r3_full (2 * n + 4) (e + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 11⟩) (by unfold c₀; execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + 3, 0, p.2 + p.1 + 2⟩) ⟨0, 9⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, e + 7 * n + 15⟩, ?_⟩
  show ⟨0, 0, 2 * n + 3, 0, e + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 3, 0, (e + 7 * n + 15) + (n + 1) + 2⟩
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show (e + 7 * n + 15) + (n + 1) + 2 = e + 8 * n + 18 from by ring]
  exact main_trans n e

end Sz22_2003_unofficial_209
