import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #442: [27/35, 65/33, 14/3, 11/13, 39/2]

Vector representation:
```
 0  3 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_442

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+3, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R4 chain: (a, 0, 0, d, e, f+k) ->* (a, 0, 0, d, e+k, f)
theorem f_to_e : ∀ k a d e f, ⟨a, 0, 0, d, e, f+k⟩ [fm]⊢* ⟨a, 0, 0, d, e+k, f⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a d e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) f)
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- R3 chain: (a, b+k, 0, d, 0, f) ->* (a+k, b, 0, d+k, 0, f)
theorem r3_chain : ∀ k a b d f, ⟨a, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k, b, 0, d+k, 0, f⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a b d f
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (d + 1) f)
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]; finish

-- (R2, R1) pairs: (a, b+1, 0, d+n, n, f) ->* (a, b+2*n+1, 0, d, 0, f+n)
theorem r2r1_pairs : ∀ n a b d f,
    ⟨a, b+1, 0, d+n, n, f⟩ [fm]⊢* ⟨a, b+2*n+1, 0, d, 0, f+n⟩ := by
  intro n; induction n with
  | zero =>
    intro a b d f; simp; exists 0
  | succ n ih =>
    intro a b d f
    rw [show d + (n + 1) = d + n + 1 from by ring,
        show (n + 1) = n + 1 from rfl]
    step fm
    rw [show d + n + 1 = (d + n) + 1 from by ring]
    step fm
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih a (b + 2) d (f + 1))
    rw [show b + 2 + 2 * n + 1 = b + 2 * (n + 1) + 1 from by ring,
        show f + 1 + n = f + (n + 1) from by ring]; finish

-- Main: (a+1, 0, 0, d+k, 0, k) ->+ (a+2*k+1, 0, 0, d+2*k+1, 0, k+1)
theorem main_trans (a d k : ℕ) :
    ⟨a+1, 0, 0, d+k, 0, k⟩ [fm]⊢⁺ ⟨a+2*k+1, 0, 0, d+2*k+1, 0, k+1⟩ := by
  cases k with
  | zero =>
    simp
    apply step_stepStar_stepPlus (by unfold fm; rfl)
    have h := r3_chain 1 a 0 d 1
    simp at h; exact h
  | succ k =>
    -- Phase 1: f_to_e (k+1)
    have h1 := f_to_e (k+1) (a+1) (d+k+1) 0 0
    simp at h1
    apply stepStar_stepPlus_stepPlus h1
    -- Phase 2: R5
    apply step_stepStar_stepPlus (by unfold fm; rfl)
    -- Phase 3: r2r1_pairs (k+1)
    rw [show d + k + 1 = d + (k + 1) from by ring]
    have h3 := r2r1_pairs (k+1) a 0 d 1
    apply stepStar_trans h3
    rw [show 0 + 2 * (k + 1) + 1 = 2*k+3 from by ring,
        show 1 + (k + 1) = k + 2 from by ring]
    -- Phase 4: r3_chain (2*k+3)
    have h4 := r3_chain (2*k+3) a 0 d (k+2)
    rw [show 0 + (2*k+3) = 2*k+3 from by ring] at h4
    convert h4 using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0, 2⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun p ↦ ⟨p.1+1, 0, 0, p.2.1+p.2.2, 0, p.2.2⟩) ⟨2, 1, 2⟩
  intro ⟨a, d, k⟩
  refine ⟨⟨a + 2*k, d + k, k + 1⟩, ?_⟩
  show ⟨a+1, 0, 0, d+k, 0, k⟩ [fm]⊢⁺ ⟨a+2*k+1, 0, 0, (d+k)+(k+1), 0, k+1⟩
  rw [show d + k + (k + 1) = d + 2 * k + 1 from by ring]
  exact main_trans a d k

end Sz22_2003_unofficial_442
