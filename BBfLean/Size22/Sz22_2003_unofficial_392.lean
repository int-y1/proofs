import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #392: [2/15, 99/14, 325/2, 7/11, 22/13]

Vector representation:
```
 1 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 1  0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_392

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k c d e f,
    (⟨0, 0, c, d, e+k, f⟩ : Q) [fm]⊢* ⟨0, 0, c, d+k, e, f⟩ := by
  intro k; induction k with
  | zero => intro c d e f; simp; exists 0
  | succ k ih =>
    intro c d e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k a c d e f,
    (⟨a+1, 0, 2*k+c, k+d, e, f⟩ : Q) [fm]⊢* ⟨a+k+1, 0, c, d, e+k, f⟩ := by
  intro k; induction k with
  | zero => intro a c d e f; simp; exists 0
  | succ k ih =>
    intro a c d e f
    rw [show 2 * (k + 1) + c = (2 * k + c + 1) + 1 from by ring,
        show (k + 1) + d = (k + d) + 1 from by ring]
    step fm
    rw [show 2 * k + c + 1 = (2 * k + c) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

theorem r3_chain : ∀ k a c e f,
    (⟨a+k, 0, c, 0, e, f⟩ : Q) [fm]⊢* ⟨a, 0, c+2*k, 0, e, f+k⟩ := by
  intro k; induction k with
  | zero => intro a c e f; simp; exists 0
  | succ k ih =>
    intro a c e f
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) e (f + 1))
    ring_nf; finish

theorem main_trans (n f : ℕ) :
    (⟨0, 0, 2*(n+1), 0, n, f+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 2*(n+2), 0, n+1, f+n+1⟩ := by
  -- Phase 1: R4 x n: (0,0,2(n+1),0,n,f+1) ->* (0,0,2(n+1),n,0,f+1)
  apply stepStar_stepPlus_stepPlus
  · show (⟨0, 0, 2*(n+1), 0, n, f+1⟩ : Q) [fm]⊢* ⟨0, 0, 2*(n+1), n, 0, f+1⟩
    have h := r4_chain n (2*(n+1)) 0 0 (f+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (0,0,2(n+1),n,0,f+1) -> (1,0,2(n+1),n,1,f)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2*(n+1), n, 0, f+1⟩ = some ⟨1, 0, 2*(n+1), n, 1, f⟩
    simp [fm]
  -- Phase 3: R2,R1,R1 x n: (1,0,2(n+1),n,1,f) ->* (n+1,0,2,0,n+1,f)
  apply stepStar_trans
  · show (⟨1, 0, 2*(n+1), n, 1, f⟩ : Q) [fm]⊢* ⟨n+1, 0, 2, 0, n+1, f⟩
    have h := r2r1r1_chain n 0 2 0 1 f
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 4: R3 x (n+1): (n+1,0,2,0,n+1,f) ->* (0,0,2(n+2),0,n+1,f+n+1)
  show (⟨n+1, 0, 2, 0, n+1, f⟩ : Q) [fm]⊢* ⟨0, 0, 2*(n+2), 0, n+1, f+n+1⟩
  have h := r3_chain (n+1) 0 2 (n+1) f
  simp only [Nat.zero_add] at h
  convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 1⟩) (by execute fm 1)
  refine progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = (⟨0, 0, 2*(n+1), 0, n, f+1⟩ : Q)) ?_ ⟨0, 0, rfl⟩
  intro q ⟨n, f, hq⟩; subst hq
  exact ⟨⟨0, 0, 2*(n+2), 0, n+1, f+n+1⟩, ⟨n+1, f+n, by ring_nf⟩, main_trans n f⟩

end Sz22_2003_unofficial_392
