import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #757: [35/6, 4/55, 847/2, 3/7, 4/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_757

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem round_chain : ∀ k, ∀ b c d e, ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem interleave_even (k r : ℕ) :
    ⟨0, 2 * k, 0, 0, 2 * k + 1 + r⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, 2 * k, r⟩ := by
  rw [show 2 * k + 1 + r = (k + r) + k + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 2 from rfl,
      show 2 * k = 0 + 2 * k from by ring,
      show k + r + k = (k + r) + k from by ring]
  apply stepStar_trans (round_chain k 0 0 0 (k + r))
  rw [show 0 + k = k from by ring,
      show 0 + 2 * k = 2 * k from by ring,
      show k + r = r + k from by ring]
  apply stepStar_trans (r2_chain k 2 (2 * k) r)
  ring_nf; finish

theorem interleave_odd (k r : ℕ) :
    ⟨0, 2 * k + 1, 0, 0, 2 * k + 2 + r⟩ [fm]⊢* ⟨2 * k + 3, 0, 0, 2 * k + 1, r⟩ := by
  rw [show 2 * k + 2 + r = (k + 1 + r) + (k + 1) from by ring]
  step fm
  rw [show (2 : ℕ) = 2 from rfl,
      show 2 * k + 1 = 1 + 2 * k from by ring]
  change (2, 1 + 2 * k, 0, 0, Nat.add (k + 1 + r) k) [fm]⊢* (2 * k + 3, 0, 0, 1 + 2 * k, r)
  rw [show Nat.add (k + 1 + r) k = (k + 1 + r) + k from rfl]
  apply stepStar_trans (round_chain k 1 0 0 (k + 1 + r))
  rw [show (0 + k : ℕ) = k from by ring,
      show (0 + 2 * k : ℕ) = 2 * k from by ring,
      show k + 1 + r = r + (k + 1) from by ring]
  step fm
  rw [show (1 : ℕ) = 1 from rfl]
  apply stepStar_trans (r2_chain (k + 1) 1 (2 * k + 1) r)
  ring_nf; finish

theorem interleave (b r : ℕ) :
    ⟨0, b, 0, 0, b + 1 + r⟩ [fm]⊢* ⟨b + 2, 0, 0, b, r⟩ := by
  rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact interleave_even k r
  · subst hk
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring]
    exact interleave_odd k r

theorem main_trans (d r : ℕ) :
    ⟨0, 0, 0, d, d + 1 + r⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, 2 * d + 4 + r⟩ := by
  rcases d with _ | d
  · -- d=0: ⟨0,0,0,0,1+r⟩ ⊢⁺ ⟨0,0,0,2,4+r⟩
    rw [show (0 : ℕ) + 1 + r = r + 1 from by ring]
    step fm
    rw [show 2 * 0 + 2 = 2 from by ring,
        show 2 * 0 + 4 + r = r + 2 * 2 from by ring,
        show (2 : ℕ) = 0 + 2 from by ring]
    exact r3_chain 2 0 0 r
  · -- d+1: ⟨0,0,0,d+1,d+2+r⟩ ⊢⁺ ⟨0,0,0,2d+4,2d+6+r⟩
    rw [show d + 1 + 1 + r = d + 2 + r from by ring,
        show 2 * (d + 1) + 2 = 2 * d + 4 from by ring,
        show 2 * (d + 1) + 4 + r = 2 * d + 6 + r from by ring]
    -- First step R4: ⟨0,0,0,d+1,d+2+r⟩ → ⟨0,1,0,d,d+2+r⟩
    step fm
    -- r4_chain d: ⟨0,1,0,d,d+2+r⟩ ⊢* ⟨0,d+1,0,0,d+2+r⟩
    have h1 := r4_chain d 1 0 (d + 2 + r)
    rw [show 0 + d = d from by ring] at h1
    apply stepStar_trans h1
    rw [show (1 + d : ℕ) = d + 1 from by ring,
        show d + 2 + r = (d + 1) + 1 + r from by ring]
    -- interleave (d+1) r: ⟨0,d+1,0,0,(d+1)+1+r⟩ ⊢* ⟨d+3,0,0,d+1,r⟩
    apply stepStar_trans (interleave (d + 1) r)
    rw [show d + 1 + 2 = 0 + (d + 3) from by ring,
        show 2 * d + 6 + r = r + 2 * (d + 3) from by ring]
    apply stepStar_trans (r3_chain (d + 3) 0 (d + 1) r)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, r⟩ ↦ ⟨0, 0, 0, d, d + 1 + r⟩) ⟨1, 0⟩
  intro ⟨d, r⟩
  refine ⟨⟨2 * d + 2, r + 1⟩, ?_⟩
  show ⟨0, 0, 0, d, d + 1 + r⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, 2 * d + 2 + 1 + (r + 1)⟩
  rw [show 2 * d + 2 + 1 + (r + 1) = 2 * d + 4 + r from by ring]
  exact main_trans d r

end Sz22_2003_unofficial_757
