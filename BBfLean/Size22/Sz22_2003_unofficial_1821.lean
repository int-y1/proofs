import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1821: [9/10, 55/21, 4/3, 7/11, 63/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1821

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r3_chain : ∀ k a, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [← Nat.add_assoc a k 1, ← Nat.add_assoc d k 1]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1)); ring_nf; finish

-- R2+R1 chain followed by R3 chain.
theorem main_trans_aux (a d : ℕ) :
    ⟨a + d + 1, 2, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 2 * d + 6, 0, 0, 0, d + 1⟩ := by
  have h1 := r2r1_chain (d + 1) a 1 0 0
  simp only [Nat.zero_add, Nat.reduceAdd] at h1
  rw [show 2 + (d + 1) = d + 3 from by ring] at h1
  apply stepStar_trans h1
  apply stepStar_trans (r3_chain (d + 3) a (e := d + 1))
  ring_nf; finish

-- R5 followed by main_trans_aux.
theorem main_trans (a d : ℕ) :
    ⟨a + d + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 6, 0, 0, 0, d + 1⟩ := by
  step fm
  exact main_trans_aux a d

-- R4 chain then main_trans.
theorem full_trans (a e : ℕ) :
    ⟨a + e + 4, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + 2 * e + 9, 0, 0, 0, e + 2⟩ := by
  have h1 : ⟨a + e + 4, 0, 0, 0, 0 + (e + 1)⟩ [fm]⊢* ⟨a + e + 4, 0, 0, 0 + (e + 1), 0⟩ :=
    e_to_d (e + 1) 0 (a := a + e + 4) (e := 0)
  simp only [Nat.zero_add] at h1
  have h2 := main_trans (a + 1) (e + 1)
  rw [show a + 1 + (e + 1) + 2 = a + e + 4 from by ring,
      show a + 1 + 2 * (e + 1) + 6 = a + 2 * e + 9 from by ring,
      show (e + 1) + 1 = e + 2 from by ring] at h2
  exact stepStar_stepPlus_stepPlus h1 h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + e + 4, 0, 0, 0, e + 1⟩) ⟨1, 0⟩
  intro ⟨a, e⟩
  refine ⟨⟨a + e + 4, e + 1⟩, ?_⟩
  show ⟨a + e + 4, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(a + e + 4) + (e + 1) + 4, 0, 0, 0, (e + 1) + 1⟩
  rw [show (a + e + 4) + (e + 1) + 4 = a + 2 * e + 9 from by ring,
      show (e + 1) + 1 = e + 2 from by ring]
  exact full_trans a e
