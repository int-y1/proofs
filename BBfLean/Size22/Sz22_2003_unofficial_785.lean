import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #785: [35/6, 56/55, 121/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_785

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih d (e + 2)); ring_nf; finish

theorem r4_chain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm; apply stepStar_trans (ih (b + 1) e); ring_nf; finish

theorem r2_chain_b0 : ∀ k a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring, show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (a + 3) (d + 1) e); ring_nf; finish

theorem interleaved : ∀ b, ∀ c d f, ⟨3, b, c, d, f + c + b⟩ [fm]⊢*
    ⟨3 * c + 2 * b + 3, 0, 0, d + c + 2 * b, f⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d f
  rcases b with _ | _ | _ | b
  · have h := r2_chain_b0 c 3 d f
    rwa [show (3 : ℕ) + 3 * c = 3 * c + 2 * 0 + 3 from by ring,
         show d + c = d + c + 2 * 0 from by ring] at h
  · rw [show f + c + 1 = f + c + 1 from rfl]
    step fm
    have h := r2_chain_b0 (c + 1) 2 (d + 1) f
    rwa [show f + (c + 1) = f + c + 1 from by ring,
         show (2 : ℕ) + 3 * (c + 1) = 3 * c + 2 * 1 + 3 from by ring,
         show d + 1 + (c + 1) = d + c + 2 * 1 from by ring] at h
  · rw [show f + c + 2 = (f + c + 1) + 1 from by ring]
    step fm; step fm
    have h := r2_chain_b0 (c + 2) 1 (d + 2) f
    rwa [show f + (c + 2) = f + c + 1 + 1 from by ring,
         show d + 2 = d + 1 + 1 from by ring,
         show (1 : ℕ) + 3 * (c + 2) = 3 * c + 2 * 2 + 3 from by ring,
         show d + 1 + 1 + (c + 2) = d + c + 2 * 2 from by ring] at h
  · rw [show f + c + (b + 3) = (f + c + b) + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show (c + 1 + 1 + 1 : ℕ) = (c + 2) + 1 from by ring,
        show (f + c + b + 1 + 1 + 1 : ℕ) = (f + (c + 2) + b) + 1 from by ring]
    step fm
    have h := ih b (by omega) (c + 2) (d + 1 + 1 + 1 + 1) f
    rwa [show d + 1 + 1 + 1 + 1 = d + 4 from by ring,
         show f + (c + 2) + b = f + (c + 2) + b from rfl,
         show 3 * (c + 2) + 2 * b + 3 = 3 * c + 2 * (b + 3) + 3 from by ring,
         show d + 4 + (c + 2) + 2 * b = d + c + 2 * (b + 3) from by ring] at h

theorem main_trans : ∀ d e, ⟨d + 2, 0, 0, d, e⟩ [fm]⊢⁺ ⟨2 * d + 3, 0, 0, 2 * d + 1, e + d + 2⟩ := by
  intro d e
  apply stepStar_stepPlus_stepPlus (r3_chain (d + 2) d e)
  have h4 := r4_chain d 0 (e + 2 * (d + 2))
  rw [show (0 : ℕ) + d = d from by ring] at h4
  apply stepStar_stepPlus_stepPlus h4
  rw [show e + 2 * (d + 2) = (e + 2 * d + 3) + 1 from by ring]
  step fm
  rw [show e + 2 * d + 3 = (e + 2 * d + 2) + 1 from by ring]
  step fm
  rw [show (e + 2 * d + 2 : ℕ) = (e + d + 2) + 0 + d from by ring]
  have h := interleaved d 0 1 (e + d + 2)
  rwa [show 3 * 0 + 2 * d + 3 = 2 * d + 3 from by ring,
       show 1 + 0 + 2 * d = 2 * d + 1 from by ring,
       show (e + d + 2) + 0 = e + d + 2 from by ring] at h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨d + 2, 0, 0, d, e⟩) ⟨1, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨2 * d + 1, e + d + 2⟩, main_trans d e⟩
