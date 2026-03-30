import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #851: [36/35, 5/22, 637/2, 11/3, 5/13]

Vector representation:
```
 2  2 -1 -1  0  0
-1  0  1  0 -1  0
-1  0  0  2  0  1
 0 -1  0  0  1  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_851

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+2, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R2+R1 interleaved chain. Net per round: a+=1, b+=2, d-=1, e-=1.
theorem r2r1_chain : ∀ k, ∀ a b d f,
    ⟨a + 2, b, 0, d + k, k, f⟩ [fm]⊢*
    ⟨a + k + 2, b + 2 * k, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d f)
    ring_nf; finish

-- R3 drain: (k, b, 0, d, 0, f) →* (0, b, 0, d+2k, 0, f+k)
theorem r3_drain : ∀ k, ∀ b d f,
    ⟨k, b, 0, d, 0, f⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · finish
  · step fm
    apply stepStar_trans (ih b (d + 2) (f + 1))
    ring_nf; finish

-- R4 drain: (0, k, 0, d, e, f) →* (0, 0, 0, d, e+k, f)
theorem r4_drain : ∀ k, ∀ d e f,
    ⟨0, k, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · finish
  · step fm
    apply stepStar_trans (ih d (e + 1) f)
    ring_nf; finish

-- Full cycle: (0, 0, 0, D+e+1, e, f+1) →⁺ (0, 0, 0, D+2e+4, 2e+2, f+e+2)
theorem full_cycle (D e f : ℕ) :
    ⟨0, 0, 0, D + e + 1, e, (f + 1 : ℕ)⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 2 * e + 4, 2 * e + 2, f + e + 2⟩ := by
  step fm
  step fm
  have h1 := r2r1_chain e 0 2 D f
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  apply stepStar_trans (r3_drain (e + 2) (2 + 2 * e) D f)
  apply stepStar_trans (r4_drain (2 + 2 * e) (D + 2 * (e + 2)) 0 (f + (e + 2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D e f, q = ⟨0, 0, 0, D + e + 1, e, f + 1⟩)
  · intro c ⟨D, e, f, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, D + 2 * e + 4, 2 * e + 2, f + e + 2⟩,
      ⟨D + 1, 2 * e + 2, f + e + 1, by ring_nf⟩, full_cycle D e f⟩
  · exact ⟨1, 0, 0, by ring_nf⟩
