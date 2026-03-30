import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #826: [35/6, 8/55, 143/2, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_826

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k b d, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem r3_chain : ∀ k a e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1) (f + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a c e, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 3) c e)
    ring_nf; finish

-- R1 fires k times: (a+k, b+k, c, d, e, f) →* (a, b, c+k, d+k, e, f)
theorem r1_chain : ∀ k a b c d, ⟨a + k, b + k, c, d, e, f⟩ [fm]⊢* ⟨a, b, c + k, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a b c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1) (d + 1))
    ring_nf; finish

-- Generalized interleaving by strong induction on b.
-- From (3, b, c, d, E+b+c, F) to (3+2*b+3*c, 0, 0, d+b, E, F).
-- When b >= 3: R1x3 + R2 reduces b by 3 and increases c by 2.
-- When b = 0,1,2: R1xb then R2 chain finishes.
theorem gen_interleave : ∀ b, ∀ c d E F,
    ⟨3, b, c, d, E + b + c, F⟩ [fm]⊢* ⟨3 + 2 * b + 3 * c, 0, 0, d + b, E, F⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d E F
  rcases b with _ | _ | _ | b
  · -- b = 0: r2_chain
    rw [show E + 0 + c = E + c from by ring]
    have := r2_chain c 3 0 E (d := d) (f := F)
    convert this using 2; ring_nf
  · -- b = 1
    rw [show E + 1 + c = E + (c + 1) from by ring]
    apply stepStar_trans (r1_chain 1 2 0 c d (e := E + (c + 1)) (f := F))
    have := r2_chain (c + 1) 2 0 E (d := d + 1) (f := F)
    convert this using 2; ring_nf
  · -- b = 2
    rw [show E + 2 + c = E + (c + 2) from by ring]
    apply stepStar_trans (r1_chain 2 1 0 c d (e := E + (c + 2)) (f := F))
    have := r2_chain (c + 2) 1 0 E (d := d + 2) (f := F)
    convert this using 2; ring_nf
  · -- b + 3: R1x3 + R2, then recurse with b, c+2, d+3
    rw [show E + (b + 3) + c = (E + b + (c + 2)) + 1 from by ring]
    -- R1 x 3: (3, b+3, c, d, ...) → (0, b, c+3, d+3, ...)
    apply stepStar_trans (r1_chain 3 0 b c d (e := (E + b + (c + 2)) + 1) (f := F))
    -- R2: (0, b, c+3, d+3, ...) → (3, b, c+2, d+3, ...)
    rw [show c + 3 = (c + 2) + 1 from by ring]
    step fm
    -- Recurse: ih b (by omega) (c+2) (d+3) E F
    have key := ih b (by omega) (c + 2) (d + 3) E F
    have h1 : ⟨3, b, c + 2, d + 3, E + b + (c + 2), F⟩ [fm]⊢*
        ⟨3 + 2 * b + 3 * (c + 2), 0, 0, d + 3 + b, E, F⟩ := key
    apply stepStar_trans h1
    ring_nf; finish

theorem opening : ⟨0, b, 0, 0, e + 1, f + 1⟩ [fm]⊢* ⟨3, b, 0, 1, e, f⟩ := by
  step fm; step fm; step fm; finish

theorem main_trans : ∀ d e f, e ≥ d + 1 → f ≥ 1 →
    ⟨0, 0, 0, d, e, f⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, e + d + 2, f + 2 * (d + 1)⟩ := by
  intro d e f he hf
  obtain ⟨E, rfl⟩ : ∃ E, e = E + d + 1 := ⟨e - d - 1, by omega⟩
  obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
  have h1 : ⟨0, 0, 0, d, E + d + 1, F + 1⟩ [fm]⊢* ⟨0, d, 0, 0, E + d + 1, F + 1⟩ := by
    rw [show (d : ℕ) = 0 + d from by ring]
    exact r4_chain d 0 0
  have h2 : ⟨0, d, 0, 0, E + d + 1, F + 1⟩ [fm]⊢* ⟨3, d, 0, 1, E + d, F⟩ := by
    rw [show E + d + 1 = (E + d) + 1 from by ring]
    exact opening
  have h3 : ⟨3, d, 0, 1, E + d, F⟩ [fm]⊢* ⟨2 * d + 3, 0, 0, d + 1, E, F⟩ := by
    rw [show E + d = E + d + 0 from by ring]
    have := gen_interleave d 0 1 E F
    convert this using 2; ring_nf
  have h4 : ⟨2 * d + 3, 0, 0, d + 1, E, F⟩ [fm]⊢⁺
      ⟨0, 0, 0, d + 1, E + d + 1 + (d + 2), F + 1 + 2 * (d + 1)⟩ := by
    rw [show 2 * d + 3 = 0 + (2 * d + 3) from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0 + (2 * d + 2) + 1, 0, 0, d + 1, E, F⟩ =
          some ⟨0 + (2 * d + 2), 0, 0, d + 1, E + 1, F + 1⟩
      simp [fm]
    apply stepStar_trans (r3_chain (2 * d + 2) 0 (E + 1) (F + 1))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus (stepStar_trans (stepStar_trans h1 h2) h3) h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 3⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d, e, f⟩ ∧ d ≥ 1 ∧ e ≥ d + 1 ∧ f ≥ 1)
  · intro c ⟨d, e, f, hq, hd, he, hf⟩; subst hq
    exact ⟨⟨0, 0, 0, d + 1, e + d + 2, f + 2 * (d + 1)⟩,
      ⟨d + 1, e + d + 2, f + 2 * (d + 1), rfl, by omega, by omega, by omega⟩,
      main_trans d e f he hf⟩
  · exact ⟨1, 3, 3, rfl, by omega, by omega, by omega⟩
