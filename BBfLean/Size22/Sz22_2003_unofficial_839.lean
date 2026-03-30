import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #839: [36/35, 25/22, 49/2, 11/3, 5/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  2  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_839

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (d + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a b d e, ⟨a + 1, b, 0, d + 2 * k, e + k⟩ [fm]⊢* ⟨a + 1 + 3 * k, b + 4 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (b + 4) d e)
    ring_nf; finish

theorem r2_chain_d0 : ∀ k, ∀ a b c e, ⟨a + k, b, c, 0, e + k⟩ [fm]⊢* ⟨a, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 2) e)
    ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ a b, ⟨a + 1, b, 2 * k, 0, 0⟩ [fm]⊢* ⟨a + 1 + 3 * k, b + 4 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (b + 4))
    ring_nf; finish

-- Phases 1-3 combined: (a+2, b+2, 0, 0, 0) →⁺ (2, 2, 0, 2a+2, b+2)
theorem phases123 (a b : ℕ) :
    ⟨a + 2, b + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨2, 2, 0, 2 * a + 2, b + 2⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 2, b + 2, 0, 0, 0⟩ = some ⟨a + 1, b + 2, 0, 2, 0⟩; simp [fm]
  rw [show a + 1 = 0 + (a + 1) from by ring]
  apply stepStar_trans (r3_chain (a + 1) 0 (b + 2) 2)
  rw [show 2 + 2 * (a + 1) = 2 * a + 4 from by ring,
      show (b + 2 : ℕ) = 0 + (b + 2) from by ring]
  apply stepStar_trans (r4_chain (b + 2) 0 (2 * a + 4) 0)
  rw [show (0 : ℕ) + (b + 2) = b + 2 from by ring]
  step fm; step fm
  finish

-- Phases 4-6 combined: (2, 2, 0, 2a+2, r+a+1) →* (t+1+3r, 4a+6+4r, 0, 0, 0)
-- where 3a+5 = (t+1)+r
theorem phases456 (a r t : ℕ) (ht : t + 1 + r = 3 * a + 5) :
    ⟨2, 2, 0, 2 * a + 2, r + (a + 1)⟩ [fm]⊢* ⟨t + 1 + 3 * r, 4 * a + 6 + 4 * r, 0, 0, 0⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * a + 2 = 0 + 2 * (a + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (a + 1) 1 2 0 r)
  rw [show 1 + 1 + 3 * (a + 1) = t + 1 + r from by omega,
      show 2 + 4 * (a + 1) = 4 * a + 6 from by ring]
  -- State: (t+1+r, 4a+6, 0, 0, r). Need to match r2_chain_d0 which has (a+k, b, c, 0, e+k).
  -- Goal has (t+1+r, ..., r). Template needs e+k in 5th pos. Set e=0, k=r: e+k = 0+r.
  -- But 0+r ≠ r definitionally. So change r → 0+r only in 5th position via show.
  -- Instead, restructure: the state is ((t+1)+r, 4a+6, 0, 0, r).
  -- Template output: (a, b, c+2k, 0, e) where a=t+1, k=r, e=0.
  -- Template input: (t+1+r, 4a+6, 0, 0, 0+r). Need goal's 5th = 0+r.
  -- Use Nat.zero_add on the template output side instead.
  have phase5 : ⟨(t + 1) + r, 4 * a + 6, 0, 0, 0 + r⟩ [fm]⊢*
      ⟨t + 1, 4 * a + 6, 0 + 2 * r, 0, 0⟩ := r2_chain_d0 r (t + 1) (4 * a + 6) 0 0
  rw [Nat.zero_add, Nat.zero_add] at phase5
  apply stepStar_trans phase5
  apply stepStar_trans (r3r1r1_chain r t (4 * a + 6))
  finish

theorem main_trans (a b : ℕ) (h1 : a + 1 ≤ b + 2) (h2 : b + 1 ≤ 4 * a + 4) :
    ⟨a + 2, b + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * b + 7, 4 * b + 10, 0, 0, 0⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, b + 2 = r + (a + 1) := ⟨b + 1 - a, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, t + 1 + r = 3 * a + 5 := ⟨3 * a + 4 - r, by omega⟩
  apply stepPlus_stepStar_stepPlus (phases123 a b)
  rw [hr]
  apply stepStar_trans (phases456 a r t ht)
  have : t + 1 + 3 * r = a + 2 * b + 7 := by omega
  have : 4 * a + 6 + 4 * r = 4 * b + 10 := by omega
  rw [‹t + 1 + 3 * r = _›, ‹4 * a + 6 + 4 * r = _›]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 2, 0, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a + 2, b + 2, 0, 0, 0⟩ ∧ a + 1 ≤ b + 2 ∧ b + 1 ≤ 4 * a + 4)
  · intro c ⟨a, b, hq, h1, h2⟩; subst hq
    refine ⟨⟨a + 2 * b + 7, 4 * b + 10, 0, 0, 0⟩,
      ⟨a + 2 * b + 5, 4 * b + 8, ?_, ?_, ?_⟩, main_trans a b h1 h2⟩
    · simp
    · omega
    · omega
  · exact ⟨0, 0, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_839
