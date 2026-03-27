import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #13: [1/12, 25/14, 121/2, 6/5, 28/11]

Vector representation:
```
-2 -1  0  0  0
-1  0  2 -1  0
-1  0  0  0  2
 1  1 -1  0  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_13

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R5/R1 drain: k rounds, each (b-=1, d+=1, e-=1)
theorem r5_r1_drain : ∀ k b d e, ⟨0, b + k, 0, d, e + k⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih b (d + 1) e); ring_nf; finish

-- R4/R2 chain: d+1 rounds draining d, each round net (b+=1, c+=1, d-=1)
theorem r4_r2_chain : ∀ d, ∀ b c e, ⟨0, b, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, b + d + 1, c + d + 2, 0, e⟩ := by
  intro d; induction' d with d ih <;> intro b c e
  · step fm; step fm; ring_nf; finish
  rw [show (d + 1) + 1 = d + 1 + 1 from by ring]
  step fm; step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply stepStar_trans (ih (b + 1) (c + 1) e); ring_nf; finish

-- R4/R3 chain: k rounds, each round net (b+=1, c-=1, e+=2)
theorem r4_r3_chain : ∀ k, ∀ b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (b + 1) c (e + 2)); ring_nf; finish

-- Main transition: (0, b, 0, 0, e) ->+ (0, 2*b+2, 0, 0, e+b+5) when e >= b + 5
theorem main_trans (b e : ℕ) (he : e ≥ b + 5) :
    ⟨0, b, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 2 * b + 2, 0, 0, e + b + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, b, e - b⟩)
  · have h := r5_r1_drain b 0 0 (e - b)
    simp only [Nat.zero_add] at h
    rw [show e - b + b = e from by omega] at h; exact h
  rw [show e - b = (e - b - 1) + 1 from by omega]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, b, (e - b - 1) + 1⟩ = some ⟨2, 0, 0, b + 1, e - b - 1⟩; simp [fm]
  rcases b with _ | b'
  · -- b=0
    step fm; step fm
    apply stepStar_trans (c₂ := ⟨0, 0 + 2, 0, 0, e - 1 + 2 + 2 * 2⟩)
    · exact r4_r3_chain 2 0 0 (e - 1 + 2)
    simp only [Nat.zero_add]
    rw [show e - 1 + 2 + 2 * 2 = e + 5 from by omega,
        show 2 * 0 + 2 = 2 from by ring, show e + 0 + 5 = e + 5 from by ring]
    finish
  · -- b=b'+1
    rw [show e - (b' + 1) - 1 = e - b' - 2 from by omega]
    step fm; step fm
    rcases b' with _ | b''
    · -- b'=0, b=1
      apply stepStar_trans (c₂ := ⟨0, 0 + 4, 0, 0, (e - 2) + 2 * 4⟩)
      · exact r4_r3_chain 4 0 0 (e - 2)
      simp only [Nat.zero_add]
      rw [show (e - 2) + 2 * 4 = e + 6 from by omega,
          show 2 * (0 + 1) + 2 = 4 from by ring,
          show e + (0 + 1) + 5 = e + 6 from by ring]
      finish
    · -- b'=b''+1, b=b''+2
      rw [show (4 : ℕ) = 3 + 1 from by ring,
          show b'' + 1 = b'' + 1 from rfl,
          show e - (b'' + 1) - 2 = e - b'' - 3 from by omega]
      apply stepStar_trans (c₂ := ⟨0, 0 + b'' + 1, 3 + b'' + 2, 0, e - b'' - 3⟩)
      · exact r4_r2_chain b'' 0 3 (e - b'' - 3)
      rw [show 3 + b'' + 2 = 0 + (b'' + 5) from by ring,
          show 0 + b'' + 1 = b'' + 1 from by ring]
      apply stepStar_trans (c₂ := ⟨0, b'' + 1 + (b'' + 5), 0, 0, (e - b'' - 3) + 2 * (b'' + 5)⟩)
      · exact r4_r3_chain (b'' + 5) (b'' + 1) 0 (e - b'' - 3)
      rw [show b'' + 1 + (b'' + 5) = 2 * (b'' + 2) + 2 from by ring,
          show (e - b'' - 3) + 2 * (b'' + 5) = e + (b'' + 2) + 5 from by omega]
      finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 7⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b, 0, 0, e⟩ ∧ e ≥ b + 5)
  · intro c ⟨b, e, hq, he⟩; subst hq
    exact ⟨_, ⟨2 * b + 2, e + b + 5, rfl, by omega⟩, main_trans b e he⟩
  · exact ⟨2, 7, rfl, by omega⟩

end Sz22_2003_unofficial_13
