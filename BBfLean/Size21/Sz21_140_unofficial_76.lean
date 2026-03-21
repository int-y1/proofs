import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #76: [4/15, 9/14, 55/2, 7/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_76

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: a → c,e
theorem r3_repeat : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 repeated: c → d
theorem r4_repeat : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- First round: (0, 0, 0, d+3, e+1) → (0, 5, 0, d, e)
theorem first_round : ∀ d e, ⟨0, 0, 0, d+3, e+1⟩ [fm]⊢⁺ ⟨0, 5, 0, d, e⟩ := by
  intro d e
  step fm
  rw [show d + 3 = d + 2 + 1 from by ring]
  step fm
  step fm
  rw [show d + 2 = d + 1 + 1 from by ring]
  step fm
  step fm
  finish

-- Subsequent round: (0, b+1, 0, d+3, e+1) → (0, b+6, 0, d, e)
theorem next_round : ∀ b d e, ⟨0, b+1, 0, d+3, e+1⟩ [fm]⊢⁺ ⟨0, b+6, 0, d, e⟩ := by
  intro b d e
  step fm
  step fm
  rw [show d + 3 = d + 2 + 1 from by ring]
  step fm
  rw [show d + 2 = d + 1 + 1 from by ring]
  step fm
  step fm
  ring_nf; finish

-- K+1 rounds
theorem rounds : ∀ K, ∀ d e, ⟨0, 0, 0, 3*(K+1)+d, (K+1)+e⟩ [fm]⊢* ⟨0, 5*(K+1), 0, d, e⟩ := by
  intro K; induction' K with K ih <;> intro d e
  · rw [show 3 * (0 + 1) + d = d + 3 from by ring,
        show (0 + 1) + e = e + 1 from by ring]
    exact stepPlus_stepStar (first_round d e)
  · rw [show 3 * (K + 1 + 1) + d = 3 * (K + 1) + (d + 3) from by ring,
        show (K + 1 + 1) + e = (K + 1) + (e + 1) from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1))
    rw [show 5 * (K + 1) = (5 * K + 5 - 1) + 1 from by omega]
    exact stepPlus_stepStar (next_round _ d e)

-- Drain: R3/R1 alternation
theorem drain : ∀ k, ∀ a b e, ⟨a+1, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+1+k, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  have h := ih (a + 1) b (e + 1)
  refine stepStar_trans h ?_
  ring_nf; finish

-- Remainder r=0
theorem remainder0 : ∀ b e, ⟨0, b+1, 0, 0, e+1⟩ [fm]⊢⁺ ⟨b+3, 0, 0, 0, e+b⟩ := by
  intro b e
  step fm
  step fm
  have h := drain b 2 0 e
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Remainder r=1
theorem remainder1 : ∀ b e, ⟨0, b+1, 0, 1, e+1⟩ [fm]⊢⁺ ⟨b+4, 0, 0, 0, e+b+2⟩ := by
  intro b e
  step fm
  step fm
  step fm
  have h := drain (b + 2) 1 0 e
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Remainder r=2
theorem remainder2 : ∀ b e, ⟨0, b+1, 0, 2, e+1⟩ [fm]⊢⁺ ⟨b+5, 0, 0, 0, e+b+4⟩ := by
  intro b e
  step fm
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  step fm
  have h := drain (b + 4) 0 0 e
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- mod 0: main transition
theorem main_trans_mod0 : ∀ m e, ⟨3*m+3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5*m+7, 0, 0, 0, e+7*m+5⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*m+3, 0, e+(3*m+3)⟩)
  · have h := r3_repeat (3*m+3) 0 0 e; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m+3, e+(3*m+3)⟩)
  · have h := r4_repeat (3*m+3) 0 0 (e+(3*m+3)); simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*(m+1), 0, 0, e+2*m+2⟩)
  · have h := rounds m 0 (e+2*m+2)
    have : 3 * (m + 1) + 0 = 3 * m + 3 := by ring
    have : (m + 1) + (e + 2 * m + 2) = e + (3 * m + 3) := by ring
    rw [‹3 * (m + 1) + 0 = 3 * m + 3›, ‹(m + 1) + (e + 2 * m + 2) = e + (3 * m + 3)›] at h
    exact h
  rw [show 5 * (m + 1) = (5*m+4) + 1 from by ring,
      show e + 2*m + 2 = (e+2*m+1) + 1 from by ring]
  have h := remainder0 (5*m+4) (e+2*m+1)
  refine stepPlus_stepStar_stepPlus h ?_
  ring_nf; finish

-- mod 1: main transition
theorem main_trans_mod1 : ∀ m e, ⟨3*m+4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5*m+8, 0, 0, 0, e+7*m+8⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*m+4, 0, e+(3*m+4)⟩)
  · have h := r3_repeat (3*m+4) 0 0 e; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m+4, e+(3*m+4)⟩)
  · have h := r4_repeat (3*m+4) 0 0 (e+(3*m+4)); simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*(m+1), 0, 1, e+2*m+3⟩)
  · have h := rounds m 1 (e+2*m+3)
    have : 3 * (m + 1) + 1 = 3 * m + 4 := by ring
    have : (m + 1) + (e + 2 * m + 3) = e + (3 * m + 4) := by ring
    rw [‹3 * (m + 1) + 1 = 3 * m + 4›, ‹(m + 1) + (e + 2 * m + 3) = e + (3 * m + 4)›] at h
    exact h
  rw [show 5 * (m + 1) = (5*m+4) + 1 from by ring,
      show e + 2 * m + 3 = (e+2*m+2) + 1 from by ring]
  have h := remainder1 (5*m+4) (e+2*m+2)
  refine stepPlus_stepStar_stepPlus h ?_
  ring_nf; finish

-- mod 2: main transition
theorem main_trans_mod2 : ∀ m e, ⟨3*m+5, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5*m+9, 0, 0, 0, e+7*m+11⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*m+5, 0, e+(3*m+5)⟩)
  · have h := r3_repeat (3*m+5) 0 0 e; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m+5, e+(3*m+5)⟩)
  · have h := r4_repeat (3*m+5) 0 0 (e+(3*m+5)); simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*(m+1), 0, 2, e+2*m+4⟩)
  · have h := rounds m 2 (e+2*m+4)
    have : 3 * (m + 1) + 2 = 3 * m + 5 := by ring
    have : (m + 1) + (e + 2 * m + 4) = e + (3 * m + 5) := by ring
    rw [‹3 * (m + 1) + 2 = 3 * m + 5›, ‹(m + 1) + (e + 2 * m + 4) = e + (3 * m + 5)›] at h
    exact h
  rw [show 5 * (m + 1) = (5*m+4) + 1 from by ring,
      show e + 2 * m + 4 = (e+2*m+3) + 1 from by ring]
  have h := remainder2 (5*m+4) (e+2*m+3)
  refine stepPlus_stepStar_stepPlus h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a+3, 0, 0, 0, e⟩)
  · intro q ⟨a, e, hq⟩
    subst hq
    have hmod : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · have ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0; subst hm
      exact ⟨⟨5*m+7, 0, 0, 0, e+7*m+5⟩, ⟨5*m+4, e+7*m+5, by ring_nf⟩, main_trans_mod0 m e⟩
    · have ha : a = 3 * (a / 3) + 1 := by omega
      rw [ha]; set m := a / 3
      exact ⟨⟨5*m+8, 0, 0, 0, e+7*m+8⟩, ⟨5*m+5, e+7*m+8, by ring_nf⟩, main_trans_mod1 m e⟩
    · have ha : a = 3 * (a / 3) + 2 := by omega
      rw [ha]; set m := a / 3
      exact ⟨⟨5*m+9, 0, 0, 0, e+7*m+11⟩, ⟨5*m+6, e+7*m+11, by ring_nf⟩, main_trans_mod2 m e⟩
  · exact ⟨0, 1, by ring_nf⟩
