import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1510: [7/15, 9/847, 50/7, 11/5, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -2
 1  0  2 -1  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1510

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R5+R2 chain
theorem r5r2_chain : ∀ k, ∀ a b e, (⟨a + k, b, 0, 0, e + 2 * k⟩ : Q) [fm]⊢*
    ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm
    rw [show b + 1 + 2 = (b + 3) from by ring,
        show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring]
    exact ih a (b + 3) e

-- R3 drain with e=0
theorem r3_drain_e0 : ∀ k, ∀ a c d, (⟨a, 0, c, d + k, 0⟩ : Q) [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d); ring_nf; finish

-- R3 drain with e=1
theorem r3_drain_e1 : ∀ k, ∀ a c d, (⟨a, 0, c, d + k, 1⟩ : Q) [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d); ring_nf; finish

-- Convenience wrappers
theorem r3_drain0 (D : ℕ) (a c : ℕ) :
    (⟨a, 0, c, D + 1, 0⟩ : Q) [fm]⊢* ⟨a + D + 1, 0, c + 2 * D + 2, 0, 0⟩ := by
  have := r3_drain_e0 (D + 1) a c 0
  rw [show 0 + (D + 1) = D + 1 from by ring,
      show a + (D + 1) = a + D + 1 from by ring,
      show c + 2 * (D + 1) = c + 2 * D + 2 from by ring] at this; exact this

theorem r3_drain1 (D : ℕ) (a c : ℕ) :
    (⟨a, 0, c, D + 1, 1⟩ : Q) [fm]⊢* ⟨a + D + 1, 0, c + 2 * D + 2, 0, 1⟩ := by
  have := r3_drain_e1 (D + 1) a c 0
  rw [show 0 + (D + 1) = D + 1 from by ring,
      show a + (D + 1) = a + D + 1 from by ring,
      show c + 2 * (D + 1) = c + 2 * D + 2 from by ring] at this; exact this

-- R4 chain
theorem r4_drain_aux : ∀ k, ∀ c a e, (⟨a, 0, c + k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c a e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c a (e + 1)); ring_nf; finish

theorem r4_chain (C : ℕ) (a e : ℕ) :
    (⟨a, 0, C + 1, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + C + 1⟩ := by
  have := r4_drain_aux (C + 1) 0 a e
  rw [show 0 + (C + 1) = C + 1 from by ring,
      show e + (C + 1) = e + C + 1 from by ring] at this
  exact this

-- R3R1R1 chain with e=0
theorem r3r1r1_e0 : ∀ k, ∀ a b d, (⟨a, b + 2 * k, 0, d + 1, 0⟩ : Q) [fm]⊢*
    ⟨a + k, b, 0, d + k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) b (d + 1)); ring_nf; finish

-- R3R1R1 chain with e=1
theorem r3r1r1_e1 : ∀ k, ∀ a b d, (⟨a, b + 2 * k, 0, d + 1, 1⟩ : Q) [fm]⊢*
    ⟨a + k, b, 0, d + k + 1, 1⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) b (d + 1)); ring_nf; finish

-- Case A: e = 4g+2. Input: (A+2g+2, 0, 0, 0, 4g+2). Output: (A+6g+5, 0, 0, 0, 6g+6).
theorem trans_A (g A : ℕ) :
    (⟨A + 2 * g + 2, 0, 0, 0, 4 * g + 2⟩ : Q) [fm]⊢⁺ ⟨A + 6 * g + 5, 0, 0, 0, 6 * g + 6⟩ := by
  -- R5+R2(2g+1)
  rw [show A + 2 * g + 2 = (A + 1) + (2 * g + 1) from by ring,
      show 4 * g + 2 = 0 + 2 * (2 * g + 1) from by ring]
  have h1 := r5r2_chain (2 * g + 1) (A + 1) 0 0
  rw [show 0 + 3 * (2 * g + 1) = 6 * g + 3 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Opening R5,R3,R1,R1
  rw [show 6 * g + 3 = (6 * g + 2) + 1 from by ring]
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm; step fm
  have h3 := r3r1r1_e0 (3 * g + 1) (A + 1) 0 1
  rw [show 1 + (3 * g + 1) + 1 = 3 * g + 3 from by ring,
      show A + 1 + (3 * g + 1) = A + 3 * g + 2 from by ring] at h3
  have : (⟨A + 1, 6 * g + 2, 0, 2, 0⟩ : Q) = ⟨A + 1, 0 + 2 * (3 * g + 1), 0, 1 + 1, 0⟩ := by ring_nf
  rw [this]
  apply stepStar_trans h3
  -- R3 drain(3g+3) + R4(6g+6)
  rw [show 3 * g + 3 = (3 * g + 2) + 1 from by ring]
  apply stepStar_trans (r3_drain0 (3 * g + 2) (A + 3 * g + 2) 0)
  rw [show A + 3 * g + 2 + (3 * g + 2) + 1 = A + 6 * g + 5 from by ring,
      show 0 + 2 * (3 * g + 2) + 2 = (6 * g + 5) + 1 from by ring]
  apply stepStar_trans (r4_chain (6 * g + 5) (A + 6 * g + 5) 0)
  rw [show 0 + (6 * g + 5) + 1 = 6 * g + 6 from by ring]; finish

-- Case B: e = 4g+4. Input: (A+2g+3, 0, 0, 0, 4g+4). Output: (A+6g+8, 0, 0, 0, 6g+9).
theorem trans_B (g A : ℕ) :
    (⟨A + 2 * g + 3, 0, 0, 0, 4 * g + 4⟩ : Q) [fm]⊢⁺ ⟨A + 6 * g + 8, 0, 0, 0, 6 * g + 9⟩ := by
  rw [show A + 2 * g + 3 = (A + 1) + (2 * g + 2) from by ring,
      show 4 * g + 4 = 0 + 2 * (2 * g + 2) from by ring]
  have h1 := r5r2_chain (2 * g + 2) (A + 1) 0 0
  rw [show 0 + 3 * (2 * g + 2) = 6 * g + 6 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 6 * g + 6 = (6 * g + 5) + 1 from by ring]
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm; step fm
  have h3 := r3r1r1_e0 (3 * g + 2) (A + 1) 1 1
  rw [show 1 + (3 * g + 2) + 1 = 3 * g + 4 from by ring,
      show A + 1 + (3 * g + 2) = A + 3 * g + 3 from by ring] at h3
  have : (⟨A + 1, 6 * g + 5, 0, 2, 0⟩ : Q) = ⟨A + 1, 1 + 2 * (3 * g + 2), 0, 1 + 1, 0⟩ := by ring_nf
  rw [this]
  apply stepStar_trans h3
  -- b=1: R3,R1 then R3 drain + R4
  rw [show 3 * g + 4 = (3 * g + 3) + 1 from by ring]
  step fm; step fm
  rw [show 3 * g + 3 + 1 = (3 * g + 3) + 1 from rfl]
  apply stepStar_trans (r3_drain0 (3 * g + 3) (A + 3 * g + 3 + 1) 1)
  rw [show A + 3 * g + 3 + 1 + (3 * g + 3) + 1 = A + 6 * g + 8 from by ring,
      show 1 + 2 * (3 * g + 3) + 2 = (6 * g + 8) + 1 from by ring]
  apply stepStar_trans (r4_chain (6 * g + 8) (A + 6 * g + 8) 0)
  rw [show 0 + (6 * g + 8) + 1 = 6 * g + 9 from by ring]; finish

-- Case C: e = 4g+3. Input: (A+2g+2, 0, 0, 0, 4g+3). Output: (A+6g+5, 0, 0, 0, 6g+7).
theorem trans_C (g A : ℕ) :
    (⟨A + 2 * g + 2, 0, 0, 0, 4 * g + 3⟩ : Q) [fm]⊢⁺ ⟨A + 6 * g + 5, 0, 0, 0, 6 * g + 7⟩ := by
  rw [show A + 2 * g + 2 = (A + 1) + (2 * g + 1) from by ring,
      show 4 * g + 3 = 1 + 2 * (2 * g + 1) from by ring]
  have h1 := r5r2_chain (2 * g + 1) (A + 1) 0 1
  rw [show 0 + 3 * (2 * g + 1) = 6 * g + 3 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 6 * g + 3 = (6 * g + 2) + 1 from by ring]
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm; step fm
  have h3 := r3r1r1_e1 (3 * g + 1) (A + 1) 0 1
  rw [show 1 + (3 * g + 1) + 1 = 3 * g + 3 from by ring,
      show A + 1 + (3 * g + 1) = A + 3 * g + 2 from by ring] at h3
  have : (⟨A + 1, 6 * g + 2, 0, 2, 1⟩ : Q) = ⟨A + 1, 0 + 2 * (3 * g + 1), 0, 1 + 1, 1⟩ := by ring_nf
  rw [this]
  apply stepStar_trans h3
  rw [show 3 * g + 3 = (3 * g + 2) + 1 from by ring]
  apply stepStar_trans (r3_drain1 (3 * g + 2) (A + 3 * g + 2) 0)
  rw [show A + 3 * g + 2 + (3 * g + 2) + 1 = A + 6 * g + 5 from by ring,
      show 0 + 2 * (3 * g + 2) + 2 = (6 * g + 5) + 1 from by ring]
  apply stepStar_trans (r4_chain (6 * g + 5) (A + 6 * g + 5) 1)
  rw [show 1 + (6 * g + 5) + 1 = 6 * g + 7 from by ring]; finish

-- Case D: e = 4g+5. Input: (A+2g+3, 0, 0, 0, 4g+5). Output: (A+6g+8, 0, 0, 0, 6g+10).
theorem trans_D (g A : ℕ) :
    (⟨A + 2 * g + 3, 0, 0, 0, 4 * g + 5⟩ : Q) [fm]⊢⁺ ⟨A + 6 * g + 8, 0, 0, 0, 6 * g + 10⟩ := by
  rw [show A + 2 * g + 3 = (A + 1) + (2 * g + 2) from by ring,
      show 4 * g + 5 = 1 + 2 * (2 * g + 2) from by ring]
  have h1 := r5r2_chain (2 * g + 2) (A + 1) 0 1
  rw [show 0 + 3 * (2 * g + 2) = 6 * g + 6 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 6 * g + 6 = (6 * g + 5) + 1 from by ring]
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]; step fm; step fm
  have h3 := r3r1r1_e1 (3 * g + 2) (A + 1) 1 1
  rw [show 1 + (3 * g + 2) + 1 = 3 * g + 4 from by ring,
      show A + 1 + (3 * g + 2) = A + 3 * g + 3 from by ring] at h3
  have : (⟨A + 1, 6 * g + 5, 0, 2, 1⟩ : Q) = ⟨A + 1, 1 + 2 * (3 * g + 2), 0, 1 + 1, 1⟩ := by ring_nf
  rw [this]
  apply stepStar_trans h3
  -- b=1: R3,R1 then R3 drain + R4
  rw [show 3 * g + 4 = (3 * g + 3) + 1 from by ring]
  step fm; step fm
  rw [show 3 * g + 3 + 1 = (3 * g + 3) + 1 from rfl]
  apply stepStar_trans (r3_drain1 (3 * g + 3) (A + 3 * g + 3 + 1) 1)
  rw [show A + 3 * g + 3 + 1 + (3 * g + 3) + 1 = A + 6 * g + 8 from by ring,
      show 1 + 2 * (3 * g + 3) + 2 = (6 * g + 8) + 1 from by ring]
  apply stepStar_trans (r4_chain (6 * g + 8) (A + 6 * g + 8) 1)
  rw [show 1 + (6 * g + 8) + 1 = 6 * g + 10 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e / 2 + 1 ∧ e ≥ 2)
  · intro q ⟨a, e, hq, ha, he⟩; subst hq
    rcases Nat.even_or_odd (e / 2) with ⟨K, hK⟩ | ⟨K, hK⟩
    · rcases Nat.even_or_odd e with ⟨F, hF⟩ | ⟨F, hF⟩
      · -- e even, e/2 even: e = 4K, K >= 1. Case B: g=K-1.
        have hK1 : K ≥ 1 := by omega
        set A := a - (2 * (K - 1) + 3)
        refine ⟨⟨A + 6 * (K - 1) + 8, 0, 0, 0, 6 * (K - 1) + 9⟩,
          ⟨A + 6 * (K - 1) + 8, 6 * (K - 1) + 9, rfl, ?_, ?_⟩, ?_⟩
        · omega
        · omega
        · have ha2 : a = A + 2 * (K - 1) + 3 := by omega
          rw [ha2, show e = 4 * (K - 1) + 4 from by omega]
          exact trans_B (K - 1) A
      · -- e odd, e/2 even: e = 4K+1, K >= 1. Case D: g=K-1.
        have hK1 : K ≥ 1 := by omega
        set A := a - (2 * (K - 1) + 3)
        refine ⟨⟨A + 6 * (K - 1) + 8, 0, 0, 0, 6 * (K - 1) + 10⟩,
          ⟨A + 6 * (K - 1) + 8, 6 * (K - 1) + 10, rfl, ?_, ?_⟩, ?_⟩
        · omega
        · omega
        · have ha2 : a = A + 2 * (K - 1) + 3 := by omega
          rw [ha2, show e = 4 * (K - 1) + 5 from by omega]
          exact trans_D (K - 1) A
    · rcases Nat.even_or_odd e with ⟨F, hF⟩ | ⟨F, hF⟩
      · -- e even, e/2 odd: e = 4K+2. Case A: g=K.
        set A := a - (2 * K + 2)
        refine ⟨⟨A + 6 * K + 5, 0, 0, 0, 6 * K + 6⟩,
          ⟨A + 6 * K + 5, 6 * K + 6, rfl, ?_, ?_⟩, ?_⟩
        · omega
        · omega
        · have ha2 : a = A + 2 * K + 2 := by omega
          rw [ha2, show e = 4 * K + 2 from by omega]
          exact trans_A K A
      · -- e odd, e/2 odd: e = 4K+3. Case C: g=K.
        set A := a - (2 * K + 2)
        refine ⟨⟨A + 6 * K + 5, 0, 0, 0, 6 * K + 7⟩,
          ⟨A + 6 * K + 5, 6 * K + 7, rfl, ?_, ?_⟩, ?_⟩
        · omega
        · omega
        · have ha2 : a = A + 2 * K + 2 := by omega
          rw [ha2, show e = 4 * K + 3 from by omega]
          exact trans_C K A
  · exact ⟨2, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1510
