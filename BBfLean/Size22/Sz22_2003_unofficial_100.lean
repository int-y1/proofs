import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# sz22_2003_unofficial #100: [1/30, 4/77, 21/2, 5/7, 484/3]

Vector representation:
```
-1 -1 -1  0  0
 2  0  0 -1 -1
-1  1  0  1  0
 0  0  1 -1  0
 2 -1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_100

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | _ => none

theorem r3_chain : ∀ k a b d, (⟨a+k, b, 0, d, 0⟩ : Q) [fm]⊢* ⟨a, b+k, 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 1))
    rw [show b + 1 + k = b + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]; finish

theorem r4_chain : ∀ k b c d, (⟨0, b, c, d+k, 0⟩ : Q) [fm]⊢* ⟨0, b, c+k, d, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro b c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

theorem r5r1r1_chain : ∀ k b c e,
    (⟨0, b+3*k, c+2*k, 0, e⟩ : Q) [fm]⊢* ⟨0, b, c, 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro b c e
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b c (e + 2))
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

theorem r3r2_chain : ∀ k a b e,
    (⟨a+1, b, 0, 0, e+k⟩ : Q) [fm]⊢* ⟨a+k+1, b+k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; rw [show a + 0 + 1 = a + 1 from by ring]; exists 0
  | succ k ih =>
    intro a b e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1) e)
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show b + 1 + k = b + (k + 1) from by ring]; finish

theorem main_trans (m : ℕ) :
    (⟨2*m+5, (m+2)*(m+3)/2, 0, 0, 0⟩ : Q) [fm]⊢⁺
    ⟨2*m+7, (m+3)*(m+4)/2, 0, 0, 0⟩ := by
  have hB2 : 2 * ((m+2)*(m+3)/2) = (m+2)*(m+3) := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
  have hB'2 : 2 * ((m+3)*(m+4)/2) = (m+3)*(m+4) := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
  set B := (m+2)*(m+3)/2
  set B' := (m+3)*(m+4)/2
  have hBge : B ≥ m + 3 := by
    have : (m+2)*(m+3) ≥ 2*(m+3) := by nlinarith
    omega
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, B - (m+1) = b₀ + 2 := ⟨B - m - 3, by omega⟩
  have hb₀_eq : b₀ + (2*m+6) = B' := by
    have h1 : 2 * b₀ + 2 * (m + 1) + 4 = 2 * B := by omega
    nlinarith
  -- Phase 1: R3 chain (2m+5 steps)
  have p1 : (⟨2*m+5, B, 0, 0, 0⟩ : Q) [fm]⊢* ⟨0, B+(2*m+5), 0, 2*m+5, 0⟩ := by
    have h := r3_chain (2*m+5) 0 B 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 chain (2m+5 steps)
  have p2 : (⟨0, B+(2*m+5), 0, 2*m+5, 0⟩ : Q) [fm]⊢* ⟨0, B+(2*m+5), 2*m+5, 0, 0⟩ := by
    have h := r4_chain (2*m+5) (B+(2*m+5)) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5R1R1 chain (m+2 rounds)
  have p3 : (⟨0, B+(2*m+5), 2*m+5, 0, 0⟩ : Q) [fm]⊢* ⟨0, B-(m+1), 1, 0, 2*(m+2)⟩ := by
    have h := r5r1r1_chain (m+2) (B-(m+1)) 1 0
    simp only [Nat.zero_add] at h
    rw [show B - (m + 1) + 3 * (m + 2) = B + (2 * m + 5) from by omega,
        show 1 + 2 * (m + 2) = 2 * m + 5 from by ring] at h
    exact h
  -- Phase 3b: R5, R1 (2 steps)
  have p3b : (⟨0, B-(m+1), 1, 0, 2*(m+2)⟩ : Q) [fm]⊢⁺ ⟨1, b₀, 0, 0, 2*(m+2)+2⟩ := by
    rw [hb₀]; step fm; step fm; finish
  -- Phase 4: R3R2 chain (2m+6 pairs)
  have p4 : (⟨1, b₀, 0, 0, 2*(m+2)+2⟩ : Q) [fm]⊢* ⟨2*m+7, B', 0, 0, 0⟩ := by
    have h := r3r2_chain (2*m+6) 0 b₀ 0
    simp only [Nat.zero_add] at h
    rw [show (2*m+6 : ℕ) + 1 = 2*m+7 from by ring, hb₀_eq] at h
    rw [show 2*(m+2)+2 = 2*m+6 from by ring]
    exact h
  -- Compose: (⊢* + ⊢* + ⊢*) + (⊢⁺ + ⊢*) = ⊢⁺
  exact stepStar_stepPlus_stepPlus (stepStar_trans (stepStar_trans p1 p2) p3)
    (stepPlus_stepStar_stepPlus p3b p4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 3, 0, 0, 0⟩) (by execute fm 27)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨2*m+5, (m+2)*(m+3)/2, 0, 0, 0⟩) 0
  intro m; exists m+1; exact main_trans m

end Sz22_2003_unofficial_100
