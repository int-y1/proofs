import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1572: [7/45, 2662/5, 5/77, 3/11, 25/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  3
 0  0  1 -1 -1
 0  1  0  0 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1572

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- Phase A: R5/R1/R1 drain chain. Each round consumes 1 from a, 4 from b, adds 2 to d.
theorem drain_chain : ∀ k, ∀ a b d,
    (⟨a + k, b + 4 * k, 0, d, 0⟩ : Q) [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; ring_nf; finish
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a b (d + 2))
    ring_nf; finish

-- Terminal case r=2: R5, R1, R2 giving ⊢⁺
theorem terminal_r2 (a d : ℕ) :
    (⟨a + 1, 2, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, d + 1, 3⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Terminal case r=1: R5, R2, R2 giving ⊢⁺
theorem terminal_r1 (a d : ℕ) :
    (⟨a + 1, 1, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a + 2, 1, 0, d, 6⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Terminal case r=3: R5, R1, R2 giving ⊢⁺
theorem terminal_r3 (a d : ℕ) :
    (⟨a + 1, 3, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1, 1, 0, d + 1, 3⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Phase B with b=0: R3/R2 interleave.
theorem r3r2_b0 : ∀ k, ∀ a e,
    (⟨a, 0, 0, k, e + 1⟩ : Q) [fm]⊢* ⟨a + k, 0, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- Phase B with b=1: R3/R2 interleave.
theorem r3r2_b1 : ∀ k, ∀ a e,
    (⟨a, 1, 0, k, e + 1⟩ : Q) [fm]⊢* ⟨a + k, 1, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- Phase C: R4 drain.
theorem r4_drain : ∀ k, ∀ a b,
    (⟨a, b, 0, 0, k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; ring_nf; finish
  | succ k ih =>
    intro a b
    step fm
    apply stepStar_trans (ih a (b + 1))
    ring_nf; finish

-- Type B transition: b%4=2
-- (F+q+1, 4q+2, 0, 0, 0) ⊢⁺ (F+2q+2, 4q+5, 0, 0, 0)
theorem trans_typeB (F q : ℕ) :
    (⟨F + q + 1, 4 * q + 2, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨F + 2 * q + 2, 4 * q + 5, 0, 0, 0⟩ := by
  have h1 : (⟨F + q + 1, 4 * q + 2, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨F + 1, 2, 0, 2 * q, 0⟩ := by
    rw [show F + q + 1 = (F + 1) + q from by ring,
        show 4 * q + 2 = 2 + 4 * q from by ring]
    have := drain_chain q (F + 1) 2 0
    rw [show 0 + 2 * q = 2 * q from by ring] at this; exact this
  have h2 : (⟨F + 1, 2, 0, 2 * q, 0⟩ : Q) [fm]⊢⁺ ⟨F + 1, 0, 0, 2 * q + 1, 3⟩ :=
    terminal_r2 F (2 * q)
  have h3 : (⟨F + 1, 0, 0, 2 * q + 1, 3⟩ : Q) [fm]⊢*
      ⟨F + 2 * q + 2, 0, 0, 0, 4 * q + 5⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl]
    apply stepStar_trans (r3r2_b0 (2 * q + 1) (F + 1) 2)
    ring_nf; finish
  have h4 : (⟨F + 2 * q + 2, 0, 0, 0, 4 * q + 5⟩ : Q) [fm]⊢*
      ⟨F + 2 * q + 2, 4 * q + 5, 0, 0, 0⟩ := by
    have := r4_drain (4 * q + 5) (F + 2 * q + 2) 0
    rw [show 0 + (4 * q + 5) = 4 * q + 5 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

-- Type A transition: b%4=1
-- (F+q+1, 4q+1, 0, 0, 0) ⊢⁺ (F+2q+2, 4q+7, 0, 0, 0)
theorem trans_typeA (F q : ℕ) :
    (⟨F + q + 1, 4 * q + 1, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨F + 2 * q + 2, 4 * q + 7, 0, 0, 0⟩ := by
  have h1 : (⟨F + q + 1, 4 * q + 1, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨F + 1, 1, 0, 2 * q, 0⟩ := by
    rw [show F + q + 1 = (F + 1) + q from by ring,
        show 4 * q + 1 = 1 + 4 * q from by ring]
    have := drain_chain q (F + 1) 1 0
    rw [show 0 + 2 * q = 2 * q from by ring] at this; exact this
  have h2 : (⟨F + 1, 1, 0, 2 * q, 0⟩ : Q) [fm]⊢⁺ ⟨F + 2, 1, 0, 2 * q, 6⟩ :=
    terminal_r1 F (2 * q)
  have h3 : (⟨F + 2, 1, 0, 2 * q, 6⟩ : Q) [fm]⊢*
      ⟨F + 2 * q + 2, 1, 0, 0, 4 * q + 6⟩ := by
    rw [show (6 : ℕ) = 5 + 1 from rfl]
    apply stepStar_trans (r3r2_b1 (2 * q) (F + 2) 5)
    ring_nf; finish
  have h4 : (⟨F + 2 * q + 2, 1, 0, 0, 4 * q + 6⟩ : Q) [fm]⊢*
      ⟨F + 2 * q + 2, 4 * q + 7, 0, 0, 0⟩ := by
    have := r4_drain (4 * q + 6) (F + 2 * q + 2) 1
    rw [show 1 + (4 * q + 6) = 4 * q + 7 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

-- Type C transition: b%4=3
-- (F+q+1, 4q+3, 0, 0, 0) ⊢⁺ (F+2q+2, 4q+6, 0, 0, 0)
theorem trans_typeC (F q : ℕ) :
    (⟨F + q + 1, 4 * q + 3, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨F + 2 * q + 2, 4 * q + 6, 0, 0, 0⟩ := by
  have h1 : (⟨F + q + 1, 4 * q + 3, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨F + 1, 3, 0, 2 * q, 0⟩ := by
    rw [show F + q + 1 = (F + 1) + q from by ring,
        show 4 * q + 3 = 3 + 4 * q from by ring]
    have := drain_chain q (F + 1) 3 0
    rw [show 0 + 2 * q = 2 * q from by ring] at this; exact this
  have h2 : (⟨F + 1, 3, 0, 2 * q, 0⟩ : Q) [fm]⊢⁺ ⟨F + 1, 1, 0, 2 * q + 1, 3⟩ :=
    terminal_r3 F (2 * q)
  have h3 : (⟨F + 1, 1, 0, 2 * q + 1, 3⟩ : Q) [fm]⊢*
      ⟨F + 2 * q + 2, 1, 0, 0, 4 * q + 5⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl]
    apply stepStar_trans (r3r2_b1 (2 * q + 1) (F + 1) 2)
    ring_nf; finish
  have h4 : (⟨F + 2 * q + 2, 1, 0, 0, 4 * q + 5⟩ : Q) [fm]⊢*
      ⟨F + 2 * q + 2, 4 * q + 6, 0, 0, 0⟩ := by
    have := r4_drain (4 * q + 5) (F + 2 * q + 2) 1
    rw [show 1 + (4 * q + 5) = 4 * q + 6 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 6, 0, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ F q',
      q = ⟨F + q' + 1, 4 * q' + 2, 0, 0, 0⟩ ∨
      q = ⟨F + q' + 1, 4 * q' + 1, 0, 0, 0⟩ ∨
      q = ⟨F + q' + 1, 4 * q' + 3, 0, 0, 0⟩)
  · intro c ⟨F, q', hq⟩
    rcases hq with rfl | rfl | rfl
    · exact ⟨⟨F + 2 * q' + 2, 4 * q' + 5, 0, 0, 0⟩,
        ⟨F + q', q' + 1, Or.inr (Or.inl (by ring_nf))⟩,
        trans_typeB F q'⟩
    · exact ⟨⟨F + 2 * q' + 2, 4 * q' + 7, 0, 0, 0⟩,
        ⟨F + q', q' + 1, Or.inr (Or.inr (by ring_nf))⟩,
        trans_typeA F q'⟩
    · exact ⟨⟨F + 2 * q' + 2, 4 * q' + 6, 0, 0, 0⟩,
        ⟨F + q', q' + 1, Or.inl (by ring_nf)⟩,
        trans_typeC F q'⟩
  · exact ⟨0, 1, Or.inl rfl⟩

end Sz22_2003_unofficial_1572
