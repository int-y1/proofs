import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #322: [18/35, 1/33, 5/3, 11/5, 3087/2]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  0  0 -1
 0 -1  1  0  0
 0  0 -1  0  1
-1  2  0  3  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_322

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+3, e⟩
  | _ => none

private theorem tuple_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ : ℕ}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) (h4 : d₁ = d₂) (h5 : e₁ = e₂) :
    (⟨a₁, b₁, c₁, d₁, e₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂, e₂⟩ := by
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

theorem pump_cd : ∀ d a b,
    ⟨a, b+1, 0, d+1, 0⟩ [fm]⊢* ⟨a+d+1, b+d+2, 0, 0, 0⟩ := by
  intro d; induction d with
  | zero => intro a b; step fm; step fm; finish
  | succ d ih =>
    intro a b; step fm; step fm
    have h := ih (a+1) (b+1)
    rw [show (⟨a + 1 + d + 1, b + 1 + d + 2, 0, 0, 0⟩ : Q) =
      ⟨a + (d + 1) + 1, b + (d + 1) + 2, 0, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl rfl] at h
    exact h

theorem drain_b : ∀ b a c,
    ⟨a, b, c, 0, 0⟩ [fm]⊢* ⟨a, 0, b+c, 0, 0⟩ := by
  intro b; induction b with
  | zero => intro a c; simp; finish
  | succ b ih =>
    intro a c; step fm
    have h := ih a (c+1)
    rw [show (⟨a, 0, b + (c + 1), 0, 0⟩ : Q) = ⟨a, 0, b + 1 + c, 0, 0⟩
      from tuple_eq rfl rfl (by ring) rfl rfl] at h
    exact h

theorem drain_c : ∀ c a e,
    ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, c+e⟩ := by
  intro c; induction c with
  | zero => intro a e; simp; finish
  | succ c ih =>
    intro a e; step fm
    have h := ih a (e+1)
    rw [show (⟨a, 0, 0, 0, c + (e + 1)⟩ : Q) = ⟨a, 0, 0, 0, c + 1 + e⟩
      from tuple_eq rfl rfl rfl rfl (by ring)] at h
    exact h

theorem drain_e : ∀ k a d e,
    ⟨a+k, 0, 0, d, e+2*k⟩ [fm]⊢* ⟨a, 0, 0, d+3*k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; simp; finish
  | succ k ih =>
    intro a d e
    rw [show (⟨a + (k + 1), 0, 0, d, e + 2 * (k + 1)⟩ : Q) =
      ⟨a + k + 1, 0, 0, d, e + 2 * k + 1 + 1⟩
      from tuple_eq (by ring) rfl rfl rfl (by ring)]
    step fm; step fm; step fm
    have h := ih a (d + 3) e
    rw [show (⟨a, 0, 0, d + 3 + 3 * k, e⟩ : Q) = ⟨a, 0, 0, d + 3 * (k + 1), e⟩
      from tuple_eq rfl rfl rfl (by ring) rfl] at h
    exact h

theorem handle_odd : ⟨a+1, 0, 0, d, 1⟩ [fm]⊢⁺ ⟨a+1, 2, 0, d+2, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem even_trans : ⟨A+k+1, 0, 0, 0, 2*k⟩ [fm]⊢⁺ ⟨A+3*k+3, 0, 0, 0, 3*k+5⟩ := by
  rw [show (⟨A + k + 1, 0, 0, 0, 2 * k⟩ : Q) = ⟨(A + 1) + k, 0, 0, 0, 0 + 2 * k⟩
    from tuple_eq (by ring) rfl rfl rfl (by ring)]
  apply stepStar_stepPlus_stepPlus (drain_e k (A+1) 0 0)
  rw [show (⟨A + 1, 0, 0, 0 + 3 * k, 0⟩ : Q) = ⟨A + 1, 0, 0, 3 * k, 0⟩
    from tuple_eq rfl rfl rfl (by ring) rfl]
  step fm
  rw [show (⟨A, 2, 0, 3 * k + 3, 0⟩ : Q) = ⟨A, 1 + 1, 0, (3 * k + 2) + 1, 0⟩
    from tuple_eq rfl rfl rfl (by ring) rfl]
  apply stepStar_trans (pump_cd (3*k+2) A 1)
  rw [show (⟨A + (3 * k + 2) + 1, 1 + (3 * k + 2) + 2, 0, 0, 0⟩ : Q) =
    ⟨A + 3 * k + 3, 3 * k + 5, 0, 0, 0⟩ from tuple_eq (by ring) (by ring) rfl rfl rfl]
  apply stepStar_trans (drain_b (3*k+5) (A+3*k+3) 0)
  rw [show (⟨A + 3 * k + 3, 0, 3 * k + 5 + 0, 0, 0⟩ : Q) =
    ⟨A + 3 * k + 3, 0, 3 * k + 5, 0, 0⟩ from tuple_eq rfl rfl (by ring) rfl rfl]
  apply stepStar_trans (drain_c (3*k+5) (A+3*k+3) 0)
  rw [show (⟨A + 3 * k + 3, 0, 0, 0, 3 * k + 5 + 0⟩ : Q) =
    ⟨A + 3 * k + 3, 0, 0, 0, 3 * k + 5⟩ from tuple_eq rfl rfl rfl rfl (by ring)]
  finish

theorem odd_trans : ⟨A+k+1, 0, 0, 0, 2*k+1⟩ [fm]⊢⁺ ⟨A+3*k+3, 0, 0, 0, 3*k+4⟩ := by
  rw [show (⟨A + k + 1, 0, 0, 0, 2 * k + 1⟩ : Q) = ⟨(A + 1) + k, 0, 0, 0, 1 + 2 * k⟩
    from tuple_eq (by ring) rfl rfl rfl (by ring)]
  apply stepStar_stepPlus_stepPlus (drain_e k (A+1) 0 1)
  rw [show (⟨A + 1, 0, 0, 0 + 3 * k, 1⟩ : Q) = ⟨A + 0 + 1, 0, 0, 3 * k, 1⟩
    from tuple_eq (by ring) rfl rfl (by ring) rfl]
  apply stepPlus_stepStar_stepPlus (handle_odd (a := A + 0) (d := 3*k))
  rw [show (⟨A + 0 + 1, 2, 0, 3 * k + 2, 0⟩ : Q) = ⟨A + 1, 1 + 1, 0, (3 * k + 1) + 1, 0⟩
    from tuple_eq (by ring) rfl rfl (by ring) rfl]
  apply stepStar_trans (pump_cd (3*k+1) (A+1) 1)
  rw [show (⟨A + 1 + (3 * k + 1) + 1, 1 + (3 * k + 1) + 2, 0, 0, 0⟩ : Q) =
    ⟨A + 3 * k + 3, 3 * k + 4, 0, 0, 0⟩ from tuple_eq (by ring) (by ring) rfl rfl rfl]
  apply stepStar_trans (drain_b (3*k+4) (A+3*k+3) 0)
  rw [show (⟨A + 3 * k + 3, 0, 3 * k + 4 + 0, 0, 0⟩ : Q) =
    ⟨A + 3 * k + 3, 0, 3 * k + 4, 0, 0⟩ from tuple_eq rfl rfl (by ring) rfl rfl]
  apply stepStar_trans (drain_c (3*k+4) (A+3*k+3) 0)
  rw [show (⟨A + 3 * k + 3, 0, 0, 0, 3 * k + 4 + 0⟩ : Q) =
    ⟨A + 3 * k + 3, 0, 0, 0, 3 * k + 4⟩ from tuple_eq rfl rfl rfl rfl (by ring)]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩)
  · execute fm 17
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a > e)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      obtain ⟨A, rfl⟩ : ∃ A, a = A + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨A + 3*k + 3, 0, 0, 0, 3*k + 5⟩,
        ⟨A + 3*k + 3, 3*k + 5, rfl, by omega⟩,
        by rw [show (⟨A + k + 1, 0, 0, 0, k + k⟩ : Q) = ⟨A + k + 1, 0, 0, 0, 2 * k⟩
              from tuple_eq rfl rfl rfl rfl (by ring)]
           exact even_trans⟩
    · subst hk
      obtain ⟨A, rfl⟩ : ∃ A, a = A + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨A + 3*k + 3, 0, 0, 0, 3*k + 4⟩,
        ⟨A + 3*k + 3, 3*k + 4, rfl, by omega⟩, odd_trans⟩
  · exact ⟨3, 5, rfl, by omega⟩

end Sz22_2003_unofficial_322
