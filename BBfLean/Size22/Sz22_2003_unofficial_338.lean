import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #338: [189/10, 2/33, 121/2, 5/7, 14/11]

Vector representation:
```
-1  3 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_338

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Rule 4 loop: move d to c
theorem rule4_loop : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · rw [Nat.add_zero]; exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

-- Rule 3 loop: drain a to e (when b=0, c=0)
theorem rule3_loop : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · rw [Nat.add_zero]; exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2))
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

-- Phase 2 inner: consume c via alternating rule1/rule2
theorem phase2_inner : ∀ c j e,
    ⟨1, 2 * j, c + 1, j + 1, e + c⟩ [fm]⊢* ⟨0, 2 * (c + j) + 3, 0, c + j + 2, e⟩ := by
  intro c; induction' c with c ih <;> intro j e
  · step fm; ring_nf; finish
  · rw [show e + (c + 1) = (e + c) + 1 from by ring]
    step fm
    step fm
    rw [show 2 * j + 2 = 2 * (j + 1) from by ring]
    apply stepStar_trans (ih (j + 1) e)
    rw [show c + (j + 1) = (c + 1) + j from by ring]; finish

-- Full phase 2: (0, 0, c+1, 0, e+c+1) ->* (0, 2*c+3, 0, c+2, e)
theorem phase2 : ∀ c e,
    ⟨0, 0, c + 1, 0, e + c + 1⟩ [fm]⊢* ⟨0, 2 * c + 3, 0, c + 2, e⟩ := by
  intro c e
  step fm
  show ⟨1, 0, c + 1, 1, e + c⟩ [fm]⊢* ⟨0, 2 * c + 3, 0, c + 2, e⟩
  have h := phase2_inner c 0 e
  simp only [Nat.zero_add, show 2 * (c + 0) + 3 = 2 * c + 3 from by ring,
             show c + 0 + 2 = c + 2 from by ring] at h
  exact h

-- Drain: (a, b, 0, d, e) ->* (0, 0, 0, d, 2*a+b+e) when a >= 1
-- By strong induction on 2*b+a
theorem drain_pos : ∀ M, ∀ a b d e, 2 * b + a ≤ M → a ≥ 1 →
    ⟨a, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, 2 * a + b + e⟩ := by
  intro M; induction' M using Nat.strongRecOn with M IH
  intro a b d e hmeas ha
  -- Case split on b and e
  match b, e with
  | 0, e =>
    -- b = 0: use rule3_loop
    have h := rule3_loop a d e
    rw [show e + 2 * a = 2 * a + 0 + e from by ring] at h; exact h
  | b + 1, 0 =>
    -- b >= 1, e = 0: rule3, then rule2, then IH
    match a with
    | 0 => omega
    | 1 =>
      -- (1, b+1, 0, d, 0) -> rule3 -> (0, b+1, 0, d, 2) -> rule2 -> (1, b, 0, d, 1)
      step fm; step fm
      apply stepStar_trans (IH (2 * b + 1) (by omega) 1 b d 1 (by omega) (by omega))
      rw [show 2 * 1 + b + 1 = 2 * 1 + (b + 1) + 0 from by ring]; finish
    | a + 2 =>
      -- (a+2, b+1, 0, d, 0) -> rule3 -> (a+1, b+1, 0, d, 2) -> IH
      step fm
      apply stepStar_trans (IH (2 * (b + 1) + (a + 1)) (by omega) (a + 1) (b + 1) d 2 (by omega) (by omega))
      rw [show 2 * (a + 1) + (b + 1) + 2 = 2 * (a + 2) + (b + 1) + 0 from by ring]; finish
  | b + 1, e + 1 =>
    -- b >= 1, e >= 1: rule2, then IH
    step fm
    apply stepStar_trans (IH (2 * b + (a + 1)) (by omega) (a + 1) b d e (by omega) (by omega))
    rw [show 2 * (a + 1) + b + e = 2 * a + (b + 1) + (e + 1) from by ring]; finish

-- Drain from (0, b, 0, d, e) with e >= 1
theorem drain_be : ∀ b d e, ⟨0, b, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d, b + e + 1⟩ := by
  intro b d e
  match b with
  | 0 => rw [show 0 + e + 1 = e + 1 from by ring]; exists 0
  | b + 1 =>
    step fm
    apply stepStar_trans (drain_pos (2 * b + 1) 1 b d e (by omega) (by omega))
    rw [show 2 * 1 + b + e = b + 1 + e + 1 from by ring]; finish

-- Main cycle: (0, 0, 0, d+1, e) ->+ (0, 0, 0, d+2, e+d+2) when e >= d+3
theorem main_cycle : ∀ d e, e ≥ d + 3 →
    ⟨0, 0, 0, d + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, e + d + 2⟩ := by
  intro d e he
  -- Phase 1: move d+1 to c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, d + 1, 0, e⟩)
  · have h := rule4_loop (d + 1) 0 e
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: consume c
  -- Need to show (0, 0, d+1, 0, e) ->+ (0, 2*d+3, 0, d+2, e-d-1)
  -- (0, 0, d+1, 0, e) with d+1 = (d)+1 and e = (e-d-1) + d + 1
  set f := e - d - 1 with hf_def
  have hf : e = f + d + 1 := by omega
  rw [hf]
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * d + 3, 0, d + 2, f⟩)
  · exact phase2 d f
  -- Phase 3: drain b and e
  -- (0, 2*d+3, 0, d+2, f) ->+ (0, 0, 0, d+2, 2*d+3+f)
  -- 2*d+3+f = 2*d+3+(e-d-1) = e+d+2
  have hfge : f ≥ 1 := by omega
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  rw [hf']
  have h := drain_be (2 * d + 3) (d + 2) f'
  have htarget : 2 * d + 3 + f' + 1 = f' + 1 + d + 1 + d + 2 := by omega
  rw [htarget] at h
  exact stepStar_stepPlus h (by
    intro heq
    have := congr_arg (fun q : Q => q.2.1) heq
    simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro q ⟨d, e, hq, he⟩; subst hq
    match d with
    | 0 =>
      -- (0, 0, 0, 0, e) with e >= 2: rule5 -> (1, 0, 0, 1, e-1) -> rule3 -> (0, 0, 0, 1, e+1)
      obtain ⟨e', he'⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
      subst he'
      refine ⟨⟨0, 0, 0, 1, e' + 3⟩, ⟨1, e' + 3, rfl, by omega⟩, ?_⟩
      step fm; step fm; finish
    | d + 1 =>
      refine ⟨⟨0, 0, 0, d + 2, e + d + 2⟩, ⟨d + 2, e + d + 2, rfl, by omega⟩, ?_⟩
      exact main_cycle d e (by omega)
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_338
