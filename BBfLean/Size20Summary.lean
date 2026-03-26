import BBfLean.FM
import BBfLean.Size20.«FM_7-15_22-3_6-77_5-2_9-5» -- author: int-y1
import BBfLean.Size20.Sz20_6_1 -- author: int-y1
import BBfLean.Size20.Sz20_6_2 -- author: int-y1
import BBfLean.Size20.Sz20_6_3 -- author: int-y1
import BBfLean.Size20.Sz20_6_4 -- author: int-y1
import BBfLean.Size20.Sz20_6_5 -- author: int-y1
import BBfLean.Size20.Sz20_6_6 -- author: int-y1

/-!
# Size 20 summary

Summary of all proofs in `Size20`.
This file provides extra confidence that the FMs are properly stated.
-/

theorem champion : haltsIn (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ 746 := «FM_7-15_22-3_6-77_5-2_9-5».fm_haltsIn_746

theorem nonhalt1 : ¬halts (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ := Sz20_6_1.nonhalt

theorem nonhalt2 : ¬halts (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ := Sz20_6_2.nonhalt

theorem nonhalt3 : ¬halts (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ := Sz20_6_3.nonhalt

theorem nonhalt4 : ¬halts (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ := Sz20_6_4.nonhalt

theorem nonhalt5 : ¬halts (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ := Sz20_6_5.nonhalt

theorem nonhalt6 : ¬halts (Q := ℕ × ℕ × ℕ × ℕ × ℕ) (fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none) ⟨1, 0, 0, 0, 0⟩ := Sz20_6_6.nonhalt
