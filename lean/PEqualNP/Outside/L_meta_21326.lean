import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21326_aux

open PEqualNP.CircuitLowerBounds

def witnessCirc : Circuit :=
  ⟨ [⟨.or, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 4]⟩,
     ⟨.or, [9, 13]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [11, 15]⟩, ⟨.and, [12, 14]⟩,
     ⟨.or, [16, 17]⟩], 18 ⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 witnessCirc := by
  simp [PEqualNP.MetaComplexity.Monotone2, witnessCirc]

end PEqualNP.Outside.L_meta_21326_aux

theorem PEqualNP.Outside.L_meta_21326 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104286 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_21326_aux.witnessCirc, PEqualNP.Outside.L_meta_21326_aux.mono, ?_, ?_⟩
  · decide
  · decide
