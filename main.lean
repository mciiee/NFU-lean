open Classical
axiom equivalence_transitivity: (p <-> q) -> (q <-> r) -> (p <-> r)
axiom contrapose_neg_elim (eq: (¬ p <-> ¬ q)):  (p <-> q)
axiom contrapose_neg_intro (eq: (p <-> q)):  (¬ p <-> ¬ q)
axiom demorgan_neg_con: ¬ (p ∧ q) -> (¬ p) ∨ (¬q)
axiom demorgan_neg_con_rev: (¬ p) ∨ (¬q) -> ¬ (p ∧ q)
axiom demorgan_neg_con_equiv: ¬ (p ∧ q) <-> (¬ p) ∨ (¬q)
axiom demorgan_neg_dis: ¬ (p ∨ q) -> (¬ p) ∧ (¬q)
axiom demorgan_neg_dis_rev: (¬ p) ∧ (¬q) -> ¬ (p ∨ q)
axiom demorgan_neg_dis_equiv: ¬ (p ∨ q) <-> (¬ p) ∧ (¬q)
axiom double_negation_intro: p -> ¬¬p
axiom double_negation_elim: (¬¬p) -> p

namespace NFU
axiom NFObject: Type
axiom IsSet: NFObject -> Prop
def IsAtom (x: NFObject) : Prop := ¬ IsSet x

axiom ElementOf : NFObject -> NFObject -> Prop
infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => λ x y => ¬ ElementOf x y

def Empty (e: NFObject) : Prop := ∀ (x: NFObject), x ∉ e
def Nonempty (A : NFObject) : Prop := ∃ (x : NFObject), x ∈ A
def SubsetOf (x a : NFObject) (_: IsSet x) (_: IsSet a) : Prop := ∀ (t : NFObject), t ∈ x → t ∈ a
infix:40 " ⊆ " => λ x y => SubsetOf x y

-- [Chapter 2]

-- Axiom of Extensionality.
axiom extensionality : ∀ (A B : NFObject), IsSet A -> IsSet B -> (∀ (x : NFObject), (x ∈ A ↔ x ∈ B)) → A = B
theorem extensionality_subset(A B : NFObject) (hA: IsSet A) (hB: IsSet B): (SubsetOf A B hA hB  ∧ SubsetOf B A hB hA) -> A = B := 
  by
  intro h
  obtain ⟨hAB, hBA⟩ := h
  apply extensionality A B
  case a =>
    apply hA
  case a =>
    apply hB
  case a => 
    intro x
    constructor
    case mp => 
      apply hAB
    case mpr =>
      apply hBA


-- Axiom of Atoms.
axiom atoms: ∀ (x: NFObject), IsAtom x -> (∀ (y: NFObject), y ∉ x)

theorem extensionality_negative: ∀ (A B : NFObject), IsSet A -> IsSet B -> (∀ (x: NFObject), ((x ∉ A) <-> (x ∉ B))) -> A = B :=
  by 
  intro A B hA hB h
  apply extensionality A B hA hB 
  intro x
  have hx := h x
  apply contrapose_neg_elim hx

-- [Chapter 3]
-- Axiom of Universal Set.
axiom universal_set: ∃ (V : NFObject), ((∀ (x: NFObject), IsSet x -> x ∈ V) ∧ IsSet V)

-- Axiom of Complements.
axiom complements: ∀ (A : NFObject), IsSet A -> ∃ (Ac: NFObject), IsSet Ac ∧ (∀ (x: NFObject), x ∈ Ac <-> x ∉ A)

-- Axiom of (Boolean) Unions.
axiom unions: ∀ (A B : NFObject), IsSet A -> IsSet B -> ∃ (AuB: NFObject), (IsSet AuB) ∧ (∀ (x: NFObject), (x ∈ A ∨ x ∈ B) <-> x ∈ AuB)

theorem intersection (A B : NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (AiB: NFObject), (IsSet AiB ∧ (∀ (x: NFObject), (((x ∈ A) ∧ (x ∈ B)) <-> (x ∈ AiB)))) := by
  obtain ⟨Ac, hAc, hAc_mem⟩ := complements A hA
  obtain ⟨Bc, hBc, hBc_mem⟩ := complements B hB
  obtain ⟨C, hC, hC_mem⟩ := unions Ac Bc hAc hBc
  obtain ⟨D, hD, hD_mem⟩ := complements C hC 

  exists D
  refine And.symm ⟨?_, hD⟩

  intro x

  have hh := hC_mem x
  rw [Decidable.and_iff_not_not_or_not]
  have hC_ap := contrapose_neg_intro (hC_mem x)
  constructor
  case mp =>
    have eq := Iff.mp (equivalence_transitivity hC_ap (Iff.symm (hD_mem x)))
    simp only [not_or] at eq
    simp only [hAc_mem x, hBc_mem x, Decidable.not_not] at eq
    simp only [not_or, Decidable.not_not]
    exact eq
  case mpr =>
    intro hCon
    simp only [not_or, Decidable.not_not]
    have eq := Iff.mpr (equivalence_transitivity hC_ap (Iff.symm (hD_mem x)))
    have hnDis := eq hCon
    rw [not_or] at hnDis
    simp only [hAc_mem x, hBc_mem x, Decidable.not_not] at hnDis
    exact hnDis
    
theorem relative_complement (A B: NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (C: NFObject), IsSet C ∧ (∀ (x: NFObject), x ∈ A ∧ x ∉ B <-> x ∈ C) := by 
  obtain ⟨Bc, hBc, hBc_mem⟩ := complements B hB
  obtain comp := intersection A Bc hA hBc
  
  match comp with 
  | ⟨C, hC, hC_comp⟩ =>
    exists C
    refine And.symm ⟨?_, hC⟩
    intro x
    have hCx_comp := hC_comp x
    rw [hBc_mem] at hCx_comp
    exact hCx_comp

theorem symmetric_difference (A B : NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (C: NFObject), IsSet C ∧ (∀ (x: NFObject), (x ∈ B ∧ x ∉ A) ∨ (x ∈ A ∧ x ∉ B) <-> x ∈ C)  := by 
  obtain ⟨AnB, hAnB, hAnB_formula⟩ := relative_complement A B hA hB
  obtain ⟨BnA, hBnA, hBnA_formula⟩ := relative_complement B A hB hA
  obtain ⟨SD, hSD, hSD_formula⟩ := unions BnA AnB hBnA hAnB 

  exists SD
  refine ⟨hSD, ?_⟩

  intro x

  obtain hSDx := hSD_formula x
  rw [<- hAnB_formula] at hSDx
  rw [<- hBnA_formula] at hSDx

  have hAnBx := hAnB_formula x

  rw [hAnB_formula]
  rw [hBnA_formula]
  rw [hSD_formula]

-- Alternative description of the symmetric difference as [(A union B)\(A intersect B)]
theorem symmetric_difference_alt (A B : NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (C: NFObject), IsSet C ∧ (∀ (x: NFObject), (x ∈ A ∨ x ∈ B) ∧ ¬ (x ∈ A ∧ x ∈ B) <-> x ∈ C)  := by 
  obtain ⟨AuB, hAuB, hAuB_formula⟩ := unions A B hA hB 
  obtain ⟨AiB, hAiB, hAiB_formula⟩ := intersection A B hA hB 
  obtain ⟨SD, hSD, hSD_formula⟩ :=  relative_complement AuB AiB hAuB hAiB

  exists SD
  refine ⟨hSD, ?_⟩

  intro x

  have hSDx := hSD_formula x
  
  rw [hAuB_formula]
  rw [hAiB_formula]
  rw [hSD_formula]

