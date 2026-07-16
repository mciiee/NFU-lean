open Classical
axiom conjunction_distributivity: p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r)
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

def Empty (E: NFObject) : Prop := ∀ (x: NFObject), x ∉ E
def Nonempty (A : NFObject) : Prop := ∃ (x : NFObject), x ∈ A
def SubsetOf (x a : NFObject) (_: IsSet x) (_: IsSet a) : Prop := ∀ (t : NFObject), t ∈ x → t ∈ a
infix:40 " ⊆ " => λ x y => SubsetOf x y
def Disjoint (A B: NFObject) (_: IsSet A) (_: IsSet B): Prop := ∀ (x: NFObject), x ∉ A ∨ x ∉ B
def Intersection (A B: NFObject) (_: IsSet A) (_: IsSet B) (C: NFObject) : Prop := ∀ (x: NFObject), (x ∈ A ∧ x ∈ B) <-> x ∈ C
def SymmetricDifference (A B: NFObject) (_: IsSet A) (_: IsSet B) (C: NFObject) : Prop := ∀ (x: NFObject), (x ∈ B ∧ x ∉ A) ∨ (x ∈ A ∧ x ∉ B) <-> x ∈ C
/- def EmptyIntersection (A B: NFObject) := -/
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
axiom universal_set: ∃ (V : NFObject), IsSet V ∧  (∀ (x: NFObject),  x ∈ V)

-- Axiom of Complements.
axiom complements: ∀ (A : NFObject), IsSet A -> ∃ (Ac: NFObject), IsSet Ac ∧ (∀ (x: NFObject), x ∈ Ac <-> x ∉ A)

theorem empty_exists: ∃ (E: NFObject), IsSet E ∧ Empty E := by 
  obtain ⟨V, hV, hV_formula⟩ := universal_set
  obtain ⟨Vc, hVc, hVc_formula⟩ := complements V hV

  exists Vc
  refine ⟨hVc, ?_⟩ 
  
  intro x
  
  obtain hVx := hV_formula x
  obtain hVcx := Iff.symm (contrapose_neg_intro (hVc_formula x))
  rw [not_not] at hVcx  
  
  apply hVcx.mp hVx


-- Axiom of (Boolean) Unions.
axiom unions: ∀ (A B : NFObject), IsSet A -> IsSet B -> ∃ (AuB: NFObject), (IsSet AuB) ∧ (∀ (x: NFObject), (x ∈ A ∨ x ∈ B) <-> x ∈ AuB)

theorem intersection (A B : NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (AiB: NFObject), IsSet AiB ∧ Intersection A B hA hB AiB := by
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

theorem symmetric_difference (A B : NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (C: NFObject), IsSet C ∧ SymmetricDifference A B hA hB C  := by 
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
theorem symmetric_difference_alt (A B : NFObject) (hA: IsSet A) (hB: IsSet B): ∃ (C: NFObject), IsSet C ∧ (∀ (x: NFObject), (x ∈ A ∨ x ∈ B) ∧ ¬ (x ∈ A ∧ x ∈ B) <-> x ∈ C) := by 
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

  
theorem empty_is_subset (A: NFObject) (hA: IsSet A) (E: NFObject) (hE: IsSet E) (hEe: Empty E) : SubsetOf E A hE hA := by
  rw [SubsetOf]
  rw [Empty] at hEe
  
  intro x

  obtain hEex := hEe x
  intro hinE

  have contra := And.intro hEex hinE
  rw [not_and_self_iff] at contra

  apply False.elim contra


theorem subset_iff_idempotent_union (A B : NFObject) (hA: IsSet A) (hB: IsSet B): SubsetOf A B hA hB <-> ∀ (x: NFObject), x ∈ A ∨ x ∈ B <-> x ∈ B :=
  by
  obtain ⟨AuB, hAuB, hAuB_formula⟩ := unions A B hA hB

  constructor
  case mp =>
    intro hSub
    rw [SubsetOf] at hSub
    intro x
    have hSubx := hSub x
    exact or_iff_right_iff_imp.mpr (hSub x)
  
  case mpr =>
    intro hUni
    rw [SubsetOf]
    intro x
    have hUnix := hUni x
    refine fun a => hUnix.mp (Or.inl a)

 
theorem disjoint_if_empty_intersection (A B : NFObject) (hA: IsSet A) (hB: IsSet B): Disjoint A B hA hB <-> ∃ (E: NFObject), IsSet E ∧ Empty E ∧  Intersection A B hA hB E := by

  constructor 
  case mp =>
    intro hDis
    rw [Disjoint] at hDis
    obtain ⟨E, hEs, hEe⟩ := empty_exists
    exists E
    refine ⟨hEs, hEe, ?_⟩ 
    rw [Intersection]

    intro x

    have hDisx := hDis x

    constructor
    case mpr =>
      rw [Empty] at hEe
      have hEex := hEe x
      intro hIne
      have contra := And.intro hEex hIne
      rw [not_and_self_iff] at contra
      apply False.elim contra

    case mp =>
      rw [<- not_and_iff_not_or_not] at hDisx
      intro hInt 
      have contra := And.intro hDisx hInt
      rw [not_and_self_iff] at contra
      apply False.elim contra


  case mpr =>
    intro hEmpt
    obtain ⟨E, hEs, ⟨hEe, hIntr⟩⟩ := hEmpt
    rw [Intersection] at hIntr
    rw [Disjoint]
    
    intro x
    rw [<- not_and_iff_not_or_not]
    
    have hIntrx := Iff.symm (contrapose_neg_intro (hIntr x))
    rw [Empty] at hEe

    have hEisE := hEe x

    apply hIntrx.mp (hEisE)
    
-- Axiom of Set Union
axiom set_union (A: NFObject) (hA: IsSet A): (∀ (x:NFObject), x ∈ A -> IsSet x) -> ∃ (S: NFObject), IsSet S ∧ (∀ (x: NFObject), x ∈ S <-> ∃ (B: NFObject), IsSet B ∧ B ∈ A ∧ x ∈ B)

-- Exercises [Chapter 2]
-- (b)
theorem symmetric_difference_symm (A B: NFObject) (hA: IsSet A) (hB: IsSet B) (hAdB: SymmetricDifference A B hA hB C) (hC: IsSet C) (hBdA: SymmetricDifference B A hB hA D) (hD: IsSet D): C = D := by
  /- rw [SymmetricDifference] at hAdB -/
  /- rw [SymmetricDifference] at hBdA -/
  apply extensionality C D hC hD
  intro x
  rw [SymmetricDifference] at hAdB
  rw [SymmetricDifference] at hBdA

  obtain hAdBx := hAdB x
  obtain hBdAx := hBdA x
  rw [or_comm] at hAdBx
  apply equivalence_transitivity (Iff.symm hAdBx) hBdAx

-- (A + B) + C = A + (B + C)
-- X + C = A + Z
-- Y = W
theorem symmetric_difference_associative (A B C : NFObject) (hA : IsSet A) (hB : IsSet B) (hC : IsSet C) (X : NFObject) (hX : IsSet X) (hXdef : SymmetricDifference A B hA hB X) (Y : NFObject) (hY : IsSet Y) (hYdef : SymmetricDifference X C hX hC Y) (Z : NFObject) (hZ : IsSet Z) (hZdef : SymmetricDifference B C hB hC Z) (W : NFObject) (hW : IsSet W) (hWdef : SymmetricDifference A Z hA hZ W) : Y = W := by
  apply extensionality Y W hY hW 
  intro x 
  have hYdefx := hYdef x
  have hWdefx := hWdef x
  have hXdefx := hXdef x
  have hZdefx := hZdef x

  simp only [not] at hYdefx
  simp only [not] at hWdefx
  simp only  [not] at hXdefx
  simp only [not] at hZdefx
  
  rw [<- hZdefx] at hWdefx
  rw [<- hXdefx] at hYdefx

  rw [not_or] at hYdefx
  rw [not_and_iff_not_or_not, not_not] at hYdefx
  rw [not_and_iff_not_or_not, not_not] at hYdefx
  
  constructor 
  case mp =>
    intro hxinY

    rcases hYdefx.mpr hxinY with ⟨hInC, hnSAB⟩ | ⟨⟨hInB, hnInA⟩ | ⟨hInA, hnInB⟩, hnInC⟩ 
    case inl =>
      rw [<- Decidable.imp_iff_not_or] at hnSAB
      rw [<- Decidable.imp_iff_not_or] at hnSAB
      rw [<- iff_def] at hnSAB

      rw [hnSAB] at hWdefx

      rw [<- hWdefx]
      by_cases hInA: x ∈ A
      case pos =>
        refine Or.inr ?_
        refine And.intro hInA ?_
        simp only [not_or, not_and, Decidable.not_not]
        exact ⟨fun a => hInA, fun a => hInC⟩
      case neg =>
        refine Or.inl ?_
        refine And.intro ?_ hInA
        refine Or.inl ?_
        exact ⟨hInC, hInA⟩ 

    case inr.inr =>
      rw [<- hWdefx]
      refine Or.inr ?_
      refine And.intro hInA ?_
      simp only [not_or, not_and, Decidable.not_not]
      rw [<- iff_def]
      rw [propext (iff_false_left hnInC)]
      exact hnInB

    case inr.inl =>
      rw [<- hWdefx]
      refine Or.inl ?_
      refine And.intro ?_ hnInA
      refine Or.inr ?_
      exact ⟨hInB, hnInC⟩ 


  case mpr =>
    intro hInW
    rcases hWdefx.mpr hInW with ⟨⟨hInC, hnInB⟩ | ⟨hInB, hnInC⟩, hnInA⟩ | ⟨hInA, hnSCB⟩
    case inl.inl =>
      rw [<- hYdefx]
      refine Or.inl ?_
      refine ⟨hInC, Or.inl hnInB, Or.inl hnInA⟩ 
    
    case inl.inr =>
      rw [<- hYdefx]
      refine Or.inr ?_
      exact ⟨Or.inl ⟨hInB, hnInA⟩ ,hnInC⟩ 

    case inr =>
      rw [<- hYdefx]
      simp only [not_or, not_and, Decidable.not_not] at hnSCB
      rw [<- iff_def] at hnSCB
      rw [hnSCB]
      by_cases hInB: x ∈ B
      case pos =>
        refine Or.inl ?_
        exact ⟨hInB, Or.inr hInA, Or.inr hInB⟩

      case neg =>
        refine Or.inr ?_
        exact ⟨Or.inr ⟨hInA, hInB⟩ , hInB⟩ 

-- (A + B) ∩ C = A ∩ C + B ∩ C
theorem symmetric_difference_inter_dist (A B C : NFObject) (hA : IsSet A) (hB : IsSet B) (hC : IsSet C) (AB : NFObject) (hAB : IsSet AB) (hABdef : SymmetricDifference A B hA hB AB) (ABC: NFObject) (hABC: IsSet ABC) (hABCdef: Intersection AB C hAB hC ABC) (AC: NFObject) (hAC: IsSet AC) (hACdef: Intersection A C hA hC AC) (BC: NFObject) (hBC: IsSet BC) (hBCdef: Intersection B C hB hC BC) (ACBC: NFObject) (hACBC: IsSet ACBC) (hACBCdef: SymmetricDifference AC BC hAC hBC ACBC): ABC = ACBC := by
  apply extensionality ABC ACBC hABC hACBC
  intro x

  rw [SymmetricDifference] at hACBCdef
  rw [Intersection] at hABCdef

  rw [SymmetricDifference] at hABdef
  rw [Intersection] at hACdef
  rw [Intersection] at hBCdef

  have hABCdefx := hABCdef x
  have hACBCdefx := hACBCdef x
  have hABdefx := hABdef x
  have hACdefx := hACdef x
  have hBCdefx := hBCdef x

  simp only at hACBCdefx
  simp only at hABdefx

  rw [<- hBCdefx] at hACBCdefx
  rw [<- hACdefx] at hACBCdefx
  
  rw [<- hABdefx] at hABCdefx
  -- rw [or_and_right] at hABCdefx
    
  

  rw [<- hACBCdefx]
  rw [<- hABCdefx]
  

  constructor
  case mp =>
    intro ⟨hBASD, hinC⟩ 
    rcases hBASD with ⟨hinB, hninA⟩  | ⟨hinA, hninB⟩
    case inl =>
      refine Or.inl ?_
      rw [not_and_iff_not_or_not]
      exact ⟨⟨hinB, hinC⟩, Or.inl hninA⟩


    case inr =>
      refine Or.inr ?_
      rw [not_and_iff_not_or_not]
      exact ⟨⟨hinA, hinC⟩,  Or.inl hninB⟩ 

  
  case mpr =>
    intro y 
    rcases y with ⟨⟨hinB, hinC⟩, hninAninC⟩  | ⟨⟨hinA, hinC⟩, hninBninC⟩
    case inl =>
      refine ⟨?_, hinC⟩ 
      rw [not_and'] at hninAninC
      have hinA := hninAninC hinC
      exact Or.inl ⟨hinB, hinA⟩ 

    case inr =>
      refine ⟨?_, hinC⟩

      rw [not_and'] at hninBninC
      have hninB := hninBninC hinC

      exact Or.inr ⟨hinA, hninB⟩ 
  
-- Chapter 4.
axiom singletons (x: NFObject): ∃ (Sx: NFObject), IsSet Sx ∧ ∀ (y: NFObject), y ∈ Sx <-> y = x

noncomputable def ι (x : NFObject) : NFObject := 
  Classical.choose (singletons x)

theorem ι_spec (x: NFObject) : IsSet (ι x) ∧ ∀ y, y ∈ (ι x) <-> y = x := Classical.choose_spec (singletons x)

