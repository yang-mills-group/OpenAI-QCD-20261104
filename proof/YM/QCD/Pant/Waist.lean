import YM.QCD.Pant.Button
/-! # Transport taxes on shell words. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
local notation "V"=>EvenA c N
variable {ι κ:Type}
def pack (p: Equiv.Perm κ): Equiv.Perm (Clusters κ):={ toFun:=fun z=>⟨z.1,p ∘ z.2⟩, invFun:=fun z=>⟨z.1,p.symm ∘ z.2⟩,left_inv z:=by simp [← Function.comp_assoc],right_inv z:=by simp [← Function.comp_assoc] }
def Got (s:ι→Support c)(p:Equiv.Perm ι)(x:Equiv.Perm (Site c)):Prop:=∀ i, s (p i)=(s i).image x
variable {s q:ι→ Support c} {r:κ→Support c}{p: Equiv.Perm ι}{p':Equiv.Perm κ}{x:Equiv.Perm (Site c)}
lemma blocksP (h: Got s p x)(i j:ι): blocked s (p i) (p j)↔ blocked s i j:=by
   apply or_congr (p.apply_eq_iff_eq); unfold Ac.meets; rw [h,h]; constructor
   · rintro ⟨a,hi,hj⟩; obtain ⟨a,rfl⟩:=x.surjective a; exact ⟨a,by simpa using hi,by simpa using hj⟩
   rintro ⟨a,h,hj⟩; exact ⟨x a,by simpa using h,by simpa using hj⟩
lemma assigns (h: Got s p x)(i:Clusters ι): seatP s (pack p i)=(seatP s i).image x :=by
    unfold seatP unionOf; rw [biUnion_image]; exact Finset.biUnion_congr rfl fun i _=> h _
variable {K:EvenA c N →+*EvenA c N}{f1 g1:ι→ EvenA c N}{f2 g2:κ→ EvenA c N}
lemma spry (h: Got s p x)(ht: Continuous K)(he:∀ i, K (f1 i)=g1 (p i)) (z:Clusters ι): K (termP (blocked s) f1 z)= termP (blocked s) g1 (pack p z):=by
    have hh: pot (blocked s) (p ∘ z.2)= pot (blocked s) z.2:=by ext; simp only [pot, mem_filter,comp_apply,blocksP h] -- pipe form invalid?
    unfold termP; rw [eSM K ht,eSM K ht]; unfold coefficient; apply congr_arg (fun a:EvenA c N => ((↑(z.fst+1).factorial:ℝ)⁻¹) • a); apply congr_arg₂ (· • ·) (congr_arg Graph.mass hh.symm) ?_; rw [map_prod]; simp_rw [he]; rfl
lemma polite (h:Got r p' x) (ht:Continuous K)(he:∀ i,K (f2 i)=g2 (p' i))(hp:Summable (termP (blocked r) f2)) (W: Support c): K (portion r f2 W)=portion r g2 (W.image x):=by
   let M:= K.toAddMonoidHom.toRealLinearMap ht
   let Z (i:Clusters κ):= if seatP r i=W then termP (blocked r) f2 i else 0; have hZ: Summable Z:= somG hp.norm W
   unfold portion; change M (∑' i,Z i)=_; rw [M.map_tsum hZ,← Equiv.tsum_eq (pack p') (fun i => if unionOf r i.2=W.image x then _ else 0)] -- syntax
   refine tsum_congr fun i=>?_ ; unfold Z; have hu:unionOf r (pack p' i).2=W.image x↔ seatP r i=W:=by change seatP r _=_↔_; rw [assigns h i]; exact (image_injective x.injective).eq_iff
   split_ifs <;> first| exact spry h ht he _ | exact map_zero _| tauto
abbrev horse (p:Equiv.Perm ι)(x: Equiv.Perm (Site c)):= Equiv.sumCongr p x.finsetCongr
lemma posterG {u:Finset (ι⊕Support c)}: (((horse p x).finsetCongr u).toLeft=p.finsetCongr u.toLeft) ∧ ((horse p x).finsetCongr u).toRight=(x.finsetCongr).finsetCongr u.toRight:=by
    constructor
    · ext i; obtain ⟨i,rfl⟩:=p.surjective i; simp [horse]
    ext i; obtain ⟨i,rfl⟩:=x.finsetCongr.surjective i; simp [horse]
lemma postP (h:Got s p x): Got (GasP.facesP s) (horse p x) x:=by
    rintro (i|i); · exact h _
    exact Finset.map_eq_image ..
lemma womb (h:Got s p x)(i:Finset ι): (p.finsetCongr i).biUnion s=(i.biUnion s).image x:= PhysicalNext.Repeat.Turn.gains p x (fun z=> (display x _ _).1 (h z)) ((PhysicalNext.Repeat.Turn.given _ _ _).1 rfl)
lemma sepR (h: Got s p x)(i : Finset ι): separated (blocked s) i↔ separated (blocked s) (p.finsetCongr i):=by
   have hf:= (given p _ _).1 (show p.finsetCongr i=_ from rfl)
   constructor
   · intro h1 z hz u hu h2 h3; obtain ⟨z,rfl⟩:=p.surjective z; obtain ⟨u,rfl⟩:=p.surjective u
     exact h1 z ((hf z).2 hz) u ((hf u).2 hu) (fun he=>h2 (congr_arg _ he)) ((blocksP h z u).1 h3)
   intro hp j hj k hk h2 h3; exact hp _ ((hf _).1 hj) _ ((hf _).1 hk) (p.injective.ne h2) ((blocksP h _ _).2 h3)
lemma friend (h:Got s p x)(z: Finset (ι⊕Support c)):
    wagon s z ↔ wagon s ((horse p x).finsetCongr z):=by
   let T:=horse p x; let Z:=T.finsetCongr z; have hV:= postP h; unfold wagon; rw [posterG.1, posterG.2]
   refine and_congr ?_ (and_congr (seam T x (fun i=> (display x _ _).1 (hV i)) ((given _ _ _).1 rfl)) (and_congr (sepR h z.toLeft) ?_)); · simp
   unfold pongs; conv_rhs=> rw [← x.finsetCongr.forall_congr_right]
   rw [womb h z.toLeft]; apply forall_congr'; intro i; apply imp_congr
   · exact (given x.finsetCongr z.toRight _).1 rfl _
   apply not_congr; rw [show x.finsetCongr i=i.image x from map_eq_image ..]; exact (Finset.disjoint_image x.injective).symm
lemma shaftsG (h:Got q p x)(z:Finset (ι⊕ Support c)): sweep q ((horse p x).finsetCongr z)=(sweep q z).image x:=by unfold sweep; rw [posterG.1]; exact womb h _
lemma railL (h:Got s p x)(hr:Got r p' x)(hd:Got q p x)(ht:Continuous K)(hf:∀ i,K (f1 i)=g1 (p i))(hg:∀ i,K (f2 i)=g2 (p' i))(hp:Summable (termP (blocked r) f2))(z:Support c)(u:Finset (ι⊕Support c)): K (motto s q r z f1 f2 u)=motto s q r (z.image x) g1 g2 ((horse p x).finsetCongr u):=by
    let Z:= horse p x; let U:=Z.finsetCongr u; have he:wound s U=(wound s u).image x:=womb (postP h) u -- name
    have hx:(z.image x)∩wound s U=sweep q U↔ z∩wound s u=sweep q u:=by
       rw [he, show sweep q U=_ from shaftsG hd _,← Finset.image_inter _ _ x.injective]; exact (image_injective x.injective).eq_iff
    unfold motto; split
    next h' =>
       rw [if_pos ⟨(friend h u).1 h'.1,hx.mpr h'.2⟩,map_prod]; symm
       erw [Finset.prod_map]; refine prod_congr rfl fun i _=>?_ ; rcases i with i|i
       · exact (hf i).symm
       change dropsP r g2 (x.finsetCongr i)= K (NormedSpace.exp _-1)
       rw [map_sub,map_one,map_exp K ht,map_neg,polite hr ht hg hp, show x.finsetCongr i=i.image x from map_eq_image ..]
       rfl
    next h' => rw [if_neg (fun H=>h' ⟨(friend h u).2 H.1,hx.mp H.2⟩),map_zero]
end YM.QCD.Patron
