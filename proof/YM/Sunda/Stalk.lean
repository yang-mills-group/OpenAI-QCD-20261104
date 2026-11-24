import YM.Sunda.Hula
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
local notation "E"=>End ℂ (Pol 9)
local notation "T"=>SpinMode 9
local notation "X"=> Pairs T
local notation "U"=> (0:Multi 9)
open Pearl (lit)
variable(a:Flavor 6)
noncomputable abbrev mnA : ↥(unitary ℂ):=⟨-1,by constructor <;> simp⟩
noncomputable def clipF(a:Flavor 6):FlavorTorus:=fun i=> if a=i then mnA else 1
noncomputable abbrev flipU (a:Flavor 6):End ℂ (Pol 9):= flavorAct (clipF a)-1
noncomputable abbrev subU(a:Flavor 6):End ℂ (Pol 9):= flavorAct (ic a) - (-Complex.I) • 1
noncomputable def oily:E:= subU 0* (subU 1* subU 2)* (flipU 0*(flipU 1*flipU 2))
abbrev favor (x:X):Flavor 6:=(Sum.elim id id x).2
lemma tagA (u:FlavorTorus)(S:Finset X): pigment 9 u (mono S)=(∏ i∈S,charon u i) • mono S:=by
      classical
      induction S using Finset.induction_on with
      | empty=> simp
      | @insert i S hi ih=>
        have ht:= mono_mul_sign (A:=X) {i} S (by simp[hi]); rw[mono_single,disjUnion_eq_union,singleton_union] at ht
        have hp:pigment 9 u (atom i* mono S)=(∏ j∈ insert i S,charon u j) • (atom i* mono S):=by rw [map_mul,show pigment 9 u (atom i)=_ from buck u i,ih,prod_insert hi,mul_smul,smul_mul_assoc,mul_smul_comm]
        rcases ht with ht|ht; rwa [ht] at hp; rwa[ht,map_neg,smul_neg,neg_inj] at hp
abbrev bill (u:FlavorTorus)(p:PowerPair 9):ℂ:= ∏ i∈p.2,charon u i
lemma pullG (u:FlavorTorus)(p:PowerPair 9): flavorAct u (gen p)= bill u p • gen p:=by unfold gen; rw[pig_weight,tagA,tmul_smul]
variable (p:PowerPair 9)
abbrev cold (p:PowerPair 9)(a:Flavor 6):ℂ:= bill (clipF a) p-1
abbrev flu (p:PowerPair 9)(a:Flavor 6):ℂ:= bill (ic a) p- (-Complex.I)
lemma scoop : flipU a (gen p)= cold p a • gen p∧ subU a (gen p)= flu p a • gen p:=by
        constructor; · change flavorAct _ _-gen p=_; rw[pullG,cold]; exact (one_smul ℂ (gen p) ▸ (_root_.sub_smul (bill (clipF a) p) (1:ℂ) (gen p))).symm
        change flavorAct _ _-(-Complex.I) • (gen p)= _; rw[pullG,flu]; exact (_root_.sub_smul (bill (ic a) p) (-Complex.I) (gen p)).symm
lemma paintG : oily (gen p)=(cold p 2 * cold p 1 * cold p 0 * flu p 2 * flu p 1 * flu p 0) • gen p:=by
      unfold oily; simp only [End.mul_apply]; rw[(scoop 2 p).1,map_smul,(scoop 1 p).1,smul_smul,map_smul, (scoop 0 p).1, smul_smul,map_smul,(scoop 2 p).2,smul_smul,map_smul,(scoop 1 p).2,smul_smul,map_smul,(scoop 0 p).2,smul_smul]
lemma scoreI (h:cold p a ≠ 0):∃ i∈p.2, favor i=a:=by
       by_contra! he; apply h; apply sub_eq_zero.mpr; apply prod_eq_one; intro i hi; specialize he i hi; rcases i with i|i <;> change i.2 ≠ a at he <;> simp [charon,clipF,he.symm]
lemma oneF (i:X)(h:favor i≠a) : charon (ic a) i=1:=by rcases i with i|i<;>change i.2≠a at h <;>simp[charon,ic,h]
lemma scout (i j k:X)(hp:flu p a ≠0)(hi:p.2={i,j,k})(h:favor i=a)(hu:favor j≠a)(hz:favor k≠a): ∃ v:T,i= .inl v:=by
      rcases i with i|i; exact ⟨_,rfl⟩
      exfalso; apply hp; apply sub_eq_zero.mpr; unfold bill; rw [Finset.prod_eq_single_of_mem (.inr i) (by simp[hi])]; · change i.2=a at h; simp [charon,ic,h]
      · intro l hv hh; rw [hi] at hv; rcases mem_insert.mp hv with he|he; · exact False.elim (hh he)
        rcases mem_insert.mp he with rfl|hl; exact oneF _ _ hu; rw [mem_singleton.mp hl]; exact oneF _ _ hz
abbrev labelE (a:Flavor 6)(i:Pinor)(v:Hue):X:=.inl ((0,i,v),a)
lemma staunch(hw:weight p ≤ 9)(h:cold p 0≠0)(h1:cold p 1≠0)(h2:cold p 2≠0)(ht:flu p 0≠0)(hl:flu p 1≠0)(hm:flu p 2≠0):∃ (i j k:Pinor)(a b c: Hue),p=(0,{labelE 0 i a, labelE 1 j b,labelE 2 k c}):=by
     obtain ⟨v,hv,e⟩:= scoreI _ p h; obtain ⟨s,hs,f⟩:=scoreI _ p h1; obtain ⟨t,hh,g⟩:=scoreI _ p h2
     have hx:v≠s∧v≠t∧s≠t:=by constructor <;> (first| exact fun r=> (_root_.zero_ne_one (α:=Fin 6)) (e.symm.trans ((congr_arg _ r).trans f)) | exact ⟨fun r=> (show (0:Fin 6) ≠ 2 by decide) (e.symm.trans ((congr_arg _ r).trans g)), fun r=> (show (1:Fin 6)≠2 by decide) (f.symm.trans ((congr_arg _ r).trans g))⟩)
     have hy:p.2={v,s,t}:=by
           unfold UV.weight at hw; have he : #p.2*3 ≤ ∑ i∈p.2,letterWeight i:=by rw [show #p.2*3=∑ i∈p.2,(3:ℕ) from by simp]; exact sum_le_sum fun i _=> Nat.le_add_right ..
           symm; apply Finset.eq_of_subset_of_card_le; · intro i; rintro h; rcases mem_insert.mp h with rfl|h; exact hv; rcases mem_insert.mp h with rfl|h; exact hs; rw [mem_singleton.mp h]; exact hh
           have hp: #{v,s,t}=3:=by simp [hx.1,hx.2.1,hx.2.2]  -- nesting!
           omega
     obtain ⟨u,rfl⟩:= scout 0 p v s t ht hy e (by rw [f]; decide) (by rw [g]; decide)
     obtain ⟨u',rfl⟩:= scout 1 p s (.inl u) t hl (hy.trans (insert_comm ..)) f (by rw[e]; decide) (by rw[g]; decide)
     obtain ⟨u'',rfl⟩:=scout 2 p t (.inl u) (.inl u') hm (by rw [hy,show ({_,t}:Finset X)={t,.inl u'} from pair_comm (.inl u') t,insert_comm]) g (by rw[e]; decide) (by rw[f]; decide)
     unfold UV.weight at hw; rw [hy,sum_insert (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨hx.1,hx.2.1⟩),sum_pair hx.2.2] at hw
     change 2* Labels.height p.1+(spinWeight u.1.1+(spinWeight u'.1.1+spinWeight u''.1.1)) ≤9 at hw
     have hO:p.1=0:=by
         unfold UV.spinWeight at hw; by_contra hn; obtain ⟨j,a,h⟩:=splits_one _ hn; have ht : Labels.height p.1=Labels.height a+(j.1+2):=by rw[h,Labels.height,map_add,Finsupp.weight_single,one_smul]; rfl
         omega
     rcases u with ⟨⟨l,i,a⟩,w⟩; rcases u' with ⟨⟨l',j,b⟩,w'⟩; rcases u'' with ⟨⟨l'',k,c⟩,w''⟩; change w=0 at e; change w'=1 at f; change w''=2 at g; refine ⟨i,j,k,a,b,c,Prod.ext hO ?_⟩; rw [hy]; dsimp only at hw; have h₁:=low l; have h₂:=low l'; have h₃:=low l''; rw [e,f,g,ground l (by omega),ground l' (by omega),ground l'' (by omega)]
set_option quotPrecheck false
local notation "Z"=>Submodule.span ℂ (Set.range fun i:Pinor × Pinor ×Pinor×Pearl.Triple=>(1:GPol)⊗ₜ[ℂ]Pearl.rowW i.1 i.2.1 i.2.2.1 i.2.2.2)
noncomputable def Peak: Submodule ℂ (Pol 9):= Z
lemma staple (hw:weight p≤9) : oily (gen p) ∈ Peak:=by
       rw [paintG]; by_cases h:cold p 2 * cold p 1*cold p 0 * flu p 2*flu p 1*flu p 0=0; · rw [h,zero_smul]; exact Peak.zero_mem
       simp only [mul_ne_zero_iff] at h; obtain ⟨⟨⟨⟨⟨h2,h1⟩,h0⟩,v2⟩,v1⟩,v0⟩:= h
       refine Peak.smul_mem _ ?_; obtain ⟨i,j,k,a,b,c,rfl⟩:= staunch p hw h0 h1 h2 v0 v1 v2; unfold UV.gen; let A:=labelE 0 i a; let B:= labelE 1 j b; let C:=labelE 2 k c
       have h: (1:GPol)⊗ₜ[ℂ] (atom A*(atom B*atom C)) ∈ Peak:=by rw [← mul_assoc]; exact Submodule.subset_span ⟨(i,j,k,a,b,c),rfl⟩
       have hu:= sign_product [A,B,C] (by simp [A,B,C,labelE])
       change (1:GPol)⊗ₜ[ℂ]mono {A,B,C}∈ _; simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,List.toFinset_cons,List.toFinset_nil,insert_empty_eq] at hu; rcases hu with he|he; · rw [← he]; exact h
       rw [he,tmul_neg] at h; exact neg_mem_iff.mp h
lemma stockL (x:Label 9): oily x.val∈ Peak:=by
      have hm : UV.cap 9≤ Peak.comap oily:= Submodule.span_le.mpr (fun _ ⟨s,h,r⟩=> r ▸ staple _ h); exact hm ((label_law _).mp x.property).1
end YM.Sunda
#print axioms YM.Sunda.stockL
