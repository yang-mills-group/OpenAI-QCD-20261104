import YM.Tawny.Anthem
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
local notation "U"=> (0:Multi 8)
variable (e:ℂ) (x:RawTensor e 8)
set_option quotPrecheck false
local notation "X" i:arg j:arg=> (x.val (i,j)).val
local notation "D" p q => prism0 a p q
local notation "g" p:arg q:arg i:arg j:arg=>prism0 a p q (x.val (i,j)).val
local notation "L" i:arg=> UV.first i
variable (p q:Multi 8)(i j k l:Axis)
open StressFlux.Offer
-- linear probes
noncomputable def ex0 (l:List Axis): RawTensor e 8 →ₗ[ℂ]ℂ:= feeP l ∘ₗ prism0 a p q ∘ₗ (UV.labels _).subtype ∘ₗ LinearMap.proj (i,j) ∘ₗ (RawTensor e 8).subtype
noncomputable def punch(e:ℂ) : RawTensor e 8 →ₗ[ℂ]ℂ:= ex0 a e U (L 0) 0 1 [0,1,0]
noncomputable def symP : RawTensor 1 8 →ₗ[ℂ](Fin 4→ℂ):= LinearMap.pi (![ex0 a 1 U U 0 0 [0,0],ex0 a 1 U (L 0) 0 0 [0,0,0],ex0 a 1 U (L 1) 0 0 [0,0,1],punch a 1])
noncomputable def altP : RawTensor (-1) 8 →ₗ[ℂ](Fin 2→ℂ):= LinearMap.pi (![punch a (-1),ex0 a (-1) U (L 2) 0 1 [0,1,2]])
lemma altL(h:punch a e x=0)(hp:i≠j) : g U (L i) i j=0∧g U (L j) i j=0:=by
     have ht:g U (L 0) 0 1=0:=germ _ _ h (bidP a e x 0 1 0)
     have he(i j:Axis)(hi:i≠j) : g U (L i) i j=0:=by
           obtain ⟨P,h,h'⟩:=StressFlux.extend_two i j hi; obtain ⟨w,hw⟩:=EuPin.choice (flag P); have hz:= paradeL a e x 0 1 0 P w hw; rw [h,h',ht, conjug, mul_zero, zero_mul] at hz; exact hz
     refine ⟨he i j hp,?_⟩; rw [S_seal a e x _ _ j i,he j i hp.symm,smul_zero]
lemma tguard {x:RawTensor 1 8}(h:symP a x=0): (prism0 a U U (x.val (i,j)).val=0 ∧prism0 a U (L k) (x.val (i,j)).val=0):=by
     have hz: punch a 1 x=0:= congr_fun h 3; let X':= fun (p q: Multi 8) i j=> prism0 a p q (x.val (i,j)).val; change X' U U i j=0 ∧ X' U _ i j=0
     by_cases hp:i=j
     · subst j; have he:X' U U 0 0=0:= germ _ _ (congr_fun h 0) (bid0 a 1 x 0 0); let P:=Equiv.swap 0 i; obtain ⟨w,hw⟩:=EuPin.choice (flag P); have hP:P 0=i:=Equiv.swap_apply_left ..
       have ht:(w:EuPin)→(conjug w (0:Spike)=0):=fun w=>by rw [conjug,mul_zero,zero_mul]
       constructor
       · rw [← hP]; exact Eq.trans (parade0 a 1 x 0 0 P w hw) (by change conjug w (X' U U 0 0)=0; rw[he,ht])
       by_cases hu:k=i
       · subst k; have he':X' U (L 0) 0 0=0:=germ _ _ (congr_fun h 1) (bidP a 1 x 0 0 0); rw [← hP]; exact Eq.trans (paradeL a 1 x 0 0 0 P w hw) (by change conjug w (X' U (L 0) 0 0)=0; rw [he',ht])
       obtain ⟨Q,hQ,hU⟩:= StressFlux.extend_two i k (Ne.symm hu); obtain ⟨r,hr⟩:=EuPin.choice (flag Q); have hb:X' U (L 1) 0 0 =0:= germ _ _ (congr_fun h 2) (bidP a 1 x 0 0 1); rw [← hQ,← hU]; exact Eq.trans (paradeL a 1 x 0 0 1 Q r hr) (by change conjug r (X' U (L 1) 0 0)=0; rw [hb,ht])
     refine ⟨unroof a _ x i j hp,?_⟩; rcases eq_or_ne k i with rfl|ht; · exact (altL _ 1 _ _ _ hz hp).1
     rcases eq_or_ne k j with rfl|hz'; · exact (altL _ 1 _ _ _ hz hp).2
     exact off_ax a _ _ _ x hp ht hz'
lemma tguardA{x:RawTensor (-1) 8}(h:altP a x=0): (prism0 a U U (x.val (i,j)).val=0 ∧prism0 a U (L k) (x.val (i,j)).val=0):=by
     have hz:punch a (-1) x=0:=congr_fun h 0; by_cases hp:i=j
     · subst j; have hv(p q:Multi 8):prism0 a p q (x.val (i,i)).val=0:= negS _ (by rw [← neg_one_smul ℂ (_:Spike)]; exact (S_seal a (-1) x p q i i).symm)
       exact ⟨hv U U,hv U (L k)⟩
     refine ⟨unroof a _ x i j hp,?_⟩; rcases eq_or_ne k i with rfl|h1; · exact (altL _ (-1) _ _ _ hz hp).1
     rcases eq_or_ne k j with rfl|h2; · exact (altL _ (-1) _ _ _ hz hp).2
     obtain ⟨P,hP,hU,hT⟩:=StressFlux.extend_three i j k hp h1.symm h2.symm; obtain ⟨w,hw⟩:=EuPin.choice (flag P); have hb:prism0 a U (L 2) (x.val (0,1)).val=0:=germ _ _ (congr_fun h 1) (bidP a _ x 0 1 2); rw [← hP,← hU,← hT]; rw [paradeL a _ x _ _ _ P w hw,hb,conjug, mul_zero,zero_mul]
private lemma both(h:spinWeight p+spinWeight q≤8): p=U∧ q=U ∨ (∃ i:Axis,p=U∧ q= L i) ∨ (∃ i:Axis,p=L i∧q=U):=by
     have hp:=Oriole.low p; have hq:=Oriole.low q; by_cases he:p=U
     · by_cases ht:q=U; · exact Or.inl ⟨he,ht⟩
       obtain ⟨i,hi⟩:=Oriole.halo q (by omega) ht; exact Or.inr (Or.inl ⟨i,he,hi.symm⟩)
     obtain ⟨i,hi⟩:=Oriole.halo p (by omega) he; rw [← hi, juicy] at h; exact Or.inr (Or.inr ⟨i,hi.symm,Oriole.ground q (by omega)⟩)
open LinearMap
local notation "Q"=> valet acts marks Prod.swap e (d:=8) (by decide)
lemma A_count (h:∀ a:Flavor 6,∀ i j k:Axis,prism0 a U U (x.val (i,j)).val=0∧prism0 a U (L k) (x.val (i,j)).val=0)(ht:Q x=0) : x=0:=by
     apply Subtype.ext; funext ⟨i,j⟩; apply denovo _ ((show Meaning _ _ _ _ 8 _ from x.property).light (i,j)) (by decide) (congr_arg Subtype.val (congr_fun (congr_arg Subtype.val ht) (i,j)))
     · intro a p q hp; rcases both p q hp with ⟨rfl,rfl⟩|⟨k,rfl,rfl⟩|⟨k,rfl,rfl⟩; · exact (h a i j 0).1
       exact (h a i j k).2
       rw [trans1 a e x U (L k),(h a i j k).2,truck_blank]
     intro a p q hp; have ht:=Oriole.low p; have hg:=Oriole.low q; omega
lemma A_drop (x:RawTensor (-1) 8) : valet acts marks Prod.swap (-1) (d:=8) (by decide) x=0:=by
     let U':TwoG su:= valet acts marks Prod.swap (-1) (d:=8) (by decide) x; change U' = 0; apply Subtype.ext; funext ⟨i,j⟩; apply Subtype.ext
     have h:= congr_arg Subtype.val (anyC QCD.simple U' i j); change fog (x.val (i,j)).val=fog (x.val (j,i)).val at h; rw [show x.val (j,i)= (-1:ℂ) • x.val (i,j) from (show Meaning _ _ _ _ 8 _ from x.property).sym (i,j),Submodule.coe_smul,map_smul,neg_one_smul] at h; have hu : (2:ℂ) • fog (x.val (i,j)).val=0:=by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr h
     exact (smul_eq_zero.mp hu).resolve_left (by norm_num)
noncomputable def symPane :RawTensor 1 8 →ₗ[ℂ] (TwoG su × (Flavor 6 → Fin 4→ℂ)):= (valet acts marks Prod.swap 1 (d:=8) (by decide)).prod (LinearMap.pi fun a=> symP a)
noncomputable def altPane : RawTensor (-1) 8→ₗ[ℂ] (Flavor 6 → Fin 2→ℂ):= LinearMap.pi fun a=>altP a
local instance (e:ℂ):AddCommGroup (RawTensor e 8):=Submodule.addCommGroup (R:=ℂ) (M:=Axis×Axis→Label 8) (p:=RawTensor e 8)
local instance: AddCommGroup (TwoG su):=Submodule.addCommGroup _
lemma full : Injective symPane:= by refine (LinearMap.ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=RawTensor 1 8) (M₂:=TwoG su × (Flavor 6→ Fin 4→ℂ)) (f:=symPane)).mp (LinearMap.ker_eq_bot'.mpr ?_); intro x h; exact A_count 1 x (fun a i j k=> tguard a i j k (congr_fun (congr_arg Prod.snd h) a)) (congr_arg Prod.fst h) -- instance
lemma alternate : Injective altPane:=by refine (LinearMap.ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=RawTensor (-1) 8) (M₂:=Flavor 6→ Fin 2 →ℂ) (f:=altPane)).mp (LinearMap.ker_eq_bot'.mpr ?_); intro x h; exact A_count (-1) x (fun a i j k=> tguardA a i j k (congr_fun h a)) (A_drop x)
lemma sky_scope : Module.finrank ℂ (RawTensor 1 8)≤28 ∧ Module.finrank ℂ (RawTensor (-1) 8)≤12:=by
     haveI:Module.Free ℂ (TwoG su):= Module.Free.of_divisionRing ℂ (TwoG su)
     have he:= finrank_le_finrank_of_injective full; have hp:=finrank_le_finrank_of_injective alternate; rw [Module.finrank_prod,Module.finrank_pi_fintype] at he; rw [Module.finrank_pi_fintype] at hp; simp only [Module.finrank_fin_fun,sum_const, card_univ, Fintype.card_fin,nsmul_eq_mul] at he hp
     have ht:= (rankRG QCD.simple).1; unfold Flavor at *; omega
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.sky_scope
