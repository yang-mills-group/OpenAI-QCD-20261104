import YM.Tawny.Scurf
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace TableT
open Rays Carnal Perla Zinc Perla.Fore
local notation "VX"=> RawVec 10
local notation "U"=> (0:Multi 10)
local notation "J"=> leadR
local notation "L"=> ηR
local notation "I"=> (0:Axis)
local notation "B"=> (1:Axis)
variable (v: Values 7)(c: Fin 3→ℂ)(i j: Axis)(p q: Multi 10)(x:Fin 7→ℂ)(X:Labels.Jet su)
set_option quotPrecheck false
local notation "g" p:arg q:arg=> prism0 a p q ((vectorZ a x).val I).val
lemma probe_zero(a:Axis)(z:ℂ)(h:z • gamma a=0): z=0:=by
     have ht:gamma a≠0:=by intro he; have hx:= Lat.gamma_sq a; rw[he,zero_mul] at hx; exact zero_ne_one hx
     exact (smul_eq_zero.mp h).resolve_right ht
lemma probe_one(z:ℂ)(h:z • (1:Spike)=0) : z=0 := (smul_eq_zero.mp h).resolve_right one_ne_zero
lemma turns (h:∀ p q:Multi 10,g p q=0) : x 0=0 ∧ x 1=0∧x 2=0∧x 3=0∧x 4=0∧x 5=0:=by
    have hu:= (row1 a x).symm.trans (h U (J B)); have he:x 1 • (gamma I)=0:=by
         rw [← mul_one (x 1 • gamma I),←Lat.gamma_sq B,← mul_assoc,Matrix.smul_mul,hu,zero_mul]
    have h1:=probe_zero I (x 1) he; have h0: x 0=0:= by apply probe_one; have he:= (row0 a x).symm.trans (h U (J I)); rw [h1,zero_smul,add_zero] at he; exact he
    have h3:=probe_zero I (x 3) ((row3 a x).symm.trans (h U (L B B))); have h4:=probe_zero B (x 4) ((row4 a x).symm.trans (h U (L I B))); refine ⟨h0,h1,probe_zero I _ ?_,h3,h4, probe_zero B _ ((row5 a x).symm.trans (h _ _))⟩
    have ht:= (row2 a x).symm.trans (h U (L I I)); simp only [h4,h3,zero_smul,add_zero] at ht; exact ht
lemma seaF : pages X ( (ocean c).val i) = c 0* pages X (leapV.val i) + c 1* pages X (lunar.val i)+c 2* pages X (eulerV.val i):=by simp [ocean]
lemma sea_zero (hz:∀ i X,pages X ((ocean c).val i)=0): c=0:=by
     obtain ⟨p,h,hP⟩:=plot_Y _ ruby_pick.choose_spec; have hp:=hz 0 (lexY p); rw[seaF,h,hP,E_full,mul_zero,mul_zero,zero_add,add_zero] at hp; have ht:c 1=0:=(mul_eq_zero.mp hp).resolve_right (by norm_num)
     obtain ⟨q,h1,h2⟩:= plot_X _ ruby_pick.choose_spec; have hQ:= hz 0 (lexY q); rw [seaF,h1,mul_one,ht,E_full,zero_mul,mul_zero,add_zero,add_zero] at hQ
     obtain ⟨u,Jx,hx⟩:= E_alive; have he:= hz u Jx; rw [seaF,ht,hQ,zero_mul,zero_mul,zero_add,zero_add] at he; funext i; fin_cases i; exact hQ; exact ht; exact (mul_eq_zero.mp he).resolve_right hx
open LinearMap
lemma spin_read (h:∀ i:Axis,∀ p q: Multi 10, prism0 a p q ((plaza (v,c)).val i).val=0) :v a 0=0∧ v a 1=0 ∧ v a 2=0 ∧ v a 3=0∧v a 4=0 ∧ v a 5=0:= turns a _ (fun p q=>(coast a v c I p q).symm.trans (h I p q))
lemma sunny: Injective plaza:=by
    refine (LinearMap.ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=Values 7 × (Fin 3→ℂ)) (M₂:=VX) (f:=plaza)).mp (LinearMap.ker_eq_bot'.mpr ?_); rintro ⟨v,c⟩ h; have hs(i): ((plaza (v,c)).val i).val=0:= congr_arg (fun M:VX=> (M.val i).val) h; have hv(a:Flavor 6)(p q:Multi 10)(i:Axis):= congr_arg (prism0 a p q) (hs i)
    have he:v=0:=by
         funext a p; obtain ⟨h0,h1,h2,h3,h4,h5⟩:= spin_read a v c (fun i p q=> (hv ..).trans (map_zero _)); fin_cases p; exact h0; exact h1; exact h2; exact h3; exact h4; exact h5
         apply probe_zero B; have ht:= coastX a v c I B (by decide); rw [hs,map_zero] at ht; exact ht.symm
    have hp: ((plaza (v,c)))=ocean c:=by
          rw[he]; change vectorY 0+_= _; have hz:vectorY 0=0:=by simp [vectorY,vectorZ]
          rw [hz,zero_add]
    have hQ:ocean c=0:=hp.symm.trans h; exact Prod.ext he (sea_zero _ (fun i X=> by rw[hQ]; exact map_zero _))
lemma certified : Bijective plaza:=by
    have he:= finrank_range_of_inj sunny; have hb: Module.finrank ℂ (Values 7) =42:=by unfold Values; rw [Module.finrank_pi_fintype]; simp only [Module.finrank_fin_fun,Flavor,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; decide
    have hT:Module.finrank ℂ plaza.range=45:=by rw[he,Module.finrank_prod,hb,Module.finrank_fin_fun]
    haveI:FiniteDimensional ℂ ↥VX:=FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=Axis→Label 10) (RawVec 10)
    refine ⟨sunny,range_eq_top.mp (Submodule.eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_))⟩; rw[hT]; exact highR
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.certified
