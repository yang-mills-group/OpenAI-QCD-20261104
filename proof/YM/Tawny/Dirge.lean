import YM.Tawny.River
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Drill
open TableT Carnal Rays Perla Zinc Perla.Fore Dream Dream.Clove
open scoped Kronecker
variable (p:Fin 3→ℂ)(y:Values 7)(h:quoV (y,p)=0)
local notation "J"=> (0:Axis)
local notation "K"=> (1:Axis)
set_option quotPrecheck false
local notation "E"=>(vectorZ a (y a)).val
local notation "C"=> (0:Hue)
include h
lemma pricesV : p 0=0 ∧ p 1=0:=by
     obtain ⟨X,h1,h2⟩:= plot_Y _ ruby_pick.choose_spec; have hz(X:Maxwell.TaylorTower su)(i:Axis):p 0 *pages (lexY X) (leapV.val i)+p 1 * pages (lexY X) (lunar.val i)=0:=by
          rw [← monetary 0 0 (0:Hue) (0:Hue) i 0 0 (vacancy _) X y p]; have ht: projection ((plaza (y,p)).val i)=0:= congr_fun h i; exact (auditor _ _ _ _ _ _ _ _ _ ((Qeq _).mp ht)).2
     have he:= hz X 0; rw[h1,h2,mul_zero,zero_add] at he; have hr: p 1=0:=(mul_eq_zero.mp he).resolve_right (by norm_num); obtain ⟨V,hV,h⟩:=plot_X _ ruby_pick.choose_spec; have ht:=hz V 0; rw [hV,mul_one,hr,zero_mul,add_zero] at ht; exact ⟨ht,hr⟩
private lemma transitV (v f g)(hF:SlashV v f)(c c':Hue)(X:Maxwell.TaylorTower su): vitality a v c c' f g hF X 10 (E J).val=0:=by
     have ht:projection ((plaza (y,p)).val J)=0:=congr_fun h _; rw[← tagsP a v c c' J f g hF X y p]; exact (auditor _ _ _ _ _ _ _ _ _ ((Qeq _).mp ht)).1
lemma soundV: y a 0=0∧y a 2=0 ∧ y a 6=0:=by
   obtain ⟨f,hF,hf⟩:= freedom; let W:= rowC; have hp(g:Pinor→ℂ)(z:ℂ):y a 0*(z*rowC g f 1)+ y a 2*(z*z*rowC g f (gamma J))=0:=by
        have ht:=transitV a p y h (z • axis) f g (radial f axis z hF) C C 0; rw [costV,twoL,twistS, twistR] at ht; change _=0 at ht; simp only [axis, Pi.smul_apply, Matrix.cons_val_zero,smul_eq_mul, mul_one,lexY,and_true, ↓reduceIte] at ht; have hy : ∀ i:Axis, StressFlux.curl0 J i (Maxwell.gaugeJet ((0:Maxwell.TaylorTower su) 0))= 0:=fun i=>by simp
        simp only[hy,show BendR.ore (0:su.Color)=0 from map_zero _,Matrix.zero_apply,zero_mul,Finset.sum_const_zero,mul_zero,add_zero] at ht; exact ht
   have hv(g:Pinor→ℂ) :y a 0*rowC g f 1=0∧y a 2*rowC g f (gamma J)=0:=by
         constructor; · linear_combination (hp g 1 - hp g (-1)) / 2
         linear_combination (hp g 1 + hp g (-1))/2
   obtain ⟨g,hg⟩:=findT f hf; obtain ⟨v,hv'⟩:=findR J f hf; have h0:y a 0=0:=(mul_eq_zero.mp (hv g).1).resolve_right hg; have h2:y a 2=0:=(mul_eq_zero.mp (hv v).2).resolve_right hv'
   let c':=Gpick; obtain ⟨V,hV⟩:= BrickM.rootY (StressFlux.leg0 J K c'); let X:Maxwell.TaylorTower su:=Pi.single 0 V; obtain ⟨b,hb⟩:=findR K f hf; have he:= transitV a p y h axis f b hF jPick iPick X; rw [costV,h0,h2, zero_mul,zero_mul,zero_add,zero_add,twistR,if_pos rfl] at he
   have hP : lexY X 0= StressFlux.leg0 J K c':=(congr_arg Maxwell.gaugeJet (show X 0=V from Pi.single_eq_same ..)).trans hV
   refine ⟨h0,h2,(mul_eq_zero.mp he).resolve_right ?_⟩; rw [hP,sum_eq_single K];
   · have hz: StressFlux.curl0 J K (StressFlux.leg0 J K c')=c':=by rw [StressFlux.curl0_leg]; norm_num [basis_eq,Fin.ext_iff]
     rw [hz]; exact mul_ne_zero findSlot.choose_spec.choose_spec hb
   · intro i _ hu; rw [StressFlux.curl0_leg]; have ht:(basis i K)=0:=by simp [basis_eq,hu, Ne.symm hu]
     norm_num only [ht,mul_zero,show basis K J=0 from (by simp [basis_eq]), show basis J K=0 from (by simp [basis_eq]),zero_mul,sub_zero,zero_smul,show BendR.ore (0:su.Color)=0 from map_zero _, Matrix.zero_apply]
   simp
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.soundV
