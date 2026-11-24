import YM.Avian.Icarus
/-! Cart probes rank three through genuine relative root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Seals
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
local notation "Q"=> fun j=>pages (mirage j) (leapV.val 0)
local notation "P"=> fun j=>pages (mirage j) (lunar.val 0)
local notation "T"=> fun j=>pages (mirage j) (eulerV.val 0)
private lemma pick_p : ‖Gpick‖=1:= ruby_pick.choose_spec
lemma M_corner0 : Q 0=1∧P 0=2∧ T 0=0:=by
    dsimp only; rw [plotL,plotH,plot_E]; simp only[mirage,veil,legV,torchK,leanV0,leanV1]; dsimp only[Matrix.cons_val_zero]; simp_rw[firstY, StressFlux.curl0_leg,map_sub,StressFlux.curl1_leg]; norm_num[Fin.sum_univ_four,basis_eq,Fin.ext_iff,pick_p]
lemma M_corner1 : Q 1=0∧P 1=2∧ T 1=0:=by
    dsimp only; rw [show mirage 1=leanY (leg0 (1:Axis) 2 Gpick) (secondY Gpick) from rfl,plotL,plotH,plot_E]; simp only[leanV0,leanV1]; simp_rw[secondY, StressFlux.curl0_leg,map_sub,StressFlux.curl1_leg]; norm_num[Fin.sum_univ_four,basis_eq,Fin.ext_iff,pick_p] <;> rw [inner_add_right,inner_sub_right,real_inner_smul_right,inner_neg_right] <;> norm_num[real_inner_smul_right,pick_p]
lemma M_corner2 : T 2≠0:=by
    dsimp only; change pages (leanY (leg0 (0:Axis) 1 Gpick) (leg1 0 0 1 Gpick)) _≠_; rw [plot_E]; simp only [leanV0,leanV1]; simp_rw [StressFlux.curl0_leg,StressFlux.curl1_leg]; norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff,pick_p]
-- output rows independent
lemma cord (x: Fin 3→ℂ)(h:∀ y:Fin 3, pages (mirage y) ((ocean x).val 0)=0): x=0:=by
    have he(y:Fin 3) : x 0 * Q y + x 1* P y+x 2*T y=0:=(seaF x 0 (mirage y)).symm.trans (h y)
    have hv:= M_corner1; have h1: x 1=0:=by have hp:=he 1; rw[hv.1,hv.2.1,hv.2.2,mul_zero,mul_zero,zero_add,add_zero] at hp; exact (mul_eq_zero.mp hp).resolve_right (by norm_num)
    have hz:= M_corner0; have h0: x 0=0:=by have hp:=he 0; simpa only[h1,hz.1,hz.2.1,hz.2.2,zero_mul,add_zero,mul_one,mul_zero] using hp
    funext i; fin_cases i; exact h0; exact h1; have hp:= he 2; rw[h1,h0,zero_mul,zero_mul,zero_add,zero_add] at hp; exact (mul_eq_zero.mp hp).resolve_right M_corner2
variable (u:Values 4)(p:Fin 4→ℂ)
lemma levy (h:∀ (y:Fin 3),∑ k:Axis, pan (veil Gpick y) (torchK Gpick y) k ((poseσ (u,p)).val (k,0))=0) : p 1=0∧p 2=0∧p 3=0:=by
      let r:Fin 3→ℂ:= ![2*p 2,(1/2:ℂ)*p 1+2*p 3,p 1]; have he:r=0:=by
            apply cord r; intro t; have ht:=h t; rw [pan_plot] at ht; rw [seaF]; change 2*p 2* Q t+((1/2:ℂ)*p 1+2*p 3)*P t+p 1*T t= _; change p 1 * (T t+1/2*P t)+ p 2*(2*Q t)+p 3*(2*P t)=0 at ht; rw [← ht]; ring
      have h1:p 1=0:=congr_fun he (2:Fin 3); have hh: (1/2:ℂ)*p 1+2*p 3=0:=congr_fun he (1:Fin 3); rw [h1,mul_zero,zero_add] at hh; exact ⟨h1,(mul_eq_zero.mp (show 2*p 2=0 from congr_fun he (0:Fin 3))).resolve_left (by norm_num), (mul_eq_zero.mp hh).resolve_left (by norm_num)⟩
end YM.Massive.Patria.Gall.Seals
#print axioms YM.Massive.Patria.Gall.Seals.levy
