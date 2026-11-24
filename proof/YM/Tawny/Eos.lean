import YM.Tawny.Beacon
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
open Carnal Perla Zinc Perla.Fore BrickM
open StressFlux (leg0 curl0 curl1)
open scoped InnerProductSpace
variable (x:Fin 4→ℂ)(y:Fin 2→ℂ)(p q: Multi 8)(J:Labels.Jet su)(i j k:Axis)
local notation "SX"=>RawTensor 1 8
local notation "TX"=>RawTensor (-1) 8
local notation "Z"=> (0:Multi 8)
local notation "L"=> UV.first
local notation "u"=> (0:Axis)
local notation "r"=> (1:Axis)
set_option quotPrecheck false
local notation "ψ"=> prism0
lemma zenith (hz:∀ (p q: Multi 8)(i j:Axis),prism0 a p q ((axisσ a x).val (i,j)).val=0):x=0:=by
     have he:=probe_zero u (x 1) ((railσ1 a x).symm.trans (hz ..)); have hk:=probe_zero r (x 3) ((railσ2 a x).symm.trans (hz ..)); have hq:= (railσ3 a x).symm.trans (hz ..); rw [he,hk,zero_smul, zero_smul, zero_add, add_zero, ← two_smul ℂ, smul_smul] at hq
     funext i; fin_cases i; exact probe_one _ ((railσ0 a x).symm.trans (hz ..)); exact he; exact (mul_eq_zero.mp (probe_zero _ _ hq)).resolve_right (by norm_num); exact hk
lemma zalt (hz:∀ (p q:Multi 8)(i j:Axis),prism0 a p q ((axisα a y).val (i,j)).val=0): y=0:=by
     funext i; fin_cases i; exact probe_zero u (y 0) ((railα0 a y).symm.trans (hz ..)); apply probe_zero (2:Axis); have he:= (railα1 a y).symm.trans (hz ..); rw [trio,if_neg (by decide)] at he; let f:= y 1 • gamma (2:Axis)
     have ht: f= f*gamma 0*gamma 1*gamma 1*gamma 0:=by rw [mul_assoc (f*gamma (0:Axis)),Lat.gamma_sq, mul_one, mul_assoc, Lat.gamma_sq,mul_one] -- check assoc with 4
     change f=0; rw [ht]; unfold f; rw[Matrix.smul_mul,Matrix.smul_mul,he,zero_mul,zero_mul]
lemma zeta : pages J ((gaugeσ x).val (i,j))= x 0* pages J (epi.val (i,j)) + x 1*pages J (spire.val (i,j))+x 2*pages J (shadow.val (i,j))+x 3*pages J (eclipse.val (i,j)):=by simp[gaugeσ]
variable (C:su.Color)(ht:‖C‖=1)
lemma axis_plot (hz:∀ (J:Maxwell.TaylorTower su)(i j:Axis),pages (lexY J) ((gaugeσ x).val (i,j))=0): x=0:=by
    let C:=ruby_pick.choose; have he:‖C‖=1:=ruby_pick.choose_spec
    have hp(A:Labels.Taylor su 0)(i j:Axis): ∃ J:Labels.Jet su,J 0=A ∧ pages J ((gaugeσ x).val (i,j))=0:=by
         obtain ⟨v,hv⟩:= rootY A; refine ⟨lexY (Pi.single 0 v),Eq.trans (congr_arg Maxwell.gaugeJet (Pi.single_eq_same ..)) hv,hz _ i j⟩
    obtain ⟨U,h,H⟩:=hp 0 0 0; rw[zeta,plotD,plotS,plots,plotA,h] at H; have h0:x 0=0:=by simpa using H
    obtain ⟨X,hx1,hx2⟩:=hp (leg0 (0:Axis) (1:Axis) C+leg0 (2:Axis) 1 C) 0 2; rw[zeta,h0,zero_mul,plotS,if_neg (by decide : (0:Axis)≠2),mul_zero,plotD,if_neg (by decide),mul_zero,zero_add,add_zero,add_zero,plots,hx1] at hx2; have h1:x 1=0:=by
         simp_rw [map_add,StressFlux.curl0_leg] at hx2; norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff,he] at hx2; exact hx2
    obtain ⟨Y,pY,hY⟩:=hp (leg0 (1:Axis) (2:Axis) C) 0 0; rw [zeta,h0,h1, zero_mul,zero_mul,plotS,if_pos rfl, plots,plotD,if_pos rfl,pY] at hY
    have h3:x 3=0:=by simp_rw [StressFlux.curl0_leg] at hY; norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff,he] at hY; exact hY
    obtain ⟨V,hv,hw⟩:= hp (leg0 (0:Axis) (1:Axis) C) 0 0; rw[zeta,h0,h1,h3,zero_mul,zero_mul,zero_mul,add_zero,zero_add,zero_add,plotS,if_pos rfl, plots,hv] at hw; have h2:x 2=0:=by simp_rw[StressFlux.curl0_leg] at hw; norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff,he] at hw; exact hw
    funext i; fin_cases i; exact h0; exact h1; exact h2; exact h3
open LinearMap
lemma sig_u: Injective poseσ:=by
     refine (ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=Values 4 × (Fin 4→ℂ)) (M₂:=SX) (f:=poseσ)).mp (ker_eq_bot'.mpr ?_); rintro ⟨v,c⟩ h
     have ht:v=0:=funext fun a=> zenith a _ (fun p q i j=> by rw[←recognize a p q i j v c,h]; exact map_zero _); have hp: poseσ (v,c)=gaugeσ c:=by
        rw [ht]; change poseσT 0+_= _; rw [show poseσT 0=0 from (by simp[poseσT,axisσ]),zero_add]; -- reduction
     rw [hp] at h; exact Prod.ext ht (axis_plot c (fun X i j=>by rw[h]; exact map_zero _))
lemma alt_u: Injective poseα:=by
     refine (ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=Values 2) (M₂:=TX) (f:=poseα)).mp (ker_eq_bot'.mpr ?_); intro v h; funext a; apply zalt _ (a:=a); intro p q i j; rw [← recognizeA,h]; exact map_zero _
local instance (e:ℂ):FiniteDimensional ℂ (RawTensor e 8):=FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=Axis×Axis→Label 8) (RawTensor e 8)
lemma tolls (n:ℕ): Module.finrank ℂ (Values n)=6*n:=by unfold Values; rw[Module.finrank_pi_fintype]; simp only [Module.finrank_fin_fun,sum_const,card_univ,Flavor,Fintype.card_fin,nsmul_eq_mul]; rfl
lemma bona : Bijective poseσ∧Bijective poseα:=by
     constructor
     · have he:Module.finrank ℂ poseσ.range=28:= (LinearMap.finrank_range_of_inj sig_u).trans (by rw[Module.finrank_prod,tolls,Module.finrank_fin_fun]); exact ⟨sig_u,range_eq_top.mp (Submodule.eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm (by rw [he]; exact sky_scope.1)))⟩
     have he:Module.finrank ℂ poseα.range=12:= (LinearMap.finrank_range_of_inj alt_u).trans (by rw[tolls]); exact ⟨alt_u,range_eq_top.mp (Submodule.eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm (by rw [he]; exact sky_scope.2)))⟩
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.bona
