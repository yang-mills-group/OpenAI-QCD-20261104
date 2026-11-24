import YM.Giles.Sculpt
import YM.Tawny.Velo
/-! On- and Off-shell representation matrices. Gauge probes preserve three distinct directions.S. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
open scoped Kronecker
namespace Seals
variable {c:Side} {d:ℕ} (X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)(i j k l m:Axis)(J:Labels.Jet su)
noncomputable def veil(a:su.Color) : Fin 3→ Labels.Taylor su 0:=![legV a 0 1, legV a 1 2, legV a 0 1]
open Perla.BrickM
noncomputable def torchK(a:su.Color) : Fin 3→Labels.Taylor su 1:=![firstY a, secondY a, leg1 0 0 1 a]
noncomputable def mirage(i:Fin 3):= leanY (veil Gpick i) (torchK Gpick i)
lemma posts(i:Fin 3): Along Gpick (veil Gpick i)∧ Along Gpick (torchK Gpick i):=by
    have h: ‖Gpick‖=1:=ruby_pick.choose_spec -- open BendR
    fin_cases i
    · exact ⟨along_leg0 Gpick _ _ h, along_sub _ _ _ (along_leg1 _ _ _ _ h) (along_leg1 _ _ _ _ h)⟩
    · exact ⟨along_leg0 Gpick _ _ h, along_sub _ _ _ (along_leg1 _ _ _ _ h) (along_leg1 _ _ _ _ h)⟩
    exact ⟨along_leg0 Gpick _ _ h,along_leg1 _ _ _ _ h⟩
lemma capP(t:Label d) (p:ℂ) (hp:∀ x:ℝ,pages (scaleJet J (x^2)) t=x^d • p): capote d J t=p:=by
     change (d.factorial:ℝ)⁻¹ • iteratedDeriv d (fun x:ℝ=>pages (scaleJet J (x^2)) t) 0=_; simp_rw [hp]; rw [iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_fun_pow_zero, if_pos rfl, inv_smul_smul₀ (by positivity)]
lemma heartP(X: Fin 4→ℂ): capote 8 J ((gaugeσ X).val (i,j))= X 1* pages J (spire.val (i,j))+X 2* pages J (shadow.val (i,j))+X 3* pages J (eclipse.val (i,j)):=by
    have hp(i j:Axis) : capote 8 J (spire.val (i,j))= pages J (spire.val (i,j)):=by
         apply capP J; intro x; simp_rw[plots, scaleJet,map_smul, real_inner_smul_left,real_inner_smul_right, Complex.ofReal_mul, Finset.smul_sum]; refine sum_congr rfl fun a _=>?_ ; push_cast; rw [show x^8 • (_:ℂ)=(x:ℂ)^8 * _ from (by rw [← Complex.ofReal_pow]; rfl)]; ring
    have hS: capote 8 J (shadow.val (i,j))=pages J (shadow.val (i,j)):=by
         rw [plotS,shadow_val]; split; · rw[←spire_val, hp,spire_val] -- check rw clears
         · exact map_zero _ -- simpler shadow rewrite case
    have he: capote 8 J (eclipse.val (i,j)) = pages J (eclipse.val (i,j)):=by
         apply capP J; intro x; rw[plotD,plotD]; split; swap; · rw [smul_zero]
         simp_rw[scaleJet,map_smul,real_inner_smul_left,real_inner_smul_right,Complex.ofReal_mul,Finset.smul_sum]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>(by push_cast; rw [show x^8 • (_:ℂ)=(x:ℂ)^8 * _ from (by rw [← Complex.ofReal_pow]; rfl)]; ring)
    have hk: capote 8 J (epi.val (i,j))=0:=by change (↑(Nat.factorial 8):ℝ)⁻¹ • iteratedDeriv 8 (fun x:ℝ=>pages (scaleJet J (x^2)) (epi.val (i,j))) 0=0; simp_rw [plotA]; rw [iteratedDeriv_const,if_neg (by decide),smul_zero]
    simp only [gaugeσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,hp,hS,he,hk,mul_zero,zero_add,smul_eq_mul]
lemma capLE : capote 10 J (GE i j k l m)=pages J (GE i j k l m):=by
    let Z:= pairDeriv su i j k l m; have hp(J): pages J (GE i j k l m)= Labels.read J Z.val:=railX _ _ _ rfl -- rfl
    apply capP J; intro x; rw[hp,hp]; unfold Z; rw[StressFlux.pairDeriv_value,StressFlux.pairDeriv_value]; simp_rw [scaleJet,map_smul,real_inner_smul_left, real_inner_smul_right,Complex.ofReal_mul]; push_cast; rw [show x^10 • (_:ℂ)=(x:ℂ)^10 * _ from (by rw [← Complex.ofReal_pow]; rfl)]; ring
lemma grove(p:Fin 3→ℂ): capote 10 J ((ocean p).val i)= pages J ((ocean p).val i):=by simp only[ocean, Submodule.coe_add,Submodule.coe_smul, Pi.add_apply,Pi.smul_apply,map_add,map_smul,oleap,olun,oeul,map_sum,capLE]
lemma p_blank (a:Flavor 6)(B: Spike)(p q:Multi d)(L:Label d)(h:L.val=bilinear a a B p q): capote _ J L=0:= capP J L 0 (fun x=>by rw [smul_zero]; change Labels.read _ (fog L.val)= 0; rw[h,bareFog,map_zero]) -- placeholders
lemma p_spell (a:Flavor 6)(p q:Multi d)(B:Spike)(h:spinWeight p+spinWeight q ≤ d): capote _ J (mixed a B p q h)=0:=by unfold Carnal.mixed; rw [map_add,p_blank J a B p q _ rfl]; rw[p_blank _ _ (truck B) q p _ rfl,zero_add]
variable (a b:Flavor 6)
lemma p_pose (u:Values 4) (p:Fin 4→ℂ): capote 8 J ((poseσ (u,p)).val (i,j))= capote 8 J ((gaugeσ p).val (i,j)):=by
    change capote 8 J ((poseσT u+gaugeσ p).val _)=_; simp only[Submodule.coe_add,Pi.add_apply,map_add]; apply add_eq_right.mpr; unfold poseσT; simp only[AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, _root_.map_sum]; refine sum_eq_zero fun i' _=>?_ ; simp only [axisσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul]; rw [W_mass,W_sun,W_trace,W_wing]; split <;> simp only [W_sun,map_add,map_sum,alter,p_blank J i' 1 0 0 (solstice i' 1 (0:Multi 8) 0 (by rw [cost_root]; decide)) rfl,p_spell,sum_const_zero,map_zero,add_zero,smul_zero] -- corner cases
set_option maxRecDepth 4000 in
lemma p_α (u:Values 2) : capote 8 J ((poseα u).val (i,j))=0:=by
    rw [show poseα u=∑ a:Flavor 6,axisα a (u a) from rfl]
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,map_sum]; refine sum_eq_zero fun i' _=>?_ ; have hp(i j:Axis) : capote 8 J ((windS i').val (i,j))=0:=by
       change (capote 8 J) (alter i' i j+(-1:ℂ) • alter i' j i)=0; simp only[map_add,map_smul,alter,p_spell,smul_zero,add_zero]
    simp only[axisα,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,hp,W_arc,map_sum,triple,p_spell,smul_zero,sum_const_zero,zero_add]
lemma p_star(i j:Axis)(g:Flavor 6)(B:Spike):capote 10 J (med g i j B)=0:=by
    apply capP J; intro x; rw[smul_zero]; change Labels.read _ (fog (youthL _ _ _ _))=_; unfold youthL; rw[map_sum]; simp_rw[mintFog,sum_const_zero,map_zero] -- mintFog
lemma p_value (v: Values 7)(p:Fin 3→ℂ): capote 10 J ((plaza (v,p)).val i)=pages J ((ocean p).val i):=by
    rw [← grove]; change capote 10 J ((vectorY v+ ocean _).val i)=_; simp only[Submodule.coe_add,Pi.add_apply,map_add]; apply add_eq_right.mpr; unfold vectorY; simp only[AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,map_sum]; refine sum_eq_zero fun a _=>?_ ; simp only[vectorZ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,bee_val,sea_val,lup_val,lap_val,s_val,t_val,star_val,map_sum,p_star, beta,sea,shell0,shell1,shell2,basil,p_spell,map_add,map_sub, zero_add,sum_const_zero,smul_zero] -- adapt.
end Seals
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.Seals.p_value
#print axioms YM.Massive.Patria.Gall.Seals.heartP
