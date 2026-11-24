import YM.QCD.Globe.Ovaltine
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable {X: Sheet c}
def Pina (X:Sheet c)(o:Site c)(D:Option Axis):Bundle:= (↑(Fintype.card Signed):ℂ)⁻¹ • ∑ j:Site c, ∑ i: Signed, (D.elim (1:ℂ) (fun a=>(foam i j a:ℂ))) • onset X o (foam i j)
def CoatM (A: Option Axis)(w:ℝ):Bundle:=wave (A.elim ((w:ℂ) • 1) fun i=>(w:ℂ) • Lat.gamma i)
lemma wavS (x:Spike)(c:ℂ):wave (c • x) = c • wave x:= Matrix.smul_kronecker ..

lemma wave_p {D:Type*}(f:D→Spike)(s:Finset D):wave (∑ i∈s,f i)= ∑ i∈s,wave (f i):=by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; apply Matrix.zero_kronecker -- maybe
   | insert a t ht ih=>rw [sum_insert ht,sum_insert ht]; unfold wave; rw [Matrix.add_kronecker]; exact congr_arg (fun x=>wave (f a)+x) ih
lemma Tempo.night (h: Tempo X)(o:Site c) : Pina X o none=CoatM none (mass X):=by
      let u:=0; rw [CoatM]; change _=wave ((mass X:ℂ) • (1:Spike)); rw [← (h.glitter o 0).1,nectar,wavS,wave_p]; unfold Pina; simp_rw [h.giltV, wave_p]; simp [kran]
lemma krans (v:Cover)(i:Axis): (kran (some (i,true)) v)-(kran (some (i,false)) v)=(v i:ℂ):=by simp only [kran,Option.elim_some,Bool.false_eq_true,↓reduceIte]; ring
lemma Tempo.flange (h:Tempo X)(o:Site c)(i:Axis): Pina X o (some i)=CoatM (some i) (sheen X):=by
      rw [CoatM]; change _=wave ((sheen X:ℂ) • Lat.gamma i); rw [← (h.glitter o i).2,nectar, nectar,← smul_sub,← sum_sub_distrib,wavS,wave_p]; unfold Pina; apply congr_arg; apply sum_congr rfl; intro j _; rw [← sum_sub_distrib,wave_p]; refine sum_congr rfl fun p _=>?_ ; rw [h.giltV,← sub_smul,wavS,krans]; rfl
lemma onset_s (v:ℂ)(o:Site c)(w:Cover): onset (v • X) o w=v • onset X o w:=by unfold onset; rw [show cell _ _ _=v • _ from rfl, smul_comm]; rfl -- ambiguous
lemma onset_add (X Y:Sheet c)(o:Site c)(w:Cover): onset (X+Y) o w=onset X o w + onset Y o w:=by unfold onset; rw [show cell (X+Y) _ _ = cell X o _+ cell Y o _ from rfl, smul_add]
noncomputable def pina (o:Site c)(D:Option Axis): Sheet c →ₗ[ℂ] Bundle where
   toFun:=fun X=>Pina X o D
   map_add':=fun x y=>by unfold Pina;simp only [onset_add,smul_add,sum_add_distrib]
   map_smul':=fun a x=>by unfold Pina; simp_rw [RingHom.id_apply,onset_s]; rw [smul_comm a _]; apply congr_arg; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; exact smul_comm ..
-- existence calibrate sites
lemma onsetH (o:Site c)(p:Signed)(j:Site c):onset (1:Sheet c) o (foam p j)= if j=0 then 1 else 0:=by
     unfold onset; by_cases he : j=0
     · subst j; have hz: foam p (0:Site c)=0:=by simp [foam]
       rw [hz,map_zero,add_zero, if_pos rfl,show occ o 0=1 from ?_,one_smul];
       · ext i j; by_cases h : i=j<;> simp [cell,Matrix.one_apply,h]
       unfold occ; rw [route_same]; rfl
     rw [foams,if_neg he]; have hx:cell (1:Sheet c) o (o+j)=0:=by ext i k; simp [cell, he]; -- edit
     rw [hx,smul_zero]
lemma lesson (m:ℝ):|m| = ‖CoatM none m‖:=by rw [CoatM,Option.elim_none, wavS,wave_one,norm_smul,norm_one,Complex.norm_real,mul_one,Real.norm_eq_abs]
lemma lesson_s (i:Axis)(m:ℝ):|m|= ‖CoatM (some i) m‖:=by
    rw [CoatM, Option.elim_some,wavS,norm_smul,Complex.norm_real,Real.norm_eq_abs]; have he : ‖wave (Lat.gamma i)‖= 1 :=?_; rw [he,mul_one]
    apply le_antisymm (Lat.rotation_price (wobble _ ⟨by simp,by simp⟩))
    let W:= wave (Lat.gamma i); have ht : W*W=1:=by unfold W; rw [wave_mul, Lat.gamma_sq,wave_one]
    have hh:= norm_mul_le W W; rw [ht,norm_one] at hh; change 1 ≤ ‖W‖; nlinarith [norm_nonneg W]
-- turnover
lemma coat1 : Pina (1:Sheet c) (0:Site c) none=1:=by
    unfold Pina; simp_rw [onsetH]; simp only [Option.elim_none,one_smul, sum_const,card_univ,smul_ite,smul_zero,sum_ite_eq', mem_univ, if_true]; rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,inv_mul_cancel₀ _,one_smul] -- needs cast
    exact_mod_cast Fintype.card_ne_zero (α:=Signed)
lemma coatS (i:Axis):Pina (1:Sheet c) (0:Site c) (some i)=0:=by
    unfold Pina; simp_rw [onsetH]; rw [sum_eq_zero,smul_zero]; intro v _; apply sum_eq_zero; intro j _; split
    next h=>subst v;simp [foam,lift,Signed.act]
    simp
end YM.QCD.Globe
