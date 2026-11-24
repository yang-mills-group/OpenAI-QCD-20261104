import YM.QCD.Globe.Terp
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
open Nola
variable (S h) (D:Sheet f)(X:EvenA f N)
set_option quotPrecheck false
local notation "K"=> (father S h + D)
local notation "Q"=> tied S h 0 1
local notation "M"=> 1 - Q*K⁻¹*(Q)ᴴ
noncomputable def switchU (A:Kit.Rail f c)(V:Kit.Rail c f): EvenA f N→ₐ[ℂ] EvenA c N:= car (adapter (choir _ A) (choir _ V)ᵀ) fun x h=>(exterior_parity _ x).trans (congr_arg _ h)
noncomputable abbrev warp (Z:EvenA f N): EvenA c N:= switchU (K⁻¹*(Q)ᴴ) (Q*K⁻¹) Z
def UPr (Z:EvenA c N):= coef ∅ Z.val
lemma ring_of (Y:EvenA c N): exp Y.val = Complex.exp (UPr Y) • exp (oilD Y).val:=by
     have hp : Stew.stage 0 Y=sparkF c N (UPr Y):=Subtype.ext (bush Y.val)
     let S:=Stew.stage 0 Y; let Z:=Y-S
     have he:Y=S+Z:=by unfold Z; abel
     calc
       _ = Cove.light _ (exp (S+Z)):= Eq.trans ((Cove.light_exp Y).symm) (congr_arg (Cove.light _ ∘ exp) he)
       _ = _:=by unfold S; change light _ (exp (Stew.stage 0 Y+Z))=_; rw [exp_add,map_mul,hp,sky_first,map_smul,map_one, light_exp,smul_mul_assoc,one_mul]; rfl -- edit
lemma oil₀ (Y:EvenA c N): UPr (oilD Y)=0:=by change coef ∅ (Y.val-(Stew.stage 0 Y).val)=0; rw [map_sub,raze,card_empty,if_pos rfl,sub_self]
lemma whiteZ (Y:Sheet c): UPr (paleF N Y)=0:=spectrum (Grass.form_two _) _ (by simp)
lemma oaks (F:EvenA c N)(W:Sheet c):exp (paleF N W + F).val=gauss (copies N W)* exp F.val:=by
       calc exp (paleF N W + F).val= Cove.light _ (exp (paleF N W +F)):= (Cove.light_exp (paleF N W +F)).symm
            _ = _:=by rw [exp_add,map_mul,Cove.light_exp,Cove.light_exp]; rfl
lemma kinderR {D E:Type*}[Fintype D][Fintype E][hx:DecidableEq D][hy:DecidableEq E](Y:Matrix D D ℂ)(Qp: Matrix E D ℂ)(X Z:Patio (Pairs D))(hP:IsUnit (Y+Qpᴴ*Qp).det)(he: fade (Y+Qpᴴ*Qp)⁻¹ (exp X.val)=exp Z.val): let H:=Y+Qpᴴ*Qp; let F:=1-Qp*H⁻¹*Qpᴴ; sheath 1 Qp (gauss Y* exp X.val)= H.det • (gauss F * exp (adapter (H⁻¹*Qpᴴ) (Qp*H⁻¹).transpose Z.val)):=by
    rw [show hx=Classical.typeDecidableEq _ from Subsingleton.elim ..] at *; rw [show hy=Classical.typeDecidableEq _ from Subsingleton.elim ..]; exact Nola.kinder _ _ _ _ hP he
lemma cocoa_step (P:Plan j)(hp: IsUnit (K).det)(hx:Tempo D)(he:Cocoa X)(Z:EvenA f N)(hZ:fade (copies N K⁻¹) (exp X.val)=exp Z.val) :
    sheath 1 (choir N (Q)) (exp (paleF N (sunny P S.wing f + D) + X).val)=((K).det^N*Complex.exp (UPr (warp S h D Z))) • exp (paleF N (M)+oilD (warp S h D Z)).val ∧ Cocoa (oilD (warp S h D Z)):=by
    let E:=sunny P S.wing f + D; let B:= choir N (Q); let G:= copies N E; let A:=paleF N E+X; let M': Sheet c:= M; let Y:= oilD (warp S h D Z)
    have ht:Y.val= _:=rfl
    have hv:G+Bᴴ*B=copies N (K):=by
         have hh : E+(Q)ᴴ*Q= K:=by unfold E sunny; rw [Pine.bare_this]; unfold father; unfold conn; abel
         rw [← hh,RP.copies_add]; unfold B; rw [← choir_star,← choir_mul]; rfl -- check
    have hy := linked (K) N hp; have hm:IsUnit (copies N K).det:=by rw [copies_det]; exact hp.pow _
    have hA: sheath 1 B (exp A.val) = ((K).det^N*Complex.exp (UPr (warp S h D Z))) • exp (paleF N M'+Y).val:=by
          unfold A; rw [oaks,oaks];
          have hf: fade ((copies N E+Bᴴ*B)⁻¹) (exp X.val)= exp Z.val:=by rw [hv, ← hy]; exact hZ
          have hP:IsUnit (G+Bᴴ*B).det:=by rw [hv]; exact hm
          have hp:= kinderR (D:=Modes f N) (E:=Modes c N) G B X Z hP hf; dsimp only at hp; rw [hv,←hy] at hp; apply hp.trans
          unfold B; rw [← choir_star,← show choir N K⁻¹=copies N K⁻¹ from replicas ..,← choir_mul,← choir_mul,← choir_mul] -- inspect
          have hQ: 1-choir N (Q*K⁻¹*(Q)ᴴ)= Lat.copies N M':=by unfold M'; rw [← copies_one N]; exact (Matrix.blockDiagonal_sub (fun _ : Flavor N=> (1: Sheet c)) (fun _=> Q*K⁻¹*(Q)ᴴ)).symm -- inspect
          rw [hQ];
          change _ • (_*exp (warp S h D Z).val)=_
          rw [copies_det,ring_of (warp S h D Z), Algebra.mul_smul_comm,smul_smul] -- alias
    refine ⟨hA,?_⟩; have hm':= temperQ S h P D hx; have ht:= weather S h A (paleF N M'+Y) (((savior P S.wing).add hx).butter N|>.add he) _ (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Complex.exp_ne_zero _)) hA (show UPr (paleF N M'+Y)=0 from ?_)
    · rw [show oilD (warp S h D Z)=(paleF N M'+Y) - paleF N M' from Eq.symm (add_sub_cancel_left ..)]; exact ht.sub (hm'.butter N)
    unfold UPr; change coef ∅ ((paleF N M').val+Y.val)=0; rw [map_add,show coef ∅ (paleF N M').val=0 from (whiteZ (N:=N) M'), show coef ∅ Y.val=0 from oil₀ _, add_zero]
end YM.QCD.Globe
