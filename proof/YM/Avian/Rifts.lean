import YM.Avian.Tore
import YM.Avian.Arun
/-! Core obligations for rank. Including exact physical surjection conditional on U-rank, alt probe. Transport at P.* orientation.Powers.X. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open YM.Sprig Tarn Tarn.Choir Pollens
open Rolls
open StressFlux.Offer (acts marks Vc)
local notation "Xσ"=> RawTensor 1 8
local notation "Xa"=> RawTensor (-1) 8
local notation "A"=> RawVec 10
local notation "T"=> Axis × Axis
noncomputable def crow(e:ℂ): Nest (Axis×Axis) := {
   Q:=fun s=>Equiv.prodCongr s.perm s.perm
   c:=marks
   w:=fun s i=>by unfold marks StressFlux.sign; split <;> split <;> norm_num
   t:=Equiv.prodComm _ _
   e:=e }
noncomputable def claw : Nest Axis:= { Q:=fun s=>s.perm,c:=signT,w:=fun s i=> UV.sign_sq ..,t:= Equiv.refl _,e:=1 }
abbrev bits (Q:Choir): A →ₗ[ℂ](Axis→Q.W):= polls claw 10 shelV Q
abbrev obσ (e:ℂ) (Q:Choir): RawTensor e 8→ₗ[ℂ](T→Q.W):= polls (crow e) 8 (fun i=>shelS i.1 i.2) Q
lemma equalT (e:ℂ): Veer (crow e) (fun i=>shelS i.1 i.2):=fun i k=> pays_rotate _ _
lemma equalV : Veer claw shelV:=fun i k=> pays_rotate _ _
variable {C:Sequence}{P:Calibration C}{Q:Choir}{φ:ℕ→ℕ}(L:Pollens P Q)(hP:P.System)(h: Q.Domestic)(hS:∀ d,∃ n:Side,Injective (P.candidate d n 0))
variable (Ux:∀ d, UV.Free.Symbol d ≃ₗ[ℂ]↥(Q.level d))(hx:∀ d,YM.Sprig.Prose (Ux d) L)
include hx hP hS h
lemma alt_rank (e:ℂ): Module.finrank ℂ (obσ e Q).range= Module.finrank ℂ (prize (crow e) 8).range:=by obtain ⟨n,hG⟩:=hS 8; exact point_rank L (crow e) 8 (fun i=>shelS i.1 i.2) _ (hx _) n h hP hG (equalT _) (fun i=>signP _ _)
omit hx hP hS h
private lemma beta:(prize claw 10)=Drill.symbV:=by -- defeq types
     apply LinearMap.ext; intro s; rfl
private lemma αl (e:ℂ): prize (crow e) 8=Drill.symbS e:=LinearMap.ext fun i=>rfl
include hx hP hS h
lemma torchV : Module.finrank ℂ (bits Q).range=20:=by
     obtain ⟨n,hG⟩:= hS 10; refine (point_rank L claw 10 shelV _ (hx _) n h hP hG equalV (fun _=>rfl)).trans ?_; rw [beta]; exact Drill.tall.2.2
lemma talent : Module.finrank ℂ (obσ (-1) Q).range=6:= (alt_rank L hP h hS Ux hx _).trans ((αl (-1)) ▸ Drill.tall.2.1) -- omit includes
lemma tinted : Module.finrank ℂ (obσ 1 Q).range=22:= (alt_rank L hP h hS Ux hx _).trans ((αl 1) ▸ Drill.tall.1)
omit hx hP hS h
noncomputable def divR (Q:Choir): (T→Q.W) →ₗ[ℂ] (Axis→Q.W):= LinearMap.pi fun i=> ∑ j,Q.arc j ∘ₗ LinearMap.proj (j,i)
noncomputable abbrev swingE(Q:Choir)(e:ℂ): RawTensor e 8→ₗ[ℂ](Axis→Q.W):= divR Q ∘ₗ obσ e Q
lemma lifta (e:ℂ)(v:RawTensor e 8)(i:Axis): swingE Q e v i=∑ a:Axis,Q.arc a (Q.focus (shelS a i) 8 (v.val (a,i))):=by unfold swingE divR; rw[LinearMap.comp_apply,LinearMap.pi_apply,LinearMap.sum_apply]; rfl
open Seals
noncomputable abbrev Pond:= Flavor 6→ℂ
-- Channel chosen ANY given color read F support.Separ.A. Mats.Use define selectors B and Q later.V.PQR.
variable (Phi1 Phi2:Memory→ₗ[ℂ]Pond)
noncomputable def tallyF (B C:Memory→ₗ[ℂ]Pond): A →ₗ[ℂ] (Pond×Pond):= (B ∘ₗ lookB).prod (C ∘ₗ lookQ)
variable (F:A→ₗ[ℂ](Pond×Pond))
-- premise abstract row scan realized Stress.
def Firm (Q:Choir)(x:ℂ): Prop:= ∀ p: RawTensor x 8,∃ d:A,(viewsL d)=viewsX x p∧lookQ d=0∧ lookB d=0∧∀ i:Axis,swingE Q x p i=bits Q d i
lemma plea {x:ℂ}(hp:Firm Q x):∃ Z:RawTensor x 8→ₗ[ℂ] A,(viewsL∘ₗZ)=viewsX x∧ ((tallyF Phi1 Phi2) ∘ₗ Z)=0∧ ((bits Q) ∘ₗ Z)=swingE Q x :=by
     choose y hy hp hG hV using hp; let z: RawTensor x 8 →ₗ[ℂ] A:= {
              toFun:=y,
              map_add':=fun a b=>by
                 apply scansion; apply Prod.ext
                 · change viewsL _= viewsL _; rw[hy,map_add,map_add,hy,hy]
                 change lookQ _= lookQ _; rw[hp,map_add,hp,hp,zero_add]
              map_smul':=fun t a=>by
                 apply scansion; apply Prod.ext
                 · change viewsL _=viewsL _; rw[hy,map_smul,map_smul,hy]; rfl
                 change lookQ _=lookQ _; rw [hp,map_smul,hp,smul_zero] }
     refine ⟨z,LinearMap.ext fun i=>hy i, LinearMap.ext fun i=> Prod.ext ((show Phi1 (lookB (y i))=0 by rw[hG,map_zero])) ((show Phi2 (lookQ (y i))=0 by rw[hp,map_zero])),LinearMap.ext fun i=>funext fun a=>(hV i a).symm⟩
-- dimensions
end YM.Massive.Patria.Gall.Onyx
#print axioms YM.Massive.Patria.Gall.Onyx.talent
