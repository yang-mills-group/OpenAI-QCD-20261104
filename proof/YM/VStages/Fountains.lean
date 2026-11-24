import YM.VStages.Bond
import YM.QCD.Fount.Read
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Fount
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Jets Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR
variable {i b j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a A B w ν α s L y u' :ℝ} {M:ParcelR}
variable (P:Plan j)(P₂:Plan k) (V : Back E K j k p u v) {X Y: SunR M} (Q:Avenue V η Ω Θ)
local notation "ds" =>divides0 V.fly V.chain i
local notation "K₀"=>park V.fly (divides0 V.fly V.chain i) P X.X X.Y t 0
local notation "Γ"=>fun z:Cnr (V.chain.n i)=> (encamp (V.port.forest i) (V.port.u i) z).1
variable (hR:Rates M s)(hp:Species V.fly (divides0 V.fly V.chain i) w ν r 0 a b (park V.fly (divides0 V.fly V.chain i) P X.X X.Y t 0))(hr:0<r)(ht:0<t)(hx:t≤1)
include hR hp hr ht hx
lemma iceMarch : Duet (K₀ ∘ Stationary.input su _) ((fun U=>shiftH V.fly ds P (X.powerG _) U) ∘ Stationary.input su _) :=by
   let f:=K₀ ∘ Stationary.input su _; have hf:= roomP K₀ hp hr
   have h:=Raft.sessionD (Tee.kinder X.X X.Y (n:= high V.fly V.chain i) hR.hr hR.hs ht hx)
   let A:=f - castF (blossomT X.X X.Y t _); have hA:ContDiffAt ℝ ω A 0:= hf.1.sub h.leftF
   have hz:= (Duet.together hA EventuallyEq.rfl).add h; unfold A at hz
   rw [sub_add_cancel] at hz; apply Duet.chain hz; refine Duet.together hz.rightF (Eventually.of_forall fun j=>?_)
   simp [f,Function.comp_apply,park,pesto,Tee.trunkM,castF, SunR.powerG,mingle,shiftH]; rfl

variable (he:Mist.BirthW M P P₂ V Q X Y α)(he':0 < u')(hQ:u'≤1)
include he he' hQ
lemma sidestep : Duet (foam V.fly ds K₀ ∘ Γ) (castF (FieldB M Y (V.chain.n i) u' P₂ V.fly.land)) :=by
   obtain ⟨W,hW,hH,hV,hx'⟩:=Raft.lecture V i Q; let g:=Stationary.input su _ ∘ W
   have hv:=duct W (iceMarch P V hR hp hr ht hx) hH hW
   let L:= tied V.fly ds 0
   have hl:= roomP K₀ hp hr; have hp':ContDiffAt ℝ ω (L ∘ g) 0:= (show ContDiffAt ℝ ω (L∘Stationary.input su _) (W 0) from hW.symm ▸ hl.2).comp 0 hH
   let n:=V.chain.n i; let k:= high V.fly V.chain i
   let G t:= (K₀ (g t),L (g t))
   let f' (z:Sheet k × Rail n k):= 1-z.2*z.1⁻¹*z.2ᴴ
   have hf:ContDiffAt ℝ ω f' (G 0):=contDiffAt_const.sub (ink_multiply (ink_multiply contDiffAt_snd (inverse_ink contDiffAt_fst (show IsUnit (K₀ _).det from hp.sole _))) (ink_star contDiffAt_snd))
   have hg:= duchy f' (paired hv (Duet.together hp' EventuallyEq.rfl)) hf
   have hgg:= (Duet.together hg.leftF (hV.symm.mono (fun z hz=> (show f' (G z)=foam V.fly ds K₀ ((Γ) z) from congr_arg (foam V.fly ds K₀) hz)))).flip
   have hf':=Duet.together hg.rightF (Q:= pulseShift V.port P X.powerG i) ?_; rotate_left
   · exact hV.symm.mono (fun z hz=>congr_arg (fun j=>shiftL V.fly ds P (X.powerG _) j) hz) -- x scope G param
   have hc:= ((hgg.chain hg).chain hf').chain (warrant P P₂ V i (he.limbs i))
   have h:=Raft.sessionD (Tee.kinder Y.X Y.Y (n:=n) hR.hr hR.hs he' hQ)
   let S:= castF fun U:Grid n=> wood P₂ 0 V.fly.land U; have he: S=(caravan P₂ V.fly.land Y.powerG n∘ Stationary.input su n)-castF (Y.powerG n):=funext fun i=> by simp only [castF,Function.comp_apply,Raft.caravan,Pi.sub_apply,add_sub_cancel_right]; rfl
   have hF : ContDiffAt ℝ ω S 0:= he ▸ hc.rightF.sub h.rightF
   exact hc.chain ((Duet.together hF EventuallyEq.rfl).add h.flip)
end YM.QCD.Fount
