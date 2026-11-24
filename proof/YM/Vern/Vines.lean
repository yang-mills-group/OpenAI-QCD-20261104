import YM.Vern.Muzzle
set_option autoImplicit false
set_option maxHeartbeats 910000
noncomputable section
namespace YM.NativeV
open Function Set Filter Analysis
open scoped Topology BigOperators Classical
open Lobo Vern Finset
variable {W X:Type}[AddCommGroup W][Module ℂ W][AddCommGroup X][Module ℂ X]
variable (C:Medal W)(J:Drift C X)(p f:ℝ)(T:Tri→Tri→W)(ht:Olive C p f T)
variable (V:Tri→X)(e:ℝ)
-- spatial μ-planes. compose three character averaging. choose Q0² k=0 & Q1². then key action character. p rows schedule: for r=i:Axis all
noncomputable def maybeQ (a:Axis):Tri:= ![0,2,1,0] a -- final
noncomputable def sAlpha(a:Axis):ℂ:=![1,-1,-1,1] a
-- signs q0²: diag=1,01 -,02 -, time0+. q1²: diag+,01-,02+, time0-.
noncomputable def sBeta(a:Axis):ℂ:=![1,-1,1,-1] a
noncomputable def FoldP(j:Tri)(r:ℂ): Module.End ℂ X:= LinearMap.id + r • (J.K j)
noncomputable def Whisp(j:Tri)(r:ℂ): Module.End ℂ X := LinearMap.id + r • ((J.K j).comp (J.K j))
noncomputable def strip (a:Axis):Module.End ℂ X:= (FoldP C J (maybeQ a) (sAlpha a)).comp ((Whisp C J 0 (sAlpha a)).comp (Whisp C J 1 (NativeV.sBeta a)))
lemma spout(a:Axis)(v:X): strip C J a v=
     (let u:=v+ sBeta a • (J.K 1 (J.K 1 v)); let t:=u+sAlpha a • (J.K 0 (J.K 0 u)); t+sAlpha a • J.K (maybeQ a) t):=rfl
structure Spirit(C:Medal W)(J:Drift C X)(P:Tri→X)(e:ℝ):Prop where
     cov: ∀ i j,J.K i (P j)=τc i j • P (roof i j)
     cash:∀ i j,J.J i (P j)=(e:ℂ) • drive i P j
variable (he:p≠f)
noncomputable def haze(a:Axis):X→ₗ[ℂ]ℂ:= (C.T.zz (T 1 2)).comp (J.d a)
lemma vacF (x:X)(hp:∀ k,J.J k x=0)(hk:∀ k,J.K k x=x) : Nation C J (fun i j=> if i=j then x else 0) 0:=by
     refine ⟨fun i j k=> ?_,fun i j k=>?_,fun i j=>by simp [eq_comm] -- error
             ⟩
     · simp only[show roof i j=roof i k ↔ j=k from (Equiv.swap (backK i) (edgeK i)).injective.eq_iff]; split <;> rename_i h; · subst j; rw[hk,smul_smul,show τc _ _*τc _ _=1 from ?_,one_smul]; unfold τc charI; split <;> norm_num
       rw [map_zero,smul_zero,smul_zero]
     rw [zero_smul]; split; exact hp i; exact map_zero _
include ht he
lemma grain (h:Spirit C J V e): haze C J T timeAxis (V 0)=0:=by
     let Y:= J.d timeAxis ∘ V; refine rain C p f T ht Y e (fun i j=> ?_) (fun i j=>?_) he -- inspect order
     · change C.J _ _= _; rw [show C.J i (Y j)= _ from J.twist i (V j),h.cash,map_smul]; apply congr_arg; unfold drive; simp only [map_sum,map_smul]; rfl
     change C.K i (J.d _ _)=_; rw [J.awe,h.cov,map_smul]; rfl
-- bit exercise. generate via python. preserving orientation constraints of candidate.P.B.
end YM.NativeV
#print axioms YM.NativeV.vacF
#print axioms YM.NativeV.grain
