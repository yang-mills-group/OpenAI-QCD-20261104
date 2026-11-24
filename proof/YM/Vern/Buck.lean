import YM.Vern.Vines
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.NativeV
open Function Set Filter Analysis
open scoped Topology BigOperators Classical
open Lobo Vern Finset
variable {W X:Type}[AddCommGroup W][Module ℂ W][AddCommGroup X][Module ℂ X]
variable (C:Medal W)(J:Drift C X)(p f:ℝ)(T:Tri→Tri→W)(ht:Olive C p f T)
structure Spire (P:Axis→Axis→X) :Prop where
  acts:∀ (i:Tri)(a b:Axis), J.K i (P a b)=(↑(Massive.UV.signT (Cup i) a*Massive.UV.signT (Cup i) b:ℝ):ℂ) • P ((Cup i).perm a) ((Cup i).perm b)
  sym: ∀ i j,P i j=P j i
variable (S:Axis→Axis→X)(h:Spire C J S)
-- automatically apply ℤ-coefficient.FIN bookkeeping. Proved strip unnormalized =8.
include h

lemma fixed0 : strip C J 0 (S 0 0)= (8:ℂ) • S 0 0:=by
     have K0:J.K 0 (J.K 0 (S 0 0))=(1:ℂ) • S 0 0:=by
           have h₁: J.K 0 (S 0 0)= (1:ℂ) • S 0 0:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 0 (S 0 0)= (1:ℂ) • S 0 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have K1:J.K 1 (J.K 1 (S 0 0))=(1:ℂ) • S 0 0:=by
           have h₁: J.K 1 (S 0 0)= (1:ℂ) • S 2 2:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 1 (S 2 2)= (1:ℂ) • S 0 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have M:J.K 0 (S 0 0)= (1:ℂ) • S 0 0:=by
          have hx:J.K 0 (S 0 0)= (1:ℂ) • S 0 0:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
          exact hx
     unfold strip; simp only [LinearMap.comp_apply]; let x:=S 0 0
     have H:Whisp C J 1 (NativeV.sBeta 0) x= (2:ℂ) • x:=by
             change x+ (1:ℂ) • J.K 1 (J.K 1 (S 0 0)) = _; rw[K1]; unfold x; module
     have G:Whisp C J 0 (sAlpha 0) x=(2:ℂ) • x:=by
             change x+ (1:ℂ) • J.K 0 (J.K 0 (S 0 0))= _; rw[K0]; unfold x; module
     have K:FoldP C J (maybeQ 0) (sAlpha 0) x=(2:ℂ) • x:=by change x+ (1:ℂ) • J.K 0 (S 0 0)=_; rw [M]; unfold x; module
     change FoldP C J _ _ (Whisp C J _ _ (Whisp C J 1 (NativeV.sBeta 0) x))=_; rw [H,map_smul,G,map_smul,map_smul,K]; unfold x; module
lemma fixed1 : strip C J 1 (S 1 0)= (8:ℂ) • S 1 0:=by
     have K0:J.K 0 (J.K 0 (S 1 0))=(-1:ℂ) • S 1 0:=by
           have h₁: J.K 0 (S 1 0)= (1:ℂ) • S 2 0:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 0 (S 2 0)= (-1:ℂ) • S 1 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have K1:J.K 1 (J.K 1 (S 1 0))=(-1:ℂ) • S 1 0:=by
           have h₁: J.K 1 (S 1 0)= (-1:ℂ) • S 1 2:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 1 (S 1 2)= (1:ℂ) • S 1 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have M:J.K 2 (S 1 0)= (-1:ℂ) • S 1 0:=by
          have hx:J.K 2 (S 1 0)= (-1:ℂ) • S 0 1:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
          exact hx.trans (congr_arg (fun (v:X)=> (-1:ℂ) • v) (h.sym ..))
     unfold strip; simp only [LinearMap.comp_apply]; let x:=S 1 0
     have H:Whisp C J 1 (NativeV.sBeta 1) x= (2:ℂ) • x:=by
             change x+ (-1:ℂ) • J.K 1 (J.K 1 (S 1 0)) = _; rw[K1]; unfold x; module
     have G:Whisp C J 0 (sAlpha 1) x=(2:ℂ) • x:=by
             change x+ (-1:ℂ) • J.K 0 (J.K 0 (S 1 0))= _; rw[K0]; unfold x; module
     have K:FoldP C J (maybeQ 1) (sAlpha 1) x=(2:ℂ) • x:=by change x+ (-1:ℂ) • J.K 2 (S 1 0)=_; rw [M]; unfold x; module
     change FoldP C J _ _ (Whisp C J _ _ (Whisp C J 1 (NativeV.sBeta 1) x))=_; rw [H,map_smul,G,map_smul,map_smul,K]; unfold x; module
lemma fixed2 : strip C J 2 (S 2 0)= (8:ℂ) • S 2 0:=by
     have K0:J.K 0 (J.K 0 (S 2 0))=(-1:ℂ) • S 2 0:=by
           have h₁: J.K 0 (S 2 0)= (-1:ℂ) • S 1 0:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 0 (S 1 0)= (1:ℂ) • S 2 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have K1:J.K 1 (J.K 1 (S 2 0))=(1:ℂ) • S 2 0:=by
           have h₁: J.K 1 (S 2 0)= (-1:ℂ) • S 0 2:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 1 (S 0 2)= (-1:ℂ) • S 2 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have M:J.K 1 (S 2 0)= (-1:ℂ) • S 2 0:=by
          have hx:J.K 1 (S 2 0)= (-1:ℂ) • S 0 2:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
          exact hx.trans (congr_arg (fun (v:X)=> (-1:ℂ) • v) (h.sym ..))
     unfold strip; simp only [LinearMap.comp_apply]; let x:=S 2 0
     have H:Whisp C J 1 (NativeV.sBeta 2) x= (2:ℂ) • x:=by
             change x+ (1:ℂ) • J.K 1 (J.K 1 (S 2 0)) = _; rw[K1]; unfold x; module
     have G:Whisp C J 0 (sAlpha 2) x=(2:ℂ) • x:=by
             change x+ (-1:ℂ) • J.K 0 (J.K 0 (S 2 0))= _; rw[K0]; unfold x; module
     have K:FoldP C J (maybeQ 2) (sAlpha 2) x=(2:ℂ) • x:=by change x+ (-1:ℂ) • J.K 1 (S 2 0)=_; rw [M]; unfold x; module
     change FoldP C J _ _ (Whisp C J _ _ (Whisp C J 1 (NativeV.sBeta 2) x))=_; rw [H,map_smul,G,map_smul,map_smul,K]; unfold x; module
lemma fixed3 : strip C J 3 (S 3 0)= (8:ℂ) • S 3 0:=by
     have K0:J.K 0 (J.K 0 (S 3 0))=(1:ℂ) • S 3 0:=by
           have h₁: J.K 0 (S 3 0)= (1:ℂ) • S 3 0:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 0 (S 3 0)= (1:ℂ) • S 3 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have K1:J.K 1 (J.K 1 (S 3 0))=(-1:ℂ) • S 3 0:=by
           have h₁: J.K 1 (S 3 0)= (-1:ℂ) • S 3 2:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ) (z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           have h₂:J.K 1 (S 3 2)= (1:ℂ) • S 3 0:=by rw[h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
           rw[h₁,map_smul,h₂]; module
     have M:J.K 0 (S 3 0)= (1:ℂ) • S 3 0:=by
          have hx:J.K 0 (S 3 0)= (1:ℂ) • S 3 0:=by rw [h.acts]; exact congr_arg₂ (fun (v:ℂ)(z:X)=>v • z) (by unfold Massive.UV.signT Cup Maxwell.Free.Corners.quarter; simp +decide [lieu]) rfl
          exact hx
     unfold strip; simp only [LinearMap.comp_apply]; let x:=S 3 0
     have H:Whisp C J 1 (NativeV.sBeta 3) x= (2:ℂ) • x:=by
             change x+ (-1:ℂ) • J.K 1 (J.K 1 (S 3 0)) = _; rw[K1]; unfold x; module
     have G:Whisp C J 0 (sAlpha 3) x=(2:ℂ) • x:=by
             change x+ (1:ℂ) • J.K 0 (J.K 0 (S 3 0))= _; rw[K0]; unfold x; module
     have K:FoldP C J (maybeQ 3) (sAlpha 3) x=(2:ℂ) • x:=by change x+ (1:ℂ) • J.K 0 (S 3 0)=_; rw [M]; unfold x; module
     change FoldP C J _ _ (Whisp C J _ _ (Whisp C J 1 (NativeV.sBeta 3) x))=_; rw [H,map_smul,G,map_smul,map_smul,K]; unfold x; module
lemma fixP (a:Axis): strip C J a (S a 0)=(8:ℂ) • S a 0:=by
    fin_cases a <;> first | exact fixed0 C J S h | exact fixed1 C J S h| exact fixed2 C J S h| exact fixed3 C J S h
end YM.NativeV
#print axioms YM.NativeV.fixP
