import YM.Lobo.Mallet
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Lobo
variable (E : Type)[AddCommGroup E][Module ℂ E]
local notation "c" t:arg => (Real.cos t:ℂ)
local notation "s" t:arg => (Real.sin t:ℂ)
noncomputable def Uno :Submodule ℂ (ℝ→E) where
     carrier:={f|∃ A B C:E,∀ t,f t=A+c t • B+s t • C}
     add_mem':=by
            intro f g ⟨A,B,C,h⟩ ⟨F,G,H,k⟩; refine ⟨A+F,B+G,C+H,fun t=>?_⟩; rw [Pi.add_apply,h,k,smul_add,smul_add]; abel
     zero_mem':=⟨0,0,0,by simp⟩
     smul_mem':=by
            intro z f ⟨A,B,C,h⟩; refine ⟨z • A,z • B,z • C,fun t=>?_⟩; rw[Pi.smul_apply,h,smul_add,smul_add,smul_comm z,smul_comm z]
noncomputable def Tres :Submodule ℂ (ℝ→E) where
     carrier:={f|∃ v∈Uno E,∃ A B:E,∀ t,f t= v t + c (t+t) • A + s (t+t) • B}
     add_mem':=by
         intro f g ⟨v,h,A,B,hf⟩ ⟨w,k,F,G,hg⟩; refine ⟨v+w,Submodule.add_mem _ h k,A+F,B+G,fun t=>?_⟩; rw [Pi.add_apply,Pi.add_apply,hf,hg,smul_add,smul_add]; abel
     zero_mem':=⟨0,Submodule.zero_mem _,0,0,by simp⟩
     smul_mem':=by
         intro z f ⟨v,h,A,B,hf⟩; refine ⟨z • v,Submodule.smul_mem _ _ h,z • A,z • B,fun t=>?_⟩; rw[Pi.smul_apply,hf,Pi.smul_apply,smul_add,smul_add,smul_comm z,smul_comm z]
lemma upt : Uno E ≤ Tres E:=fun f h=>⟨f,h,0,0,fun t=>by rw[smul_zero,smul_zero,add_zero,add_zero]⟩
variable {E} (A:E) {f:ℝ→E} (hs:f ∈ Uno E)
local notation "q"=> Real.pi/2
lemma univoc : (fun _=>A)∈Uno E:=⟨A,0,0,by simp⟩
include hs
lemma uni_map {Y:Type}[AddCommGroup Y][Module ℂ Y](P:E→ₗ[ℂ]Y): (fun t=>P (f t))∈ Uno Y:=by obtain ⟨A,B,C,h⟩:=hs; exact ⟨P A,P B,P C,fun t=>by dsimp only; rw[h,map_add,map_add,map_smul,map_smul]⟩
lemma echoes (t:ℝ) : f t-f (t+q)+ f (t+Real.pi) - f (t+Real.pi+q)=0:=by
     obtain ⟨A,B,C,h⟩:=hs; rw [h,h,h,h, Real.cos_add_pi_div_two, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,Real.sin_add_pi_div_two]; simp only[Real.cos_add_pi, Real.sin_add_pi,Complex.ofReal_neg,neg_neg,neg_smul]; abel
lemma known (g:ℝ→E)(hg:g∈Uno E)(h:f 0=g 0)(hp:f (Real.pi/2)=g (Real.pi/2))(hk:f Real.pi=g Real.pi):f=g:=by
     let F:=f-g; obtain ⟨A,B,C,hF⟩:=Submodule.sub_mem (Uno E) hs hg; have he:F 0=0:=sub_eq_zero.mpr h; have ht:F q=0:=sub_eq_zero.mpr hp; have hx:F Real.pi=0:=sub_eq_zero.mpr hk
     change ∀ t:ℝ, F t=A+c t • B+s t • C at hF
     rw [hF] at he ht hx
     simp at he ht hx -- may simplify into hF?
     have hB : A=B:=by rw[← sub_eq_add_neg] at hx; exact sub_eq_zero.mp hx
     have hv:A=0:=by rw [← hB] at he; rw[←two_smul ℂ] at he; simpa using he
     have hz:C=0:=by simpa [hv] using ht
     exact funext fun x=>sub_eq_zero.mp (show F x=0 from by rw [hF,← hB,hv,hz]; simp)
omit hs
lemma gleams {g:ℝ→E}(hg:g∈Tres E)(h:∀ t:ℝ,g t-g (t+q)+g (t+Real.pi)- g (t+Real.pi+q)=0):g∈Uno E:=by
      obtain ⟨f,hf,A,B,ht⟩:= hg; suffices g=f by rwa [this]
      funext t; specialize h t; have hZ:=h; have he:=echoes hf t
      let p:= Real.pi; have hu(r:ℝ): c ((r+q)+(r+q)) = - c (r+r) ∧ s ((r+q)+(r+q)) = - s (r+r):=by
             rw [show (r+q)+(r+q)=(r+r)+Real.pi from by ring]; simp
      have hv(r:ℝ): c ((r+p)+(r+p)) = c (r+r) ∧ s ((r+p)+(r+p)) = s (r+r):=by
             unfold p; rw [show r+Real.pi+(r+Real.pi)= r+r+Real.pi+Real.pi from by ring]; simp
      have hz : c (t+t) • A+s (t+t) • B=0:=by
             apply smul_right_injective E (show (4:ℂ)≠0 from by norm_num); change (4:ℂ) • _=(4:ℂ) • 0; rw[smul_zero, show (4:ℂ)=(1+1)+(1+1) from by norm_num]; simp only [add_smul,one_smul]
             set Z:= c (t+t) • A; set W:=s (t+t) • B; rw [show (Z+W+(Z+W))+(Z+W+(Z+W)) = _ from (?_ : Z+W+(Z+W)+(Z+W+(Z+W))=(g t-g (t+q)+g (t+Real.pi)-g (t+Real.pi+q))-(f t-f (t+q)+f (t+Real.pi)-f (t+Real.pi+q))), hZ,he,sub_self]
             rw[ht,ht,ht,ht,(hu t).1,(hu t).2,(hu (t+Real.pi)).1,(hu (t+Real.pi)).2]; unfold p at hv; simp only [(hv t).1,(hv t).2,neg_smul]; unfold Z W; abel
      rw [ht,add_assoc,hz,add_zero]
-- multiplication by cos and sin
lemma pole (t:ℝ) : c (t+t)=2*(c t*c t)-1∧ c (t+t)=1-2*(s t*s t)∧ s (t+t)=2*(s t*c t):=by
      have ht:c t*c t+s t*s t=1:=by rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_add,← pow_two,←pow_two, Real.cos_sq_add_sin_sq, Complex.ofReal_one]
      simp only [Real.cos_add, Real.sin_add, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]; constructor; · linear_combination - ht -- sign
      constructor; · linear_combination ht
      ring
include hs
lemma aspens : (fun t:ℝ=> c t • f t)∈Tres E∧ (fun t:ℝ=> s t • f t)∈Tres E:=by
      obtain ⟨A,B,C,h⟩:=hs
      let hB:=(1/2:ℂ) • B; let hC:=(1/2:ℂ) • C
      constructor
      · refine ⟨(fun t=> hB+c t • A),⟨hB,A,0,fun t=> by simp⟩,hB,hC,fun t=>?_⟩; dsimp only; rw [h,(pole t).1,(pole t).2.2]; unfold hB hC; module
      refine ⟨(fun t=> hC+s t • A),⟨hC,0,A,fun t=>by simp⟩,-hC,hB,fun t=>?_⟩; dsimp only; rw[h,(pole t).2.1,(pole t).2.2]; unfold hC hB; module
omit hs
variable (k i j:Tri)
lemma chord (f:Tri→ E) : (fun t=> wing k t f i)∈Uno E:=by
      rcases stateU k i with hi|hi|hi; · rw [hi, show (fun t=>wing k t f k)=(fun _=> f k) from funext fun t=> (wingsI k t f).1]; exact univoc _
      · rw[hi]; exact ⟨0, f (edgeK k), f (backK k),fun t=>by rw [zero_add]; exact (wingsI k t f).2.1⟩
      rw [hi]; exact ⟨0,f (backK k),- f (edgeK k),fun t=>by rw [zero_add, smul_neg,← sub_eq_add_neg]; exact (wingsI k t f).2.2⟩
lemma anthem (f:Tri→ℝ→E)(h:∀ i:Tri,f i∈ Uno E) : (fun t=> wing k t (fun j=> f j t) i)∈Tres E:=by
      rcases stateU k i with hi|hi|hi
      · rw [hi,funext (show ∀ t:ℝ,wing k t (fun i=> f i t) k=f k t from fun _=> (wingsI ..).1)]; exact upt E (h _)
      · let X :ℝ→E := fun t=> c t • f (edgeK k) t; let Y :ℝ→ E:= fun t=> s t • f (backK k) t; rw [hi,funext (show ∀ t:ℝ,wing k t (fun i=> f i t) (edgeK k)=(X+Y) t from fun t=> (wingsI k t (fun i=> f i t)).2.1)]; exact Submodule.add_mem _ (aspens (h _)).1 (aspens (h _)).2
      let X: ℝ→ E:= fun t=> c t • f (backK k) t; let Y:ℝ→ E:= fun t=> s t • f (edgeK k) t; rw[hi, funext (show ∀ t:ℝ,wing k t (fun i=> f i t) (backK k)=(X-Y) t from fun t=> (wingsI k t (fun i=>f i t)).2.2)]; exact Submodule.sub_mem _ (aspens (h _)).1 (aspens (h _)).2
end YM.Sunda
#print axioms YM.Sunda.known
#print axioms YM.Sunda.anthem
#print axioms YM.Sunda.echoes
#print axioms YM.Sunda.gleams
#print axioms YM.Sunda.chord
