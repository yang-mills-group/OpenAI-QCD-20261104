import YM.Tawny.Perla
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
section
variable {R:Type*}[DecidableEq R]
noncomputable def Pe (d:ℕ): Submodule ℂ (Label d) where
 carrier:={x|Quiet x.val ∧ chargeAct x.val=x.val}
 add_mem':=by
     rintro x y ⟨⟨hv,hx⟩,h⟩ ⟨⟨ht,hk⟩,z⟩
     refine ⟨⟨?_,fun p=>?_⟩,?_⟩<;> simp only [Submodule.coe_add,map_add,hv,ht,hx,hk,h,z]
 smul_mem':=by rintro z x ⟨⟨hv,hx⟩,h⟩; refine ⟨⟨?_,fun p=>?_⟩,?_⟩ <;> simp only [Submodule.coe_smul,map_smul,hv,hx,h]
 zero_mem':= ⟨⟨map_zero _,fun _=> map_zero _⟩,map_zero _⟩
noncomputable def stoke (v:Axis×Axis→ Label d)(e:ℂ) (h:∀ i j,v (i,j)∈ Pe d)(hz:∀ (s:Signed)(w:EuPin)(hw:w.Lifts s) (i j:Axis),pinAct w (v (i,j)).val=((signT s i:ℂ)*(signT s j:ℂ)) • (v (s.perm i,s.perm j)).val)(hy:∀ i j,v (j,i)=e • v (i,j)): RawTensor e d:=⟨v,fun ⟨i,j⟩=> (h i j).1,fun ⟨i,j⟩=>(h i j).2,fun s w hp ⟨i,j⟩=>by rw [hz s w hp]; rw [← Complex.ofReal_mul]; rfl, fun ⟨i,j⟩=>hy i j⟩
noncomputable def stick (v:Axis→Label d)(h:∀ i,v i∈Pe d)(hp:∀ (s:Signed)(w:EuPin)(hw:w.Lifts s) i,pinAct w (v i).val=(↑(signT s i):ℂ) • (v (s.perm i)).val): RawVec d:= ⟨v,fun i=>(h i).1,fun i=>(h i).2,hp, fun i=>Eq.symm (one_smul ..)⟩
lemma diagV {v:Axis×Axis→ Label d}(e:ℂ)(h: v∈ RawTensor e d) : (fun P:Axis×Axis=>if P.1=P.2 then v P else 0)∈ RawTensor e d:=by
     have he:= show Meaning _ _ _ _ d v from h; refine ⟨fun ⟨i,j⟩=>?_,fun ⟨i,j⟩=>?_,fun s w hw ⟨i,j⟩=>?_,fun ⟨i,j⟩=>?_⟩
     · split_ifs; exact he.light _; exact ((Pe d).zero_mem).1
     · split_ifs; exact he.coal _; exact ((Pe d).zero_mem).2
     · simp only [acts,s.perm.injective.eq_iff]; split_ifs; exact he.ringo _ _ hw _; simp
     simp only; split_ifs with h k z; exact he.sym _; exfalso; exact k h.symm; exfalso; exact h z.symm; simp
noncomputable def diagT (e)(x:RawTensor e d):RawTensor e d:= ⟨_, diagV e x.property⟩
end
namespace Perla
variable (i j k:Axis) (s:Signed)
local notation "σ" i:arg=> (signT s i:ℂ)
local notation "P"=> RawTensor 1 8
local notation "Z"=> RawVec 10
open StressFlux.Offer
noncomputable def epi:P:= by
     let A:Label 8:=dowry (Labels.unit su (d:=4))
     exact stoke (fun p=>if p.1=p.2 then A else 0) 1 (by
          intro i j; simp only; split
          · refine ⟨plainQ _,?_⟩; change chargeAct (plain _ (1:GPol))=plain _ 1; rw[plainX,map_one]
          exact (Pe _).zero_mem) (by
          intro s w hw i j; simp only [s.perm.injective.eq_iff]; by_cases h:i=j
          · subst j; simp only[↓reduceIte]; change pinAct w (plain _ (1:GPol))= _ • plain _ 1; rw [plainT _ s w hw,map_one, ← Complex.ofReal_mul, UV.sign_sq,Complex.ofReal_one,one_smul]
          simp [h]) (by intro i j; simp [eq_comm])
private lemma stamp_p (i j u v): GG i j u v∈ Pe 8:=⟨plainQ _, colorC ..⟩
private lemma stamp_v (i j u v w): GE i j u v w∈ Pe 10:=⟨plainQ _,colourE ..⟩
noncomputable def spire : P:= stoke (fun p=>∑ i:Axis, GG p.1 i p.2 i) 1 (by intro i j; exact Submodule.sum_mem _ (fun _ _=> stamp_p ..)) (by
    intro s w h i j; change pinAct w (∑ k:Axis,_:Label 8).val= _; rw [AddSubmonoidClass.coe_finsetSum, map_sum, AddSubmonoidClass.coe_finsetSum]; simp_rw [payG _ _ _ _ s w h]; have he k: ((signT s i:ℂ)*(signT s k:ℂ))* ((signT s j:ℂ)*(signT s k:ℂ))=(signT s i:ℂ)*(signT s j:ℂ):=by unfold signT; split <;> split <;> split <;> norm_num
    simp only [he,← smul_sum]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun k=> (GG (s.perm i) k (s.perm j) k).val))) (by
    intro i j; rw [one_smul]; apply Finset.sum_congr rfl; intro x _; exact congr_arg dowry (StressFlux.pair_swap ..))
noncomputable def shadow : P:= diagT 1 spire
noncomputable def eclipse : P:= stoke (fun p=> if p.1=p.2 then ∑ i:Axis,∑ j:Axis, GG i j i j else 0) 1 (by
    intro i j; split; exact Submodule.sum_mem _ (fun i _=> Submodule.sum_mem _ (fun j _=> stamp_p ..)); exact (Pe _).zero_mem) (by
    intro s w h i j; simp only[s.perm.injective.eq_iff]; split <;> rename_i hz
    · subst j; rw [← Complex.ofReal_mul,UV.sign_sq,Complex.ofReal_one,one_smul]; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum,payG _ _ _ _ s w h]; have ht (i j:Axis): ((signT s i:ℂ)*(signT s j:ℂ))* ((signT s i:ℂ)*(signT s j:ℂ))= 1:=by unfold signT; split <;> split <;> norm_num
      have H(j:Axis): (∑ k:Axis,(GG j (s.perm k) j (s.perm k)).val)= ∑ k:Axis,(GG j k j k).val:= Equiv.sum_comp s.perm (fun k=> (GG j k j k).val)
      simp_rw [ht,one_smul,H]; exact Equiv.sum_comp s.perm (fun j=>∑ k:Axis,(GG j k j k).val)
    simp) (by intro i j; simp[eq_comm])
instance (e:ℂ):AddCommGroup (RawTensor e 8):=Submodule.addCommGroup (R:=ℂ) (M:=Axis×Axis→Label 8) (p:=RawTensor e 8)
noncomputable def solid : P:= spire- (1/4:ℂ) • eclipse
lemma epi_at : ((epi).val (i,j)).val= if i=j then UV.unit 8 else 0:=by
    change (ite (i=j) _ (0:Label 8)).val=_; split_ifs <;> rfl
lemma spire_val : spire.val (i,j)=∑ k:Axis,GG i k j k:=rfl
lemma shadow_val:shadow.val (i,j)=if i=j then (∑ k:Axis,GG i k j k) else 0:=rfl
lemma dark : eclipse.val (i,j)= if i=j then ∑ k:Axis, ∑ l:Axis, GG k l k l else 0:=rfl
lemma gauge_val : (solid.val (i,j)).val=UV.gaugeStress i j:=by
    change (spire.val (i,j)-(1/4:ℂ) • eclipse.val (i,j)).val=_; simp only [spire_val,dark,gaugeStress]
    split_ifs <;> simp only [Submodule.coe_sub,Submodule.coe_smul, smul_zero, Submodule.coe_zero,AddSubmonoidClass.coe_finsetSum,fullD]
local notation "τ" =>GE
noncomputable def leapV : Z:= stick (fun i=>∑ b:Axis,GE i b i i b) (fun i=> Submodule.sum_mem _ (fun j _=>stamp_v ..)) (by
   intro s w hp i; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum,payE _ _ _ _ _ s w hp]; have he(j:Axis): (signT s i:ℂ)*(signT s j:ℂ)* (((signT s i:ℂ))* ((signT s i:ℂ)*(signT s j:ℂ)))=(signT s i:ℂ):=by unfold signT; split <;> split <;> norm_num
   simp only [he,← smul_sum]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun k=>(τ (s.perm i) k (s.perm i) (s.perm i) k).val)))
noncomputable def lunar : Z:= stick (fun i=>∑ a:Axis, ∑ b:Axis,GE a b i a b) (fun i=> Submodule.sum_mem _ (fun a _=> Submodule.sum_mem _ (fun b _=> stamp_v ..))) (by
    intro s w hp i; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum,payE _ _ _ _ _ s w hp]; have he(j k:Axis): (signT s j:ℂ)*(signT s k:ℂ)* ((signT s i:ℂ)*((signT s j:ℂ)*(signT s k:ℂ)))=(signT s i:ℂ):=by unfold signT; split <;> split <;> split <;> norm_num
    have ht(j:Axis): (∑ k:Axis, (τ j (s.perm k) (s.perm i) j (s.perm k)).val)=∑ k:Axis,(τ j k (s.perm i) j k).val:= Equiv.sum_comp s.perm (fun k=> (τ j k (s.perm i) j k).val)
    simp only [he, ← smul_sum, ht]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun j=>∑ k: Axis,(τ j k (s.perm i) j k).val)))
noncomputable def eulerV : Z:= stick (fun b=>∑ i:Axis,∑ a:Axis,GE b i a a i) (fun b=>Submodule.sum_mem _ (fun i _=> Submodule.sum_mem _ fun _ _=> stamp_v ..)) (by
    intro s w hp i; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum,payE _ _ _ _ _ s w hp]; have he(j k:Axis): (signT s i:ℂ)*(signT s j:ℂ)* ((signT s k:ℂ)* ((signT s k:ℂ)*(signT s j:ℂ)))=(signT s i:ℂ):=by unfold signT; split <;> split <;> split <;> norm_num
    have ht(j:Axis): (∑ k:Axis,(τ (s.perm i) j (s.perm k) (s.perm k) j).val)=∑ k: Axis,(τ (s.perm i) j k k j).val:= Equiv.sum_comp s.perm (fun k=> (τ (s.perm i) j k k j).val)
    simp only [he,← smul_sum, ht]; exact congr_arg (_ • ·) (Equiv.sum_comp s.perm (fun j=>∑ k:Axis,(τ (s.perm i) j k k j).val)))
end Perla
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Perla.gauge_val
#print axioms YM.Massive.Tawny.Cast.Perla.lunar
