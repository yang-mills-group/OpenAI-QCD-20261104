import YM.Needle.Patch
import YM.Fir.Soot
/-! Authentic position geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open scoped Topology
variable {C:Sequence} (P:Calibration C) {β e:ℝ}(hp:C.Path β e) {n:ℕ}
abbrev Strings (n:ℕ):= Fin n→ Cover
noncomputable abbrev pollF (C:Sequence)(n:ℕ):= Fields.Limit.regulatorPositions (n:=n) C
abbrev FrameI (n:ℕ):= Fin n × Axis
noncomputable def crossing (n:ℕ): Points n ≃L[ℝ] (FrameI n→ℝ):= Points.flatten.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _=>ℝ))
def jade (n:ℕ): Strings n≃(FrameI n→ℤ) where
    toFun f:=fun i=> f i.1 i.2
    invFun f:=fun i b=>f (i,b)
    left_inv _:=rfl
    right_inv _:=rfl
abbrev Exposes {V:Type*}[TopologicalSpace V] (C:Sequence)(φ:ℕ→ℕ) (f:ℕ→Strings n→ V) (x:Points n) (A:V):Prop:=seesF (fun i=>pollF C n (φ i)) f x A
noncomputable abbrev Watch (C:Sequence)(φ:ℕ→ℕ) (x:Points n):=noteF (fun i=>pollF C n (φ i)) x
lemma seen (i:ℕ)(x:Strings n):(crossing n) (pollF C n i x)=imageF (C.S.spacing (C.N i)) (jade n x):=rfl
lemma pivotF (i: Fin n)(b:Axis):crossing n (Points.direction i b)= Pi.single (i,b) 1:=by
     funext j; obtain ⟨p,a⟩:=j; change Points.direction i b p a=_; by_cases h:p=i
     · subst p; by_cases h:a=b; · subst a; simp [Points.direction,basis_eq]
       simp [h,Ne.symm h,Points.direction]
     simp [Points.direction,h,Ne.symm h]
def advanced (p:Fin n)(b:Axis)(y:Strings n):Strings n:=update y p (y p+step b)
lemma brightF (p:Fin n)(b:Axis)(y:Strings n): jade n (advanced p b y)= advanceF (p,b) (jade n y):= by
    funext j; obtain ⟨i,c⟩:=j; by_cases hx:i=p
    · subst i; by_cases he:c=b; · subst c; change update y p (y p+step b) p b= _; unfold advanceF; simp only [update_self]; simp [jade,step]
      change update y p (y p+step b) p c= _; unfold advanceF; rw [update_self, Function.update_of_ne (show (p,c) ≠ ((p,b):FrameI n) from fun h=> he (congr_arg Prod.snd h))]; simp [jade,step,he]
    change update y p (y p+step b) i c= _; unfold advanceF; rw [update_of_ne hx, update_of_ne (show (i,c) ≠ ((p,b):FrameI n) from fun h=>hx (congr_arg Prod.fst h))]; rfl
variable {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
include hp hφ
lemma visions (x:Points n):∃ r:ℕ→ Strings n,Tendsto (fun i=> pollF C n (φ i) (r i)) atTop (𝓝 x):=by
     let a(i):=C.S.spacing (C.N (φ i)); let X:= crossing n; let y:= X x; have hm:Tendsto a atTop (𝓝 0):=(tendsto_nhds_of_tendsto_nhdsWithin hp.physical).comp hφ
     let z(i):=(jade n).symm (markF (a i) y); refine ⟨z,?_⟩; have h:= (X.symm.continuous.tendsto _).comp (visible y (fun _=>space0 _ _) hm); rw [X.symm_apply_apply] at h; exact h.congr' (Eventually.of_forall fun i=> X.injective (by simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]; exact (seen (C:=C) (φ i) (z i)).symm
        ))
lemma alive (x:Points n): (Watch C φ x).NeBot:=by obtain ⟨f,hf⟩:=visions hp hφ x; exact fullness hf
omit hp hφ
lemma incited (x:Points n): Tendsto (fun p:ℕ×Strings n=> (p.1,jade n p.2)) (Watch C φ x) (noteF (fun i=>imageF (C.S.spacing (C.N (φ i)))) ((crossing n) x)):= ride _ _ beyond (((crossing n).continuous.tendsto x).comp (show Tendsto _ (Watch C φ x) _ from approach))
lemma rouses (x:Points n): Tendsto (fun p:ℕ×(FrameI n→ℤ)=> (p.1,(jade n).symm p.2)) (noteF (fun i=>imageF (C.S.spacing (C.N (φ i)))) ((crossing n) x)) (Watch C φ x):=by
     apply ride _ _ beyond; let z:=crossing n; let F:= noteF (fun i=>imageF (C.S.spacing (C.N (φ i)))) (z x); have h:= (z.symm.continuous.tendsto _).comp (show Tendsto _ F _ from approach (v:=fun i=>imageF (C.S.spacing (C.N (φ i)))) (x:=z x)); rw [z.symm_apply_apply] at h; exact h.congr fun p=> z.injective (by rw [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]; exact (seen (φ p.1) ((jade n).symm p.2)).symm
     )
lemma nNote {X:Type*}[TopologicalSpace X](x:Points n)(C:Sequence) (φ:ℕ→ℕ) (f:ℕ→ Strings n→X)(A:X): Exposes C φ f x A ↔ seesF (fun i=> imageF (C.S.spacing (C.N (φ i)))) (fun i=> f i ∘(jade n).symm) ((crossing n) x) A:=⟨fun h=>h.comp (rouses x),fun h=>h.comp (incited x)⟩
variable {x:Points n} (hr:x∈ conf n)
-- local price. need ∀ᶠ watch localSep.
include hp hφ hr
lemma seascape : ∃ r:ℝ,0 < r∧∀ᶠ y in Watch C φ x, localSep C (φ y.1) y.2 r:=by
    let A:= {ij:Fin n×Fin n// ij.1≠ij.2}; let Y(k:A):= dist (x k.val.1) (x k.val.2)
    have hh :∀ᶠ m in 𝓝[>] (0:ℝ),∀ k:A,m < Y k:=eventually_all.mpr fun k=> eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show 0 < Y k from dist_pos.mpr ((show Injective x.ofLp from hr).ne k.property))) -- order
    obtain ⟨m,h,h0⟩:= (hh.and (self_mem_nhdsWithin)).exists
    refine ⟨m/2,half_pos h0,?_⟩
    suffices H:∀ᶠ y in Watch C φ x,∀ k:A, let i:=φ y.1; m/2 ≤ C.S.spacing (C.N i)*↑(separation (wrap _ (y.2 k.val.1)) (wrap (C.S.side (C.R i) (C.N i)) (y.2 k.val.2))) by exact H.mono fun y hy i j ht=> hy ⟨(i,j),ht⟩
    apply eventually_all.mpr; intro k; let F(y:Points n):= dist (y k.val.1) (y k.val.2); have hF:Continuous F:=by unfold F; fun_prop
    have he:= ((hF.tendsto x).comp (show Tendsto _ (Watch C φ x) _ from approach)).eventually (Ioo_mem_nhds (show m<F x from h k) (show F x<Y k+1 from lt_add_one _))
    filter_upwards [he,(hφ.comp beyond).eventually (fullPrice hp m (Y k+1))] with y hy hp; exact hp _ _ hy.1.le hy.2.le
end YM.Massive.Fir
#print axioms YM.Massive.Fir.seascape
