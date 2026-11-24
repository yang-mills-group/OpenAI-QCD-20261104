import YM.VStages.Settlement
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{p:ChangeQ→ChartRatio su}{h s:ℕ→ℕ}
 (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))
open ChangeQ
open Fog.Voyage
variable {P J} {d:ChangeQ→ℕ}(Y:Track P J p d)
namespace Track
lemma tune (i:ℕ):∃ d:ℕ,Y.den i=(3:Side)^d:=by
    induction i with
    | zero=> exact ⟨0,by simp⟩
    | succ i ih=>
       obtain ⟨d,h⟩:= ih; obtain ⟨s,hS⟩:= Y.powers i
       have hp:Y.spacing i=(3:Side)^s:=by exact (Y.length_eq i).trans hS
       exact ⟨d+s,by rw [den,h,hp,pow_add]⟩
lemma tune_head (i:ℕ)(v:ℕ)(x:ℝ):∃ d:ℕ,head (Y.spacing i) v x=(3:Side)^d:=by
    obtain ⟨d,hD⟩:= Y.powers i
    refine ⟨d*rootX (Y.spacing i) v x,?_⟩; change (Y.spacing i)^_ = (3:Side)^_; rw [pow_mul, show Y.spacing i=(3:Side)^d from (Y.length_eq i).trans hD]

theorem den_sound (b i k:ℕ):∃ l:ℕ,b+i≤l ∧ Y.ring ((accord b).n i) k=refrain l :=by
   obtain ⟨l,hL⟩:= tune Y k; change ∃ l:ℕ,b+i≤l ∧ Y.ring (refrain _) k=_
   exact ⟨i+b+l,(by omega),by rw [Track.ring,hL]; simp [refrain,pow_add,mul_assoc]⟩

open PhysicalNext.Repeat Slide -- check
lemma plane (M:ℕ) (v:ℕ→ℕ)(x:ℕ→ℝ): ∀ᶠ k:ℕ in atTop, ∃ S:ℕ→SparkMesh, Track.Align Y (accord k) S M ∧ ∀ i:ℕ, i < M →
  let Q:= head (Y.spacing i) (v i) (x i); (∀ j:Stars,(S i).n j.val=stellar Q j.val)∧∀ j:ℕ,2*style (Y.spacing i) (v i) (x i)< ((S i).n (j+5)).val:=by
    let B i:= head (Y.spacing i) (v i) (x i)
    let t i:=2*style (Y.spacing i) (v i) (x i)
    have hw (i):∀ᶠ k:ℕ in atTop, let A:=ratioM (Y.den i) (accord k);
         t i < (A.n 0).val ∧ bonds (stellar (B i) 4) (A.n 0):=by
        have hp: Tendsto (fun k=>(Y.ring ((accord k).n 0) i).val) atTop atTop:=by
           have he:=ringing Y (accord 0) i
           have heh : Tendsto (fun k=>(Y.ring ((accord 0).n k) i).val) atTop atTop:=tendsto_atTop.mpr (fun b=> by
                filter_upwards [he.eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with j hj; exact le_trans (Nat.le_succ _) hj)
           apply heh.congr'; filter_upwards with j; change (Y.ring (refrain _) _).val=(Y.ring (refrain _) _).val; rw [Nat.zero_add,Nat.add_zero]
        obtain ⟨d,hD⟩:=tune_head Y i (v i) (x i); change B i=_ at hD; filter_upwards [hp.eventually_gt_atTop (t i), eventually_ge_atTop (d+4)] with k hk h
        intro A; refine ⟨hk,?_⟩
        obtain ⟨b,hb,H⟩:=den_sound Y k 0 i
        let a:=b-(d+4); have hy:d+4+a=b:=by unfold a; omega
        refine ⟨3^a,?_, (by decide : Odd (3:ℕ)).pow⟩; change (Y.ring ((accord k).n 0) i).val=_; rw [H,hD,← hy]; simp[refrain,pow_add,stellar]; ac_rfl
    have hf : ∀ᶠ k:ℕ in atTop,∀ i:Fin M,t i < ((ratioM (Y.den i) (accord k)).n 0).val ∧ bonds (stellar (B i) 4) ((ratioM (Y.den i) (accord k)).n 0):= eventually_all.mpr (fun i=> hw i.val)
    filter_upwards [hf] with k hk; let A i:=ratioM (Y.den i) (accord k)
    have he(i:ℕ)(hi:i<M):= crew (B i) (A i) (hk (⟨i,hi⟩: Fin M)).2
    letI :Nonempty SparkMesh:=⟨accord k⟩
    choose! P hv hL using he
    -- result
    refine ⟨P,⟨fun i hi j=>hL i hi j⟩,fun i hi=>⟨hv i hi,fun j=>?_⟩⟩; rw [hL i hi]; exact ((hk ⟨i,hi⟩).1).trans_le (crest_mon (A i) _ _ (by omega))

end Track
end YM.QCD.Acre.Stratum.MarchQ
