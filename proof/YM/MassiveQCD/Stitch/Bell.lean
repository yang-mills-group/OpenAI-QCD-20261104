import YM.MassiveQCD.Stitch.Seam
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "W"=> Junta c f N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
variable (t)[Fintype D]
open Further.ShellBirth49.Fusing Collide
local notation "Γ"=> Fj D E J
def pawnU (U:Grid f)(s:Finset Γ): Tine c N I:= if P.wish (spent s)= flags t U then X.hue t G s U else 0
omit [Fintype D] in
lemma pawns (U:Grid f)(O:Finset D)(XG:Finset E)(K:Finset J): light Y' (X.pawnU t G U (pin O XG K))=
  carry S (tunnel G (pin O XG K) U) (light X' ((∏ i∈XG,(NormedSpace.exp (X.read t U i)-1))*X.dusk t U K)):=by
  unfold pawnU Tablet.dusk
  split_ifs with he hf hh
  · have hk: flags t U⊆ brimW G P (pin O XG K):=he ▸ (Subset.trans (wish_sub G P _) (native_sub G P _)); have hQ: closeS G P t (pin O XG K) U:=by unfold closeS; rw [he,inter_eq_left.mpr hk]
    unfold hue; rw [if_pos ⟨by rw [pinK]; exact hf.1,hQ⟩]; change carry S _ (light _ (Tablet.made _ _ _ _)) =_; simp [made]
  · rw [pinK] at he; have hp: ¬ P.spare K := fun hz=> hf ⟨hz,he⟩; unfold hue; rw [if_neg (by simp [hp])]; simp only [mul_zero,map_zero]
  · rw [pinK] at he; exact False.elim (he hh.2)
  rw [mul_zero]; simp only [map_zero]

def dyes (U: Grid f)(s: Finset (Finset Γ)): Tine c N I:=if P.wish (spent (s.biUnion id))= flags t U then ∏ i∈s,X.hue t G i U else 0
structure Staid (U: Grid f): Prop where
 exp : Summable (X.read t U)
 bound : Summable (fun i=> ‖NormedSpace.exp (X.read t U i)-1‖)
 plugs : Summable (fun i=> ‖X.plug i U‖)

lemma grand (U:Grid f) (ht:X.Staid t U): HasSum (fun i:Finset Γ=>light _ (X.pawnU t G U i)) (
    carry S ((wipeL G U).comp ((birth (∑ i,G.treats i U)).comp (nearL f c N))) (light X' (Tablet.bluff X t U))):=by
  let Y i:= light _ (X.pawnU t G U i)
  let e₁ i:= ∏ j∈i, (NormedSpace.exp (X.read t U j)-1)
  let V:= NormedSpace.exp (∑' i,X.read t U i)
  have he : Summable fun i=> ‖e₁ i‖:= Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> Finset.norm_prod_le _ _) (summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) ht.bound)
  let q:= X.dusk t U
  have ht' : Summable fun i=> ‖q i‖ := by
    let Q i:=∏ j ∈i, ‖X.plug j U‖
    have hp:Summable Q:=summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) ht.plugs
    refine Summable.of_nonneg_of_le (fun _=> norm_nonneg _) ?_ hp
    intro i; unfold q Tablet.dusk; split; exact Finset.norm_prod_le ..
    rw [norm_zero]; exact prod_nonneg (fun _ _=> norm_nonneg _)
  have hh: HasSum e₁ V:= by
    refine hasSum_of_subseq_of_summable he (p:=atTop) (s:=Finset.powerset) (tendsto_atTop.2 ?_) ?_
    · intro i; filter_upwards [eventually_ge_atTop (i.biUnion id)] with z hz; exact fun j hj=> mem_powerset.mpr ((subset_biUnion_of_mem id hj).trans hz)
    unfold e₁; simp_rw [← flicker]; exact NormedSpace.exp_continuous.continuousAt.tendsto.comp ht.exp.hasSum
  have hk:= toss_big hh ht'.of_norm.hasSum he ht'
  let l O : Patio X'→L[ℂ]Alg Y':=(carry S (tunnel G (pin O (∅:Finset E) (∅:Finset J)) U)).comp (LinearMap.toContinuousLinearMap (light X').toLinearMap)
  have hx (O: Finset D)(X:Finset E)(K:Finset J): axle G U (pin O X K)= axle G U (pin O (∅:Finset E) (∅ : Finset J)):=by simp only [axle,pinC]
  have hP (i): HasSum (fun j:Finset E× Finset J=> (Y ∘ each D E J) (i,j)) (l i (V*∑' j,q j)):=by
    apply (ContinuousLinearMap.hasSum (l i) hk).congr_fun
    intro b; unfold Y; simp only [comp_apply]; change light _ (pawnU _ t _ _ (pin _ _ _))=_; rw [pawns]; unfold tunnel; rw [hx]; rfl
  apply ((each D E J).hasSum_iff).mp -- parse?
  have hw : Summable (Y ∘ each D E J):=((summable_prod_of_nonneg (show 0 ≤ (fun i=> ‖(Y ∘ each D E J) i‖) from fun _=> norm_nonneg _)).2
     ⟨fun i=> (hP i).summable.norm,(hasSum_fintype _).summable⟩).of_norm
  have hp : HasSum (Y ∘ each D E J) (∑ i,l i (V*∑' j,q j)):=by rw [← (hw.hasSum.prod_fiberwise hP).unique (hasSum_fintype _)]; exact hw.hasSum
  refine Eq.subst (motive:=fun x=> HasSum _ x) (show (∑ i,l i (V*∑' j,q j))= _ from ?_) hp
  apply vista (Keys c N); intro s; rw [map_sum,wing]
  let Z:= scrape (Keys f N) s (light _ (X.bluff t U))
  change (∑ _i:Finset D,_)=wipe A B (G.shortP U) (birth (∑ i,G.treats i U) (near A B Z))
  rw [← dripe _ (fun i j=>G.hat U i j) univ,show (univ:Finset D).powerset=univ from by ext; simp,_root_.sum_apply, map_sum]
  refine sum_congr rfl fun i _=>?_; change scrape (Keys c N) s (carry S _ _)=_; rw [wing]; unfold tunnel axle; simp only [pinC]; rfl


def caller (M:Fj D E J→Support c)(U: Grid f)(s: Finset (Finset Γ)):Tine c N I:= if s∈taxes M then X.dyes t G U s else 0
include h in
omit [Fintype D] in
lemma dots (U:Grid f)(ht:X.Wave t q o) {K:Alg Y'}(hh: HasSum (fun i=>light _ (X.pawnU t G U i)) K): HasSum (fun s=>light _ (X.caller t G M U s)) K:=by
  let z i:= parts M i; have he : Injective z :=fun i j he=>by rw [← recombine M i, ←recombine M j,show parts M i=parts M j from he]
  have hi : taxes M=Set.range z:=by
    ext k; constructor
    · intro hv; change _ ∧_ at hv; exact ⟨ _,uncluttered M k hv.1 hv.2⟩
    rintro ⟨i,rfl⟩; exact ⟨Collide.separate M i,fun j hj=>(living M hj).2⟩
  apply (he.hasSum_iff _).1; rotate_left; · intro i hx; unfold caller; rw [hi,if_neg hx,map_zero]
  refine hh.congr_fun (fun i=>?_); change light _ (X.caller t G M U (z i))=_
  unfold caller; rw [hi, if_pos (Set.mem_range_self _)]; apply congr_arg; unfold dyes pawnU
  rw [← hue_product X G ht h _ U (Collide.separate M i) (erases M i),show (z i).biUnion id=i from recombine M i]

include h
lemma cashS (WS:Grid f)(hp:X.Wave t q o)(hh:X.Staid t WS): Summable (X.caller t G M WS):=by
   have ht:= dots X t G h WS hp (grand X t G WS hh); exact Summable.of_norm (show Summable fun i=> ‖light Y' (X.caller t G M WS i)‖ from ht.summable.norm) -- fintype D implicit?

end Tablet
end YM.MassiveQCD.Stitch
/-! # Joint graded rolls on the front.

 Actual new spin read at every marker monomial, remaining Gaussian. Push
 integral operates only on ACTUAL Keys, not in storage alphabet.
-/
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj QCD.Kit
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
variable (t)[Fintype D]
include hw h
lemma grain_step (Q:Grid f→Matrix B A ℂ) (D₀:Grid f→Matrix A A ℂ) (W:Grid f)(hv:G.Cast Q (fun U=> D₀ U+(Q U)ᴴ*Q U)) (he:IsUnit (D₀ W+(Q W)ᴴ*Q W).det) (hs:X.Staid t W) (s:Finset S):
    let H:=D₀ W+(Q W)ᴴ*Q W; let q:= X.caller t G M W; sheath 1 (Q W) (gauss (D₀ W) * scrape (Keys f N) s (light _ (X.bluff t W)))= H.det • (scrape (Keys c N) s (light Y' (∑' i,q i))*gauss (1-Q W*H⁻¹*(Q W)ᴴ)):=by
      have hg:= dots X t G h W hw (grand X t G W hs); have hM:= (cashS X t G h W hw hs).hasSum.map (light _) (lightC _); intro H q; rw [G.drum _ _ hv _ _ he, ← hg.unique (show HasSum (fun i=> light _ (q i)) _ from hM),wing]; rfl
end Tablet
end YM.MassiveQCD.Stitch
