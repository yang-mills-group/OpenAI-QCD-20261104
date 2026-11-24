import YM.QCD.Cove.Hem
/-! # high fermion transformation. Pure tickets don't alter it at U. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{f c: Side}{S: Ratio c f}{E D J: Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "I"=> Fj D E J
variable (g:Send S F D) (P:Rise f F E J)(t:ℝ)
variable {M:Fj D E J→ Support c} (h: Count g P M)  [Fintype D]

def pawnU (U:Grid f)(s:Finset I): EvenA c F:= if P.wish (spent s)= flags t U then hue g P t s U else 0
lemma pawns (U:Grid f)(O:Finset D)(X:Finset E)(K:Finset J): light (Keys c F) (pawnU g P t U (pin O X K))=
  wipe A B (g.shortP U) (axle g U (pin O X K) (near A B (light _ ((∏ i∈X,(NormedSpace.exp (P.reading t U i)-1))*P.dusk t U K)))):=by
  unfold pawnU Rise.dusk
  split_ifs with he hf hh
  · have hk: flags t U⊆ brimW g P (pin O X K):=he ▸ (Subset.trans (wish_sub g P _) (native_sub g P _)); have hQ: closeS g P t (pin O X K) U:=by unfold closeS; rw [he,inter_eq_left.mpr hk]
    unfold hue; rw [if_pos ⟨by rw [pinK]; exact hf.1,hQ⟩, dipping]; simp [made]
  · rw [pinK] at he; have hp: ¬ P.spare K := fun hz=> hf ⟨hz,he⟩; unfold hue; rw [if_neg (by simp [hp])]; simp only [mul_zero,map_zero]
  · rw [pinK] at he; exact False.elim (he hh.2)
  rw [mul_zero]; simp only [map_zero]

def taxes (M:Fj D E J→Support c) : Set (Finset (Finset I)) := {p| (p:Set (Finset I)).PairwiseDisjoint (fun s => s.biUnion M)∧∀ i∈p, spark M i}
def dyes (U: Grid f)(s: Finset (Finset I)): EvenA c F:=if P.wish (spent (s.biUnion id))= flags t U then ∏ i∈s,hue g P t i U else 0
structure Placid (U: Grid f): Prop where
 exp : Summable (P.reading t U)
 bound : Summable (fun i=> ‖NormedSpace.exp (P.reading t U i)-1‖)
 plugs : Summable (fun i=> ‖P.plug i U‖)
open Filter
lemma toss_big {κ ρ:Type*}{V:Type*} [NormedCommRing V][CompleteSpace V]{f: κ→V}{p:ρ→V}{a b:V}(h : HasSum f a)(hh: HasSum p b)(he: Summable (fun i=> ‖f i‖))(hx: Summable fun i=> ‖p i‖) : HasSum (fun i:κ×ρ=> f i.1*p i.2) (a*b):=by
    apply h.mul hh
    let T (i:κ×ρ):=‖f i.1‖*‖p i.2‖
    have hh : Summable T:=by
      apply (summable_prod_of_nonneg (show 0 ≤ T from fun i=> mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      refine ⟨fun i=>?_ ,?_⟩
      · exact hx.mul_left ‖f i‖
      change Summable (fun i=> ∑' j, ‖f i‖*‖p j‖); simp_rw [tsum_mul_left]; exact he.mul_right _
    exact Summable.of_norm_bounded hh (fun i=> norm_mul_le (f i.1) (p i.2))

lemma grand (U:Grid f) (ht:Placid P t U): HasSum (fun i:Finset I=>light _ (pawnU g P t U i)) (
    wipe A B (g.shortP U) (birth (∑ i,g.treats i U) (near A B (P.bluff t U)))):=by
  let Y i:= light _ (pawnU g P t U i)
  let e₁ i:= ∏ j∈i, (NormedSpace.exp (P.reading t U j)-1)
  let V:= NormedSpace.exp (P.hyp t U)
  have he : Summable fun i=> ‖e₁ i‖:= Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> Finset.norm_prod_le _ _) (summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) ht.bound)
  let q:= P.dusk t U
  have ht' : Summable fun i=> ‖q i‖ := by
    let Q i:=∏ j ∈i, ‖P.plug j U‖
    have hp:Summable Q:=summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) ht.plugs
    refine Summable.of_nonneg_of_le (fun _=> norm_nonneg _) ?_ hp
    intro i; unfold q Rise.dusk; split; exact Finset.norm_prod_le ..
    rw [norm_zero]; exact prod_nonneg (fun _ _=> norm_nonneg _)
  have hh: HasSum e₁ V:= by
    refine hasSum_of_subseq_of_summable he (p:=atTop) (s:=Finset.powerset) (tendsto_atTop.2 ?_) ?_
    · intro i; filter_upwards [eventually_ge_atTop (i.biUnion id)] with z hz; exact fun j hj=> mem_powerset.mpr ((subset_biUnion_of_mem id hj).trans hz)
    unfold e₁; simp_rw [← flicker]; exact NormedSpace.exp_continuous.continuousAt.tendsto.comp ht.exp.hasSum
  have hk:= toss_big hh ht'.of_norm.hasSum he ht'
  let l O : Patio (Keys _ F) →L[ℂ]Fields c F := LinearMap.toContinuousLinearMap ((wipe A B (g.shortP U)).toLinearMap.comp ((axle g U (pin O (∅:Finset E) (∅ : Finset J))).toLinearMap.comp ((near A B).toLinearMap.comp (light _).toLinearMap)))
  have hx (O: Finset D)(X:Finset E)(K:Finset J): axle g U (pin O X K)= axle g U (pin O (∅:Finset E) (∅ : Finset J)):=by simp only [axle,pinC]
  have hP (i): HasSum (fun j:Finset E× Finset J=> (Y ∘ each D E J) (i,j)) (l i (V*∑' j,q j)):=by
    apply (ContinuousLinearMap.hasSum (l i) hk).congr_fun
    intro b; unfold Y; simp only [comp_apply]; change light _ (pawnU _ _ t _ (pin _ _ _))=_; rw [pawns,hx]; rfl
  apply ((each D E J).hasSum_iff).mp -- parse?
  have hw : Summable (Y ∘ each D E J):=((summable_prod_of_nonneg (show 0 ≤ (fun i=> ‖(Y ∘ each D E J) i‖) from fun _=> norm_nonneg _)).2
     ⟨fun i=> (hP i).summable.norm,(hasSum_fintype _).summable⟩).of_norm
  have hp : HasSum (Y ∘ each D E J) (∑ i,l i (V*∑' j,q j)):=by rw [← (hw.hasSum.prod_fiberwise hP).unique (hasSum_fintype _)]; exact hw.hasSum
  rw [← dripe _ (fun i j=>g.hat U i j) univ,show (univ:Finset D).powerset=univ from by ext; simp, ContinuousLinearMap.sum_apply,map_sum]; convert! hp using 1; apply sum_congr rfl; intro i _; dsimp only [l,axle]; simp only [pinC]; rfl

def caller (M:Fj D E J→Support c)(U: Grid f)(s: Finset (Finset I)):EvenA c F:= if s∈taxes M then dyes g P t U s else 0
include h in
lemma dots (U:Grid f)(ht:P.Wave t) {K:Fields c F}(hh: HasSum (fun i=>light _ (pawnU g P t U i)) K): HasSum (fun s=>light _ (caller g P t M U s)) K:=by
  let z i:= parts M i; have he : Injective z :=fun i j he=>by rw [← recombine M i, ←recombine M j,show parts M i=parts M j from he]
  have hi : taxes M=Set.range z:=by
    ext k; constructor
    · intro hv; change _ ∧_ at hv; exact ⟨ _,uncluttered M k hv.1 hv.2⟩
    rintro ⟨i,rfl⟩; exact ⟨separate M i,fun j hj=>(living M hj).2⟩
  apply (he.hasSum_iff _).1; rotate_left; · intro i hx; unfold caller; rw [hi,if_neg hx,map_zero]
  refine hh.congr_fun (fun i=>?_); change light _ (caller g P t M U (z i))=_
  unfold caller; rw [hi, if_pos (Set.mem_range_self _)]; apply congr_arg; unfold dyes pawnU
  rw [← hue_product g P t h _ U ht (separate M i) (erases M i),show (z i).biUnion id=i from recombine M i]

include h
lemma cashS (W:Grid f)(hp:P.Wave t)(hh:Placid P t W): Summable (caller g P t M W):=by
   have ht:= dots g P t h W hp (grand g P t W hh); exact Summable.of_norm (show Summable fun i=> ‖light (Keys c F) (caller g P t M W i)‖ from ht.summable.norm) -- fintype D implicit?
lemma push_fermi (Q:Grid f→Matrix B A ℂ) (D₀:Grid f→Matrix A A ℂ) (W:Grid f)(hp:P.Wave t)(hv:g.Cast Q (fun U=> D₀ U+(Q U)ᴴ*Q U)) (he:IsUnit (D₀ W+(Q W)ᴴ*Q W).det) (hh: Placid P t W):
   let H:=D₀ W+(Q W)ᴴ*Q W
   sheath 1 (Q W) (gauss (D₀ W)*P.bluff t W)= H.det • (light _ (∑' i, caller g P t M W i)*gauss (1-Q W*H⁻¹*(Q W)ᴴ)):= by
     have hg:= dots g P t h W hp (grand g P t W hh)
     have hM:= (cashS g P t h W hp hh).hasSum.map (light _) (lightC _)
     rw [g.drum _ _ hv _ _ he, hg.unique (show HasSum (fun i=> light _ (caller _ _ _ _ _ i)) _ from hM)]
end YM.QCD.Cove
