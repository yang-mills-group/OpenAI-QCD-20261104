import YM.QCD.Door.Stoke
/-! # pro tempore equivariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Eyrie Sparks Fj
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{F:ℕ}
variable {Z:Ratio c f}{U V : Grid f}{E D J:Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
variable {O:Send Z F D}{P:Rise f F E J}{p:OrbitG (Modes f F⊕Modes c F)}{r:OrbitG (Modes f F)}{q:OrbitG (Modes c F)}{s:Equiv.Perm (Site f)}{e:Equiv.Perm E}{j:Equiv.Perm J}{d:Equiv.Perm D}{t:ℝ}
variable (hv:Usher Z O U V p r q s d)(hp: Parade U V r P s e j t)

open Fj
abbrev sail (d:Equiv.Perm D)(e:Equiv.Perm E)(j:Equiv.Perm J): Equiv.Perm (Fj D E J) := Equiv.sumCongr d (Equiv.sumCongr e j)
variable [Countable E][Countable J]
lemma cutRead (hv:Parade U V r P s e j t) (i:E): r.passL (P.reading t U i)= P.reading t V (e i):=by
 have he: Healthy t (P.row i).support U↔Healthy t (P.row (e i)).support V:=by unfold Healthy; rw [hv.poseE,← hv.flags, Finset.disjoint_image s.injective]
 rw [P.hype,P.hype]; by_cases h:Healthy t (P.row i).support U; · rw [if_pos h,if_pos (he.1 h),hv.ease]
 rw [if_neg h, if_neg (mt he.2 h),map_zero]

lemma parts_map (d:Equiv.Perm D)(e:Equiv.Perm E)(j:Equiv.Perm J)(T:Finset (Fj D E J)):
    let W:=T.image (sail d e j); ops W=(ops T).image d ∧ leftE W=(leftE T).image e∧ spent W=(spent T).image j:=by
    intro W; let φ:= sail d e j; constructor
    · ext i; obtain ⟨i,rfl⟩:=d.surjective i
      rw [Finset.mem_image]; simp only [EmbeddingLike.apply_eq_iff_eq,exists_eq_right]
      change d i ∈ (ops (T.image φ)) ↔ i ∈ _; simp [ops, show Sum.inl (d i)= φ (.inl i) from rfl]
    constructor
    · ext i; obtain ⟨i,rfl⟩:=e.surjective i
      simp only [mem_image, EmbeddingLike.apply_eq_iff_eq,exists_eq_right]; -- goal Fmap image LHS?
      unfold leftE; change e i ∈ (T.image φ).toRight.toLeft ↔ _; simp only [mem_toLeft,mem_toRight]; rw [show Sum.inr (.inl (e i))=φ (.inr (.inl i)) from rfl]; simp
    ext i; obtain ⟨i,rfl⟩:=j.surjective i
    have he : Sum.inr (Sum.inr (j i))=φ (.inr (.inr i)):=rfl
    rw [mem_image]; unfold W spent; simp [show Sum.inr (Sum.inr (j i))=φ (.inr (.inr i)) from rfl,← show φ=sail d e j from rfl]; -- check

lemma seal_ax (hv:Usher Z O U V p r q s d)(T: Finset (Fj D E J))(e j x): p.φ (axle O U T x)= axle O V (T.image (sail d e j)) (p.φ x):=by
    let X (G:Finset (Fj D E J)):= G.image (sail d e j); unfold Cove.axle
    have he:= (parts_map d e j T).1
    rw [noncommProd_congr he (fun _ _=> rfl)]; -- induct on opsT avoid he dependent
    have H (b: Finset D)(h h'): p.φ ((b.noncommProd (fun i=> bucks O i U) h) x)= ((b.image d).noncommProd (fun i=>bucks O i V) h') (p.φ x):=by
      induction b using Finset.induction_on with
      | empty=> simp only [Finset.image_empty,noncommProd_empty, ContinuousLinearMap.one_apply]
      | insert i t hi ih=>
        rw [noncommProd_congr (image_insert ..) (fun _ _=>rfl)]; simp only [noncommProd_insert_of_notMem _ i _ _ hi,noncommProd_insert_of_notMem _ _ _ _ (show d i ∉ Finset.image d t by simp [hi]),ContinuousLinearMap.mul_apply,hv.axle]; rw [ih]
    exact H _ _ _
include hp in
lemma bornE (T:Finset (Fj D E J))(d : Equiv.Perm D):r.passL (made P t U T) = made P t V (T.image (sail d e j)):=by
  unfold Cove.made; rw [map_mul,(parts_map ..).2.1,(parts_map ..).2.2]; -- motive
  refine congr_arg₂ (·*·) ?_ ?_ <;> rw [map_prod]
  · rw [prod_image e.injective.injOn]; apply prod_congr rfl; intro i _; rw [map_sub,map_one, map_exp r.passL r.phare,cutRead hp]
  rw [prod_image j.injective.injOn]; exact prod_congr rfl fun i _=>hp.voyage _
include hp hv
lemma iris (T:Finset (Fj D E J)): q.passL (Cove.dye O P t T U)= Cove.dye O P t (T.image (sail d e j)) V:=by
  apply Subtype.ext; change q.φ (light _ (Cove.dye ..))=light _ (Cove.dye ..); rw [dipping,dipping,hv.ships,seal_ax hv T e j,hv.rents]
  have he: r.φ (light _ (made P t U T))=light _ (made P t V (T.image (sail d e j))) := congr_arg Subtype.val (bornE hp T d)
  rw [he]
end YM.QCD.Sway
