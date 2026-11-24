import YM.Intag.Vane
import YM.Pods.Typing
import YM.Work.E08
import YM.Lyre.Range
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Set Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical
namespace Column
variable (S:Scheme)(R:Side){i j k p N F:ℕ}
local notation "f"=> S.side R
local notation "V" => viewW S R
lemma chip (h:i≤k) : ratioTo S (k+1) i=(S.step k).L.val*ratioTo S k i:=size_comp (viewW S 1 h) (Flume.sliceL (S.step k) (S.sides_next 1 k)) (viewW S 1 (Nat.le_step h))
-- sets for funding through.Engine of costs tK. Flares offset M.Info.
noncomputable def pillar (x:Site (S.side R i)) (k:ℕ) : Site (S.side R k) := if h:i ≤ k then (V h).embed x else 0
variable (x y:Site (S.side R i))(M:ℕ)
lemma home_c (m:ℕ): ratioTo S m m=1:= centreN -- check
lemma homes : pillar S R x i=x:=by unfold pillar; rw [dif_pos le_rfl]; unfold Ratio.embed; change wrap _ (ratioTo S i i • _)=_; rw [home_c]; simp
local notation "l" k:arg=> 50*(S.J k+10)
-- residual lease grows as material.Link factor 3+. subtract linear allowance to ensure enough for Tide.
noncomputable def allowance (M i k:ℕ): ℕ := ratioTo S k i * M - l k
lemma bears (k:ℕ): l (k+1) + fuel (S.step k).patch ≤ (S.step k).L.val * l k:=by
    unfold fuel Patch.radius; let v:=(S.step k).L.val; let z:= S.J k; let u:= S.J (k+1); have he:u ≤ z+1:= (S.step k).narrow
    have hh : 3 ≤ v := (S.step k).coarse
    change 50*(u+10)+20*((u+3)*v) ≤ _; nlinarith only [he,hh,Nat.mul_le_mul_left v he,Nat.mul_le_mul_left (z+10) hh, Nat.zero_le z]
variable (hm:50*(S.J i+10) ≤ M)
local notation "Tk" k:arg=> allowance S M i k
include hm
lemma attests (h:i≤k): l k ≤ (ratioTo S k i) * M:=by
    induction h with
    | refl=> rw [home_c,one_mul]; exact hm
    | @step k hk ih=> have hh:= bears S k; rw [chip S hk,mul_assoc]; exact le_trans ((Nat.le_add_right _ _).trans hh) (Nat.mul_le_mul_left _ ih)
lemma passt (h:i≤k): (S.step k).L.val * allowance S M i k + fuel (S.step k).patch ≤ allowance S M i (k+1):=by
    let v:=(S.step k).L.val; have hh : v*(Tk k + l k) = ratioTo S (k+1) i*M:=by rw [chip S h,mul_assoc,show Tk k + l k= ratioTo S k i*M from Nat.sub_add_cancel (attests _ M hm h)]
    rw [mul_add] at hh; change v*Tk k+_ ≤ ratioTo S (k+1) i*M - (l (k+1)); rw [← hh]; have hp:l (k+1)+fuel (S.step k).patch ≤ v*l k:= bears _ _; omega
omit hm in
lemma enlarg {n:Side}{P Q:ℕ}(hp:P ≤ Q){x:Site n}: window x P ⊆ window x Q := by
     rintro y ⟨z,hz,rfl⟩; exact ⟨z,box_larger hz hp,rfl⟩ -- maybe Max
noncomputable def dome (i:ℕ)(x:Site (S.side R i))(M:ℕ)(k:ℕ): Set (Site (S.side R k)):= window (pillar S R x k) (allowance S M i k)
lemma leaseX : Lease i N (dome S R i x M):=by
      let L:=dome S R i x M; intro k hk hj y hy t ht
      let u:=Flume.sliceL (S.step k) (S.sides_next R k); change _ ∈ window (pillar S R x k) (Tk k) at hy; change t ∈ window (pillar S R x (k+1)) (Tk (k+1)); have hh:pillar S R x (k+1)= u.embed (pillar S R x k):=by unfold pillar; rw [dif_pos (Nat.le_step hk),dif_pos hk]; exact embed_comp ..
      have hq:t ∈ window (u.embed (pillar S R x k)) (u.count.val* allowance S M i k + fuel (S.step k).patch):= window_add (window_embed u hy) ht
      have hp:u.count.val* allowance S M i k + fuel (S.step k).patch ≤ allowance S M i (k+1):= passt S M hm hk
      rw [hh]; exact enlarg hp hq
omit hm
lemma window_key {c:Side}(x y:Site c)(P:ℕ): x∈window y P ↔ separation y x ≤ P := by
      constructor; · rintro ⟨z,hz,rfl⟩; exact Work.E08.separation_box_add _ hz
      intro h; refine ⟨Lattice.lift (x-y), Work.E08.lift_mem_box h,?_⟩; dsimp only; rw [wrap_lift,sub_add_cancel]
lemma battered (hx:2*M < separation x y)(h:i≤k): Disjoint (dome S R i x M k) (dome S R i y M k):=by
      refine Set.disjoint_left.mpr ?_; intro z hz hr
      unfold dome pillar at hz hr; rw [dif_pos h] at hz hr
      let u:=viewW S R h; have ht:separation (u.embed x) (u.embed y) ≤ (Tk k)+(Tk k):=by
             apply (separation_triangle _ z _).trans; rw [separation_comm z (u.embed y)]; exact add_le_add ((window_key ..).mp hz) ((window_key ..).mp hr)
      have hl:Tk k ≤ (u.count.val*M):= Nat.sub_le _ _; have hv:=Nat.mul_lt_mul_of_pos_left hx u.count.property; rw [both] at ht; rw [two_mul,mul_add] at hv; exact (not_lt.mpr (ht.trans (add_le_add hl hl))) hv
-- placed chamber & submargins for any pitch. Any ascent.
variable (z:Site (S.side R i))(hr: Even (S.side R p).val) (P:Site (S.side R p))
noncomputable abbrev sky (p k:ℕ)(h:p≤k)(hr:Even (S.side R p).val) (z:Site (S.side R i)):= mural (viewW S R h) hr (pillar S R z k)
lemma sheaf (h:p ≤ i)(he:i ≤ k)(m:ℕ)(hy:x ∈ (mural (viewW S R h) hr z).margin P (M+m)): dome S R i x M k ⊆ (sky S R p k (h.trans he) hr z).margin P ((viewW S R he).count.val*m):=by
      intro t ht; let u:=viewW S R he; let v:= viewW S R (h.trans he)
      unfold dome pillar at ht; rw [dif_pos he] at ht
      have hz:u.embed x∈ (mural v hr (u.embed z)).margin P (u.count.val*(M+m)):= (stepSpan (V h) u v z x P hr (viewOdd ..) (viewOdd ..) (M+m)).1 hy -- `..` hope
      unfold sky pillar; rw [dif_pos he]; apply (key_margin v (u.embed z) t P hr (viewOdd ..) (u.count.val*m)).mpr
      let b:=u.embed z+v.embed P; have hc : separation t (u.embed x)≤ u.count.val*M:=by rw [separation_comm]; exact ((window_key ..).1 ht|>.trans (Nat.sub_le ..))
      have hh:separation (u.embed x) b+u.count.val*(M+m) ≤ v.count.val/2:= (key_margin v _ _ _ hr (viewOdd ..) _).mp hz; rw [mul_add] at hh; have hx:= separation_triangle t (u.embed x) b; change separation t b+_ ≤ _; omega
-- Tiling ancestry anchors; recursive.Norm cuts.G.Mapping at EVERY stage.Act.
lemma halos (h:p ≤ i)(hx:i≤ k)(a:Axis): (sky S R p (k+1) (h.trans (Nat.le_step hx)) hr z).bandCut P a= gateH ((sky S R p k (h.trans hx) hr z).bandCut P a) (Flume.sliceL (S.step k) (S.sides_next R k)) :=by
      let v:=Flume.sliceL (S.step k) (S.sides_next R k); unfold sky pillar; rw [dif_pos (Nat.le_step hx),dif_pos hx,show (viewW S R (Nat.le_step hx)).embed z=v.embed ((viewW S R hx).embed z) from embed_comp ..]; exact bankcut _ _ _ _ _ hr (viewOdd S R (h.trans hx)) (S.step k).odd _
end Column
end YM.Intag
#print axioms YM.Intag.Column.battered
#print axioms YM.Intag.Column.sheaf
#print axioms YM.Intag.Column.passt
#print axioms YM.Intag.Column.halos
#print axioms YM.Intag.Column.leaseX
