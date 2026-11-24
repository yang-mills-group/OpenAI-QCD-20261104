import YM.VMarker.Limbs
import YM.MassiveQCD.Plate.Coupons
/-! # Applying an actual extra marked soft operation, and restoring unmarked Rail. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)
local notation "M"=> Ribbon.ample N I
variable (Y: Ruby.Hue c (ample N I) J)(F: Patron.Rail c (ample N I) U)
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "d!"=> withdraw N p θ
local notation "T!"=> Trail Y F t
namespace Card
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
local notation "Vt"=> (vacR R K).comp (withdraw N p θ)
open Relation
lemma raisedK (Y:Ruby.Hue c N J)(X: Patron.Rail c N U)(i:U): gemD Y X ({Sum.inl i}) :=by
    let p:= Stamp J U; let j:p:= Sum.inl i
    refine ⟨⟨?_,fun k hk=> (?_)⟩,⟨i,mem_toLeft.mpr (mem_singleton_self _)⟩,singleton_nonempty _,?_⟩
    · intro k hk m hm h; exact False.elim (h ((Sum.inl.inj (mem_singleton.mp (mem_toLeft.mp hk))).trans (Sum.inl.inj (mem_singleton.mp (mem_toLeft.mp hm))).symm))
    · exact False.elim (Sum.inr_ne_inl (mem_singleton.mp (mem_toRight.mp hk)))
    simp only [mem_singleton]; rintro _ rfl _ rfl; exact ReflTransGen.refl
noncomputable def floorK (Y:Ruby.Hue c N J)(X:Patron.Rail c N U):U ↪ Plot Y X:=⟨fun i=> ⟨{.inl i},raisedK N Y X i⟩,fun i j h=> Sum.inl.inj (Finset.singleton_injective (Subtype.ext_iff.mp h))⟩
local notation "θᵃ"=> floorK _ Y F
lemma stance (Y:Ruby.Hue c N J)(X:Patron.Rail c N U)(z:Plot Y X)(h:∀ j:J, Sum.inr j ∉ z.val) : z∈ Set.range (floorK N Y X) :=by
    obtain ⟨j,hj⟩:= z.property.2.1
    let v:=z.val; let X':=footD Y X
    have hf(i k:U ⊕ J)(hp:Ac.bonds X' v i k):i=k:=by
       obtain ⟨hi,hk,hv⟩:=hp; rcases i with i|i; swap; · exact (h i hi).elim
       rcases k with k|k; swap; · exact (h k hk).elim
       exact congr_arg Sum.inl (by_contra fun h=> z.property.1.1 _ (mem_toLeft.mpr hi) _ (mem_toLeft.mpr hk) h (Or.inr hv)) -- Lean Add syntax. i=j inferred?
    refine ⟨j,Subtype.ext ?_⟩; change {Sum.inl j}=v; ext i; rw [mem_singleton]; constructor; · rintro rfl; exact mem_toLeft.mp hj
    intro hi; have h:= Ac.swaps _ (z.property.2.2.2 _ (mem_toLeft.mp hj) _ hi)
    -- chain endpoints both specific; generalize
    have hx(i k:U⊕J)(h:Ac.chain X' v i k):i=k:=by induction h with| refl=>rfl| tail _ h ih=> exact ih.trans (hf _ _ h)
    exact hx _ _ h
lemma bowerScope (i:U) : scopeK Y F (θᵃ i).val= (F.addr i).place:=by change ({_}:Finset _).biUnion _=_; rw [singleton_biUnion]; rfl
lemma bowerBadge (i:U) : badgeK F (θᵃ i).val=(F.addr i).inv:=by
    change (toLeft ({.inl i}:Finset (Stamp J U))).biUnion _ = _ -- syntax
    rw [show toLeft ({.inl i}:Finset (Stamp J U))={i} from (by ext; simp),singleton_biUnion]; rfl
lemma bowerHat (i:U) : (Trail Y F t).addr (θᵃ i)= F.addr i :=by
    let h:= bowerScope N Y F i; let g:= bowerBadge N Y F i
    have ht (a b:Hat c)(h:a.place=b.place)(hg:a.inv=b.inv):a=b:=by cases a; cases b; subst_vars; rfl
    exact ht _ _ (bowerScope N Y F i) (bowerBadge N Y F i)
variable (ht : F.Reg t)(hc : ∀ i V,vacR (Spine I) (Keys c N) (withdraw N p θ (Y.mean i V))=0)
include ht
lemma scope_pays (i:U)(V:Grid c): (T!).warp (θᵃ i) V= F.warp i V:=by
    change payer Y F t V (θᵃ i).val=_; unfold payer; rw [bowerScope,bowerBadge]; split
    · change ∏ j∈({.inl i}:Finset (Stamp J U)),Ruby.flower Y F V j= _ -- notation `_` binder unused
      rw [prod_singleton]; rfl
    next h=> exact (by_contra fun he=>h (ht.buys i V he) : F.warp i V = 0).symm -- expects goal F.warp ≠ 0
omit ht
include hc
lemma vacant (V:Grid c)(i:Plot Y F)(h:i ∉ Set.range θᵃ): (faultK N p θ (Trail Y F t)).warp i V=0:=by
   obtain ⟨j,hj⟩:∃ j:J,Sum.inr j ∈ i.val:= not_forall_not.mp fun hf=> h (stance _ Y F _ hf)
   change (Vt) (payer Y F t V i.val)=0; unfold payer; split
   · rw [map_prod]; apply prod_eq_zero hj; change (Vt) (NormedSpace.exp (Y.mean j V)-1)=0; rw [map_sub,map_exp Vt (Vt).toLinearMap.toContinuousLinearMap.continuous,show Vt (Y.mean j V)=0 from hc j V,map_one,NormedSpace.exp_zero,sub_self]
   exact map_zero _
include ht
lemma receipt (X: Patron.Rail c N E)(he:Correspond (faultK N p θ F) X)(h: ∀ V,Summable fun i=> ‖(Trail Y F t).warp i V‖) : Correspond (faultK N p θ (T!)) X:=by
    refine ⟨fun V=> Film.payable (Vt).toLinearMap.toContinuousLinearMap (h V),he.coins,fun H V=> Eq.trans ?_ (he.governs H V)⟩
    unfold coin; -- undo!
    change coin (Trail Y F t).addr (fun i=> Vt ((T!).warp i V)) H=coin F.addr (fun i=> Vt (F.warp i V)) H
    rw [fingerprint,fingerprint]; let f(i:Plot Y F):= if (Trail Y F t).addr i=H then Vt ((T!).warp i V) else 0
    have hf: Function.support f ⊆ Set.range θᵃ:= fun i h=> by
           by_contra he; change f _≠0 at h; unfold f at h; split at h; exact h (vacant N p θ Y F hc V i he); exact h rfl
    exact ((θᵃ).injective.tsum_eq hf).symm.trans (tsum_congr (fun i=>show f (θᵃ i)=_ from by unfold f; rw [bowerHat,scope_pays N Y F ht]))
omit hc ht
variable (hTip:Wage.Tip N p q F O θ v w) (hWax: Wax Y O.threshold O.B a A θ) (he : ∀ i,shadeG (Y.mean i))(hM: ∀ i V,Well N p θ q (Y.mean i V))
include hTip hWax he hM
lemma tipped (h:StackK O.B w t₁ v t₂ a A)(hf:0<θ): Wage.Tip N p q (Trail Y F O.threshold) O θ t₂ t₁:=by
    refine ⟨⟨plant _ _ hWax.burns hTip.tilt.uses,fun i=> limbsColor M hTip.tilt.pigment he O.threshold i,h c M J U Y F O.threshold θ hWax.expense hTip.tilt.sold⟩,fun i V=>?_⟩
    change Well _ _ _ _ (payer ..); unfold payer; split; swap; · exact Well.zeroV
    apply Well.product; intro k hk; rcases k with k|k; · exact hTip.fits k V
    unfold Ruby.flower sparkY; simp only [Sum.elim_inr]; rw [sub_eq_add_neg]; exact Well.plus hf ((hM k _).flash) (Well.minus hf Well.oneV)
variable (X:Patron.Rail c N E)(T:StackK O.B w t₁ v t₂ a A)
include T
lemma contract (hp:∀ i V,vacR (Spine I) (Keys c N) (withdraw N p θ (Y.mean i V))=0) (hv:1≤ θ)(hz:1 ≤ w)(hQ:1 ≤ t₁)(hZ:0 ≤ t₂) (hs:Correspond (faultK N p θ F) X) : Correspond (faultK N p θ (Trail Y F O.threshold)) X :=by
    have h:= tipped N p q θ Y F hTip hWax he hM T (zero_lt_one.trans_le hv); exact receipt N p θ Y F hTip.tilt.uses hp X hs fun V=> prints _ V h.tilt.uses h.tilt.sold hQ hZ hv
omit he hM T
lemma extraDuty (hv:1≤θ)(hZ:1 ≤ w)(hV:0 ≤ v)(ha:0≤a) (U:Grid c) : heartK (Trail Y F O.threshold) O.threshold U=heartK F O.threshold U * NormedSpace.exp (swarm Y U):= by obtain ⟨he,hX⟩:= hWax.heated hv ha U; exact (plenary Y F U (profits F U hv hZ hTip.tilt.sold hV _) hWax.burns he hX).tsum_eq
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.receipt
