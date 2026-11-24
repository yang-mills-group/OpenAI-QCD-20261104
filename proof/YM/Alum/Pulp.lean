import YM.Alum.Sip
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV Quills.Eden
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
namespace Pulp
open Clover
variable (Q:I→Bool)(v:I→ℕ)(P: ∀ i:I, Arise.Bill.Cups (v i) (Q i))(p:I→ E4)
variable (i:Finset I)
local notation "R"=> Spine I
local notation "Kv" i:arg=> Quills.tour i
-- small rank spectral continuity. Unit obligations.Point circumference. Need only bounded but prove local continuous.Ss
variable (hp:Set.InjOn p (i:Set I))
include hp
lemma flour : ContinuousAt (fun p=> freeCost Q v P p i) p:=by
      unfold freeCost; let f(k:I→ E4):Points i.card:= points (k∘ tour i); have h : f p∈conf i.card:= fun j l e=>snug i (hp (i.equivFin.symm j).property (i.equivFin.symm l).property e)
      apply (UV.Free.Sip.smoothC h _ _).continuousAt.comp; -- argument `?m2`
      suffices hh:Continuous f from hh.continuousAt; unfold f; refine (PiLp.continuous_toLp 2 _).comp (?_) -- check simp
      exact continuous_pi fun i=>continuous_apply _
lemma off : ∀ᶠ x: (I→ E4) in 𝓝 p,Set.InjOn x (i:Set I):=by
     have h : ∀ᶠ x:(I→E4) in 𝓝 p,∀ u v:(↥i),u≠v→x u≠x v:=by
          refine eventually_all.mpr fun u=> eventually_all.mpr fun v=>?_ ; by_cases he:u=v; exact Eventually.of_forall fun y h=>False.elim (h he)
          have h:p u≠ p v:=fun h=> he (Subtype.ext (hp u.2 v.2 h)); have ht:ContinuousAt (fun x : I→ E4=>x u-x v) p :=(continuous_apply u.val).continuousAt.sub ((continuous_apply v.val).continuousAt); exact (ht.eventually_ne (sub_ne_zero.mpr h)).mono (fun i hi _=> sub_ne_zero.mp hi)
     exact h.mono fun f h=> fun x hx y hy he'=> by by_contra hP; exact h ⟨x,hx⟩ ⟨y,hy⟩ (fun h=>hP (congr_arg Subtype.val h)) he'
lemma transparent :ContinuousAt (fun p=> cupZ Q v P p i) p:=by
     let f(k:I→ E4):Alg (Spine I):= arms Q v P k i
     have ht:ContinuousAt f p:= (flour Q v P p i hp).smul continuousAt_const
     let H(k:I→ E4):Patio (Spine I):=cupZ Q v P k i; apply tendsto_subtype_rng.mpr; have h:Filter.EventuallyEq (𝓝 p) (fun j=> (H j).val) f :=(off p i hp).mono fun x hx=> (by change (cupZ Q v P x i).val = _; unfold cupZ; rw (transparency:=.default) [dif_pos hx]) -- type
     change Tendsto _ _ (𝓝 ((H p).val)); rw [show (H p).val=f p from h.eq_of_nhds]; exact ht.tendsto.congr' h.symm -- type subtype.
lemma smart (j:Finset I)(hj:j⊆i):ContinuousAt (fun p=>cetacea (cupZ Q v P p) j) p:=by
     suffices h:∀ n:ℕ,∀ j⊆ i, ContinuousAt (fun p=>sturdy (cupZ Q v P p) n j) p from h _ _ hj
     intro n; induction n with|zero=> exact fun _ _=> continuousAt_const | succ n ih=>
         intro j ht; unfold sturdy; split_ifs
         · exact (transparent Q v P p j (hp.mono ‹_›)).sub (tendsto_finsetSum _ (fun u h=> tendsto_finsetProd _ (fun k hk=> ih k ((member (mem_of_mem_erase h) hk).2.trans ‹_›)))) -- names
         exact continuousAt_const
lemma unmon : ContinuousAt (fun p=> fareZ Q v P p i) p :=by
    apply NormedSpace.exp_continuous.continuousAt.comp
    exact tendsto_finsetSum _ fun j hj=> (smart Q v P _ i hp _ (mem_powerset.mp (mem_of_mem_erase hj))).neg
omit hp
variable (l:List I)(hx:Set.InjOn p l.toFinset)(f:Fin n→I)
include hx
lemma continuity :ContinuousAt (fun p=> compZ Q v P p l i) p:=by
      apply continuousAt_const.mul; apply continuousAt_const.mul; apply (Grass.continuous_coef _).continuousAt.comp; exact continuous_subtype_val.continuousAt.comp (unmon Q v P p _ hx)
omit hx
lemma enhance (h:Set.InjOn p (crest f))(he:i⊆crest f):ContinuousAt (fun p=> saves Q v P p f i) p:=by
     apply ContinuousAt.mul _ continuousAt_const; apply continuousAt_const.mul; apply (Grass.continuous_coef _).continuousAt.comp; apply continuousAt_const.mul; exact continuous_subtype_val.continuousAt.comp (transparent Q v P p i (h.mono ‹_›)) -- Set Coe!
end Pulp
end YM.MassiveQCD.Sample.Quills
#print axioms YM.MassiveQCD.Sample.Quills.Pulp.continuity
#print axioms YM.MassiveQCD.Sample.Quills.Pulp.enhance
