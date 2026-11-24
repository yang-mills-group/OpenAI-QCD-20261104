import YM.Rill.Pane
/-! Authentic torus support in strict positive-time caps using whole-field prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry
variable {n:Side}(h:Even n.val)(a:Axis)
lemma summedF {I:Type*}(x:I→ Insertion n 6)(S:Finset I)(v:Set (Site n))(hx:∀ i∈ S,Fence v (x i)): Fence v (⇑(∑ i∈S,x i)):=by
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact (show Fence v (0:Stud n 6) from (by have h:=(Fence.one (A:=v) (F:=6)|>.mass (0:ℂ)); rw [zero_smul] at h; exact h))
    | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (hx i (Finset.mem_insert_self ..)).add (ih (fun t ht=> hx t (Finset.mem_insert_of_mem ht)))
lemma shelter {T:Tiling n}{R: Regulator n 6}{p:T.Cell}{x:Insertion n 6}{z:ℝ}(h:Gold R T p x z): Fence (T.chamber p) x:=by obtain ⟨k,f,hx,hf,h⟩:=h; rw [← hx]; exact summedF f _ _ fun i _=> (hf i).1
variable {C:Sequence}{P:Calibration C} (G:∀ d,Cottage P d) {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S)
set_option quotPrecheck false
local notation "S"=> C.S
local notation "r" i:arg=> C.S.side (C.R i) (C.N i)
include hp
lemma distanceP : Tendsto (fun i=> (C.S.spacing (C.N i))*((r i).val:ℝ)) atTop atTop:=by
     have h:= tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp hp.infinite; refine h.congr (fun i=>?_); unfold Scheme.side Scheme.spacing; rw [PNat.mul_coe,Nat.cast_mul, mul_left_comm, inv_mul_cancel₀ (show (↑((C.S.ratio (C.N i)).val):ℝ) ≠ 0 by positivity),mul_one]; rfl
variable {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {f:ℕ→ Cover}{x:E4}
local notation "w" i:arg=> digit (C.S.spacing (C.N i))
local notation "pH" i:arg=> panH (evenW C.S (C.R i) (hp.even i) (C.N i)) a
omit hp
private lemma panels {x:Cover}{σ:ℝ}(hx:0<σ) (J:ℕ) {u:Site n}(he:separation u (wrap n x) ≤ J)(L:ℝ)(hL:digit σ x a ≤ L)(hX:σ*(J:ℕ) ≤ digit σ x a)(hY:(L+ σ*(J:ℕ))*2 < σ*(n.val:ℝ)): u∈ (panH h a).sector:=by
      let A:= lift (u-wrap n x); have hu:wrap n (x+A)= u:= (by unfold A; rw[map_add,wrap_lift,add_sub_cancel]); have hv:(A a).natAbs ≤ J:= (component_le ..).trans he
      let z:= panH h a; let B:=x a+A a; have hz : 0 ≤ B∧ B< (z.half.val:ℤ):=by
          have he:= z.even; change σ*↑(x a) ≤ L at hL; change σ * ↑J ≤ σ * ↑(x a) at hX; have h0:J ≤ x a:=by exact_mod_cast le_of_mul_le_mul_left hX hx
          constructor; · unfold B; omega
          have hh : (A a:ℝ) ≤ ↑J:= by exact_mod_cast (show A a ≤ (J:ℤ) by omega)
          have hf : (n.val:ℝ)= 2*(z.half.val:ℝ):=by exact_mod_cast he
          have hg: σ*(↑(x a)+↑(A a)) < σ*(z.half.val:ℝ):= by rw[hf] at hY; nlinarith [mul_le_mul_of_nonneg_left hh hx.le]
          exact_mod_cast lt_of_mul_lt_mul_left hg hx.le
      have hr: z.distance u=B.toNat:=by
          have hnat: B.toNat < n.val:=by rw [z.even]; omega
          have hh:B= ↑B.toNat:=(Int.toNat_of_nonneg hz.1).symm
          unfold Cells.Cut.distance; change ZMod.val (u a-0)=_; rw[sub_zero,←hu]; change ZMod.val ((B:ℤ):Per n)=_; nth_rw 1 [hh]; push_cast; exact ZMod.val_natCast_of_lt hnat
      change z.distance u< z.half.val; rw[hr]; omega
include hp hφ
private lemma horizon (hx:Tendsto (fun i=>digit (C.S.spacing (C.N (φ i))) (f i)) atTop (𝓝 x))(hk:0<x a)(j:ℕ)(hS:C.S.spacing j≤x a/2):∀ᶠ i in atTop,∀ u:Site (r (φ i)),separation u (wrap _ (f i))≤ ratioTo C.S (C.N (φ i)) j→u∈ (pH (φ i)).sector:=by
    let L:=x a+1; let v:= C.S.spacing j
    have ht:= ((show Continuous fun y:E4=> y a from by fun_prop).tendsto _).comp hx; filter_upwards [((distanceP hp).comp hφ).eventually_gt_atTop ((L+v)*2),((hp.uv.tendsto_atTop).comp hφ).eventually_ge_atTop j, ht.eventually_le_const (show x a<L from lt_add_one _),ht.eventually_const_le (half_lt_self hk)] with i hi hk hh hv u hu
    exact panels _ _ (space0 _ _) _ hu L hh (by rw [footprint C.S j (C.N (φ i)) hk]; exact hS.trans hv) (by rw [footprint C.S j (C.N (φ i)) hk]; exact hi)
include G hr
open Choir Choir.Strip Choir.Petals
lemma esteemed (p: Petal P)(g:Averaging)(ht: Atlas C P φ p)(hh:0<p.x a):∀ᶠ i in atTop,Fence (pH (φ i)).sector ⇑(signalW g p φ i):=by
     let d:=p.fieldT.1; let V(i):= stemV P d i g p.fieldT.2; obtain ⟨N,hN⟩:=eventually_atTop.mp ((((G d).pointsP hp hr g (fun _=>p.fieldT.2) ⟨_,norm_nonneg _,Eventually.of_forall fun _=> le_rfl⟩).1).and (hr.high.eventually_gt_atTop (6*1)))
     obtain ⟨j,hj,h⟩:= shyness hp _ (half_pos hh) N; obtain ⟨⟨Q,hv,H⟩,hJ⟩:=hN j hj
     filter_upwards [hφ.eventually H,horizon a hp hφ ht hh j h.le, (hp.uv.tendsto_atTop.comp hφ).eventually_ge_atTop (j+1)] with i hi hv hm; let k:=φ i; let K:= r k
     let T:=mural (viewW C.S (C.R k) (show j ≤ C.N k from Nat.le_of_lt hm)) (evenW _ _ (hp.even k) _) (0:Site K); let B:=wrap K (p.r i)
     let U:Fin 1→ Site K:=fun _=> B; let V':= viewW C.S (C.R k) (show j+1 ≤ C.N k from hm); let L:= 3*V'.count.val; have hpL: 1*(2*L) < T.side.val:=by
          have hh: T.side.val= (C.S.step j).L.val* V'.count.val:=step_factor hm; rw [hh]; apply lt_of_eq_of_lt _ (Nat.mul_lt_mul_of_pos_right hJ V'.count.property); change (1:ℕ) * (2*(3*V'.count.val))=(6*1)*V'.count.val; ring
     obtain ⟨x,hx⟩:= T.fits_together U L (by unfold L; positivity) hpL
     let Y:=T.newly x; let A:=Y.which B; exact Fence.high (shelter (hi hm Y rfl rfl A (p.r i) (hx 0))) fun p' hp=> hv _ (Y.extent hp (show B∈ Y.chamber A from (hx 0).1))
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.esteemed
